/*!
Provides a parser for [POSIX's `TZ` environment variable][posix-env].

NOTE: Sadly, at time of writing, the actual parser is in `src/shared/posix.rs`.
This is so it can be shared (via simple code copying) with proc macros like
the one found in `jiff-tzdb-static`. The parser populates a "lowest common
denominator" data type. In normal use in Jiff, this type is converted into
the types defined below. This module still does provide the various time zone
operations. Only the parsing is written elsewhere.

The `TZ` environment variable is most commonly used to set a time zone. For
example, `TZ=America/New_York`. But it can also be used to tersely define DST
transitions. Moreover, the format is not just used as an environment variable,
but is also included at the end of TZif files (version 2 or greater). The IANA
Time Zone Database project also [documents the `TZ` variable][iana-env] with
a little more commentary.

Note that we (along with pretty much everyone else) don't strictly follow
POSIX here. Namely, `TZ=America/New_York` isn't a POSIX compatible usage,
and I believe it technically should be `TZ=:America/New_York`. Nevertheless,
apparently some group of people (IANA folks?) decided `TZ=America/New_York`
should be fine. From the [IANA `theory.html` documentation][iana-env]:

> It was recognized that allowing the TZ environment variable to take on values
> such as 'America/New_York' might cause "old" programs (that expect TZ to have
> a certain form) to operate incorrectly; consideration was given to using
> some other environment variable (for example, TIMEZONE) to hold the string
> used to generate the TZif file's name. In the end, however, it was decided
> to continue using TZ: it is widely used for time zone purposes; separately
> maintaining both TZ and TIMEZONE seemed a nuisance; and systems where "new"
> forms of TZ might cause problems can simply use legacy TZ values such as
> "EST5EDT" which can be used by "new" programs as well as by "old" programs
> that assume pre-POSIX TZ values.

Indeed, even [musl subscribes to this behavior][musl-env]. So that's what we do
here too.

Note that a POSIX time zone like `EST5` corresponds to the UTC offset `-05:00`,
and `GMT-4` corresponds to the UTC offset `+04:00`. Yes, it's backwards. How
fun.

# IANA v3+ Support

While this module and many of its types are directly associated with POSIX,
this module also plays a supporting role for `TZ` strings in the IANA TZif
binary format for versions 2 and greater. Specifically, for versions 3 and
greater, some minor extensions are supported here via `IanaTz::parse`. But
using `PosixTz::parse` is limited to parsing what is specified by POSIX.
Nevertheless, we generally use `IanaTz::parse` everywhere, even when parsing
the `TZ` environment variable. The reason for this is that it seems to be what
other programs do in practice (for example, GNU date).

# `no-std` and `no-alloc` support

A big part of this module works fine in core-only environments. But because
core-only environments provide means of indirection, and embedding a
`PosixTimeZone` into a `TimeZone` without indirection would use up a lot of
space (and thereby make `Zoned` quite chunky), we provide core-only support
principally through a proc macro. Namely, a `PosixTimeZone` can be parsed by
the proc macro and then turned into static data.

POSIX time zone support isn't explicitly provided directly as a public API
for core-only environments, but is implicitly supported via TZif. (Since TZif
data contains POSIX time zone strings.)

[posix-env]: https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap08.html#tag_08_03
[iana-env]: https://data.iana.org/time-zones/tzdb-2024a/theory.html#functions
[musl-env]: https://wiki.musl-libc.org/environment-variables
*/

use crate::{
    civil::{Date, DateTime, Time, Weekday},
    error::{err, Error, ErrorContext},
    shared,
    timestamp::Timestamp,
    tz::{
        timezone::TimeZoneAbbreviation, AmbiguousOffset, Dst, Offset,
        TimeZoneOffsetInfo, TimeZoneTransition,
    },
    util::{
        array_str::Abbreviation,
        escape::Bytes,
        parse,
        rangeint::{ri16, ri32, ri8, RInto},
        t::{self, Month, SpanZoneOffset, Year, C},
    },
    SignedDuration,
};

type PosixJulianDayNoLeap = ri16<1, 365>;
type PosixJulianDayWithLeap = ri16<0, 365>;
type PosixWeek = ri8<1, 5>;
type PosixTimeSeconds = ri32<{ -604799 }, 604799>;

/// The result of parsing the POSIX `TZ` environment variable.
///
/// A `TZ` variable can either be a time zone string with an optional DST
/// transition rule, or it can begin with a `:` followed by an arbitrary set of
/// bytes that is implementation defined.
///
/// In practice, the content following a `:` is treated as an IANA time zone
/// name. Moreover, even if the `TZ` string doesn't start with a `:` but
/// corresponds to a IANA time zone name, then it is interpreted as such.
/// (See the module docs.) However, this type only encapsulates the choices
/// strictly provided by POSIX: either a time zone string with an optional DST
/// transition rule, or an implementation defined string with a `:` prefix. If,
/// for example, `TZ="America/New_York"`, then that case isn't encapsulated by
/// this type. Callers needing that functionality will need to handle the error
/// returned by parsing this type and layer their own semantics on top.
#[cfg(feature = "tz-system")]
#[derive(Debug, Eq, PartialEq)]
pub(crate) enum PosixTzEnv {
    /// A valid POSIX time zone with an optional DST transition rule.
    Rule(PosixTimeZone),
    /// An implementation defined string. This occurs when the `TZ` value
    /// starts with a `:`. The string returned here does not include the `:`.
    Implementation(alloc::boxed::Box<str>),
}

#[cfg(feature = "tz-system")]
impl PosixTzEnv {
    /// Parse a POSIX `TZ` environment variable string from the given bytes.
    fn parse(bytes: impl AsRef<[u8]>) -> Result<PosixTzEnv, Error> {
        let bytes = bytes.as_ref();
        if bytes.get(0) == Some(&b':') {
            let Ok(string) = core::str::from_utf8(&bytes[1..]) else {
                return Err(err!(
                    "POSIX time zone string with a ':' prefix contains \
                     invalid UTF-8: {:?}",
                    Bytes(&bytes[1..]),
                ));
            };
            Ok(PosixTzEnv::Implementation(string.into()))
        } else {
            PosixTimeZone::parse(bytes).map(PosixTzEnv::Rule)
        }
    }

    /// Parse a POSIX `TZ` environment variable string from the given `OsStr`.
    pub(crate) fn parse_os_str(
        osstr: impl AsRef<std::ffi::OsStr>,
    ) -> Result<PosixTzEnv, Error> {
        PosixTzEnv::parse(parse::os_str_bytes(osstr.as_ref())?)
    }
}

#[cfg(feature = "tz-system")]
impl core::fmt::Display for PosixTzEnv {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match *self {
            PosixTzEnv::Rule(ref tz) => write!(f, "{tz}"),
            PosixTzEnv::Implementation(ref imp) => write!(f, ":{imp}"),
        }
    }
}

/// A POSIX time zone.
///
/// # On "reasonable" POSIX time zones
///
/// Jiff only supports "reasonable" POSIX time zones. A "reasonable" POSIX time
/// zone is a POSIX time zone that has a DST transition rule _when_ it has a
/// DST time zone abbreviation. Without the transition rule, it isn't possible
/// to know when DST starts and stops.
///
/// POSIX technically allows a DST time zone abbreviation *without* a
/// transition rule, but the behavior is literally unspecified. So Jiff just
/// rejects them.
///
/// Note that if you're confused as to why Jiff accepts `TZ=EST5EDT` (where
/// `EST5EDT` is an example of an _unreasonable_ POSIX time zone), that's
/// because Jiff rejects `EST5EDT` and instead attempts to use it as an IANA
/// time zone identifier. And indeed, the IANA Time Zone Database contains an
/// entry for `EST5EDT` (presumably for legacy reasons).
///
/// Also, we expect `TZ` strings parsed from IANA v2+ formatted `tzfile`s to
/// also be reasonable or parsing fails. This also seems to be consistent with
/// the [GNU C Library]'s treatment of the `TZ` variable: it only documents
/// support for reasonable POSIX time zone strings.
///
/// Note that a V2 `TZ` string is precisely identical to a POSIX `TZ`
/// environment variable string. A V3 `TZ` string however supports signed DST
/// transition times, and hours in the range `0..=167`. The V2 and V3 here
/// reference how `TZ` strings are defined in the TZif format specified by
/// [RFC 9636]. V2 is the original version of it straight from POSIX, where as
/// V3+ corresponds to an extension added to V3 (and newer versions) of the
/// TZif format. V3 is a superset of V2, so in practice, Jiff just permits
/// V3 everywhere.
///
/// [GNU C Library]: https://www.gnu.org/software/libc/manual/2.25/html_node/TZ-Variable.html
/// [RFC 9636]: https://datatracker.ietf.org/doc/rfc9636/
#[derive(Clone, Debug, Eq, PartialEq)]
// NOT part of Jiff's public API
#[doc(hidden)]
// This ensures the alignment of this type is always *at least* 8 bytes. This
// is required for the pointer tagging inside of `TimeZone` to be sound. At
// time of writing (2024-02-24), this explicit `repr` isn't required on 64-bit
// systems since the type definition is such that it will have an alignment of
// at least 8 bytes anyway. But this *is* required for 32-bit systems, where
// the type definition at present only has an alignment of 4 bytes.
#[repr(align(8))]
pub struct PosixTimeZone {
    std_abbrev: Abbreviation,
    std_offset: PosixOffset,
    dst: Option<PosixDst>,
}

impl PosixTimeZone {
    /// Parse a IANA tzfile v3+ `TZ` string from the given bytes.
    #[cfg(feature = "alloc")]
    pub(crate) fn parse(
        bytes: impl AsRef<[u8]>,
    ) -> Result<PosixTimeZone, Error> {
        let bytes = bytes.as_ref();
        let shared_tz = shared::PosixTimeZone::parse(bytes.as_ref())
            .map_err(Error::adhoc)
            .map_err(|e| {
                e.context(err!("invalid POSIX TZ string {:?}", Bytes(bytes)))
            })?;
        let posix_tz = PosixTimeZone::from_shared_owned(&shared_tz);
        Ok(posix_tz)
    }

    /// Like `parse`, but parses a POSIX TZ string from a prefix of the
    /// given input. And remaining input is returned.
    #[cfg(feature = "alloc")]
    pub(crate) fn parse_prefix<'b, B: AsRef<[u8]> + ?Sized + 'b>(
        bytes: &'b B,
    ) -> Result<(PosixTimeZone, &'b [u8]), Error> {
        let bytes = bytes.as_ref();
        let (shared_tz, remaining) =
            shared::PosixTimeZone::parse_prefix(bytes.as_ref())
                .map_err(Error::adhoc)
                .map_err(|e| {
                    e.context(err!(
                        "invalid POSIX TZ string {:?}",
                        Bytes(bytes)
                    ))
                })?;
        let posix_tz = PosixTimeZone::from_shared_owned(&shared_tz);
        Ok((posix_tz, remaining))
    }

    /// Converts from the shared-but-internal API for use in proc macros.
    #[cfg(feature = "alloc")]
    pub(crate) fn from_shared_owned(
        sh: &shared::PosixTimeZone<Abbreviation>,
    ) -> PosixTimeZone {
        let std_abbrev = sh.std_abbrev;
        let std_offset = PosixOffset {
            offset: SpanZoneOffset::new(sh.std_offset)
                .expect("expected std offset in range"),
        };
        let dst = sh.dst.as_ref().map(PosixDst::from_shared_owned);
        PosixTimeZone { std_abbrev, std_offset, dst }
    }

    /// Converts from the shared-but-internal API for use in proc macros.
    ///
    /// This works in a `const` context by requiring that the time zone
    /// abbreviations are `static` strings. This is used when converting
    /// code generated by a proc macro to this Jiff internal type.
    pub(crate) const fn from_shared_const(
        sh: &shared::PosixTimeZone<&'static str>,
    ) -> PosixTimeZone {
        use crate::util::constant::unwrap;

        let std_abbrev = unwrap!(
            Abbreviation::new(sh.std_abbrev),
            "expected short enough std tz abbreviation"
        );
        let std_offset = PosixOffset {
            offset: unwrap!(
                SpanZoneOffset::new_const(sh.std_offset),
                "expected std offset in range",
            ),
        };
        let dst = match sh.dst {
            None => None,
            Some(ref dst) => Some(PosixDst::from_shared_const(dst)),
        };
        PosixTimeZone { std_abbrev, std_offset, dst }
    }

    /// Returns the appropriate time zone offset to use for the given
    /// timestamp.
    ///
    /// If you need information like whether the offset is in DST or not, or
    /// the time zone abbreviation, then use `PosixTimeZone::to_offset_info`.
    /// But that API may be more expensive to use, so only use it if you need
    /// the additional data.
    pub(crate) fn to_offset(&self, timestamp: Timestamp) -> Offset {
        if self.dst.is_none() {
            return self.std_offset();
        }

        let dt = Offset::UTC.to_datetime(timestamp);
        self.dst_info_utc(dt.date().year_ranged())
            .filter(|dst_info| dst_info.in_dst(dt))
            .map(|dst_info| dst_info.offset())
            .unwrap_or_else(|| self.std_offset())
    }

    /// Returns the appropriate time zone offset to use for the given
    /// timestamp.
    ///
    /// This also includes whether the offset returned should be considered
    /// to be "DST" or not, along with the time zone abbreviation (e.g., EST
    /// for standard time in New York, and EDT for DST in New York).
    pub(crate) fn to_offset_info(
        &self,
        timestamp: Timestamp,
    ) -> TimeZoneOffsetInfo<'_> {
        if self.dst.is_none() {
            let abbreviation =
                TimeZoneAbbreviation::Borrowed(self.std_abbrev.as_str());
            return TimeZoneOffsetInfo {
                offset: self.std_offset(),
                dst: Dst::No,
                abbreviation,
            };
        }

        let dt = Offset::UTC.to_datetime(timestamp);
        self.dst_info_utc(dt.date().year_ranged())
            .filter(|dst_info| dst_info.in_dst(dt))
            .map(|dst_info| {
                let abbreviation = TimeZoneAbbreviation::Borrowed(
                    dst_info.dst.abbrev.as_str(),
                );
                TimeZoneOffsetInfo {
                    offset: dst_info.offset(),
                    dst: Dst::Yes,
                    abbreviation,
                }
            })
            .unwrap_or_else(|| {
                let abbreviation =
                    TimeZoneAbbreviation::Borrowed(self.std_abbrev.as_str());
                TimeZoneOffsetInfo {
                    offset: self.std_offset(),
                    dst: Dst::No,
                    abbreviation,
                }
            })
    }

    /// Returns a possibly ambiguous timestamp for the given civil datetime.
    ///
    /// The given datetime should correspond to the "wall" clock time of what
    /// humans use to tell time for this time zone.
    ///
    /// Note that "ambiguous timestamp" is represented by the possible
    /// selection of offsets that could be applied to the given datetime. In
    /// general, it is only ambiguous around transitions to-and-from DST. The
    /// ambiguity can arise as a "fold" (when a particular wall clock time is
    /// repeated) or as a "gap" (when a particular wall clock time is skipped
    /// entirely).
    pub(crate) fn to_ambiguous_kind(&self, dt: DateTime) -> AmbiguousOffset {
        let year = dt.date().year_ranged();
        let std_offset = self.std_offset();
        let Some(dst_info) = self.dst_info_wall(year) else {
            return AmbiguousOffset::Unambiguous { offset: std_offset };
        };
        let diff = dst_info.offset().duration_since(std_offset);
        // When the difference between DST and standard is positive, that means
        // STD->DST results in a gap while DST->STD results in a fold. However,
        // when the difference is negative, that means STD->DST results in a
        // fold while DST->STD results in a gap. The former is by far the most
        // common. The latter is a bit weird, but real cases do exist. For
        // example, Dublin has DST in winter (UTC+01) and STD in the summer
        // (UTC+00).
        //
        // When the difference is zero, then we have a weird POSIX time zone
        // where a DST transition rule was specified, but was set to explicitly
        // be the same as STD. In this case, there can be no ambiguity. (The
        // zero case is strictly redundant. Both the diff < 0 and diff > 0
        // cases handle the zero case correctly. But we write it out for
        // clarity.)
        if diff.as_secs() == 0 {
            debug_assert_eq!(std_offset, dst_info.offset());
            AmbiguousOffset::Unambiguous { offset: std_offset }
        } else if diff.is_negative() {
            // For DST transitions that always move behind one hour, ambiguous
            // timestamps only occur when the given civil datetime falls in the
            // standard time range.
            if dst_info.in_dst(dt) {
                AmbiguousOffset::Unambiguous { offset: dst_info.offset() }
            } else {
                let fold_start = dst_info.start.saturating_add(diff);
                let gap_end = dst_info.end.saturating_sub(diff);
                if fold_start <= dt && dt < dst_info.start {
                    AmbiguousOffset::Fold {
                        before: std_offset,
                        after: dst_info.offset(),
                    }
                } else if dst_info.end <= dt && dt < gap_end {
                    AmbiguousOffset::Gap {
                        before: dst_info.offset(),
                        after: std_offset,
                    }
                } else {
                    AmbiguousOffset::Unambiguous { offset: std_offset }
                }
            }
        } else {
            // For DST transitions that always move ahead one hour, ambiguous
            // timestamps only occur when the given civil datetime falls in the
            // DST range.
            if !dst_info.in_dst(dt) {
                AmbiguousOffset::Unambiguous { offset: std_offset }
            } else {
                // PERF: I wonder if it makes sense to pre-compute these?
                // Probably not, because we have to do it based on year of
                // datetime given. But if we ever add a "caching" layer for
                // POSIX time zones, then it might be worth adding these to it.
                let gap_end = dst_info.start.saturating_add(diff);
                let fold_start = dst_info.end.saturating_sub(diff);
                if dst_info.start <= dt && dt < gap_end {
                    AmbiguousOffset::Gap {
                        before: std_offset,
                        after: dst_info.offset(),
                    }
                } else if fold_start <= dt && dt < dst_info.end {
                    AmbiguousOffset::Fold {
                        before: dst_info.offset(),
                        after: std_offset,
                    }
                } else {
                    AmbiguousOffset::Unambiguous { offset: dst_info.offset() }
                }
            }
        }
    }

    /// Returns the timestamp of the most recent time zone transition prior
    /// to the timestamp given. If one doesn't exist, `None` is returned.
    pub(crate) fn previous_transition(
        &self,
        timestamp: Timestamp,
    ) -> Option<TimeZoneTransition> {
        let dt = Offset::UTC.to_datetime(timestamp);
        let dst_info = self.dst_info_utc(dt.date().year_ranged())?;
        let (earlier, later) = dst_info.ordered();
        let (prev, dst_info) = if dt > later {
            (later, dst_info)
        } else if dt > earlier {
            (earlier, dst_info)
        } else {
            let prev_year = dt.date().year_ranged().checked_sub(C(1))?;
            let dst_info = self.dst_info_utc(prev_year)?;
            let (_, later) = dst_info.ordered();
            (later, dst_info)
        };

        let timestamp = Offset::UTC.to_timestamp(prev).ok()?;
        let dt = Offset::UTC.to_datetime(timestamp);
        let (offset, abbrev, dst) = if dst_info.in_dst(dt) {
            (dst_info.offset(), dst_info.dst.abbrev.as_str(), Dst::Yes)
        } else {
            (self.std_offset(), self.std_abbrev.as_str(), Dst::No)
        };
        Some(TimeZoneTransition { timestamp, offset, abbrev, dst })
    }

    /// Returns the timestamp of the soonest time zone transition after the
    /// timestamp given. If one doesn't exist, `None` is returned.
    pub(crate) fn next_transition(
        &self,
        timestamp: Timestamp,
    ) -> Option<TimeZoneTransition> {
        let dt = Offset::UTC.to_datetime(timestamp);
        let dst_info = self.dst_info_utc(dt.date().year_ranged())?;
        let (earlier, later) = dst_info.ordered();
        let (next, dst_info) = if dt < earlier {
            (earlier, dst_info)
        } else if dt < later {
            (later, dst_info)
        } else {
            let next_year = dt.date().year_ranged().checked_add(C(1))?;
            let dst_info = self.dst_info_utc(next_year)?;
            let (earlier, _) = dst_info.ordered();
            (earlier, dst_info)
        };

        let timestamp = Offset::UTC.to_timestamp(next).ok()?;
        let dt = Offset::UTC.to_datetime(timestamp);
        let (offset, abbrev, dst) = if dst_info.in_dst(dt) {
            (dst_info.offset(), dst_info.dst.abbrev.as_str(), Dst::Yes)
        } else {
            (self.std_offset(), self.std_abbrev.as_str(), Dst::No)
        };
        Some(TimeZoneTransition { timestamp, offset, abbrev, dst })
    }

    /// Returns the offset for standard time in this POSIX time zone.
    fn std_offset(&self) -> Offset {
        self.std_offset.offset()
    }

    /// Returns the range in which DST occurs.
    ///
    /// The civil datetimes returned are in UTC. This is useful for determining
    /// whether a timestamp is in DST or not.
    fn dst_info_utc(&self, year: impl RInto<Year>) -> Option<DstInfo<'_>> {
        let year = year.rinto();
        let dst = self.dst.as_ref()?;
        let std_offset = self.std_offset.offset();
        let dst_offset = dst.offset.offset();
        // DST time starts with respect to standard time, so offset it by the
        // standard offset.
        let start = dst.rule.start.to_datetime(year, std_offset);
        // DST time ends with respect to DST time, so offset it by the DST
        // offset.
        let end = dst.rule.end.to_datetime(year, dst_offset);
        Some(DstInfo { dst, start, end })
    }

    /// Returns the range in which DST occurs.
    ///
    /// The civil datetimes returned are in "wall clock time." That is, they
    /// represent the transitions as they are seen from humans reading a clock
    /// within the geographic location of that time zone.
    fn dst_info_wall(&self, year: impl RInto<Year>) -> Option<DstInfo<'_>> {
        let year = year.rinto();
        let dst = self.dst.as_ref()?;
        // POSIX time zones express their DST transitions in terms of wall
        // clock time. Since this method specifically is returning wall
        // clock times, we don't want to offset our datetimes at all.
        let start = dst.rule.start.to_datetime(year, Offset::ZERO);
        let end = dst.rule.end.to_datetime(year, Offset::ZERO);
        Some(DstInfo { dst, start, end })
    }

    /// Returns the DST transition rule. This panics if this time zone doesn't
    /// have DST.
    #[cfg(test)]
    fn rule(&self) -> Rule {
        self.dst.as_ref().unwrap().rule
    }
}

impl core::fmt::Display for PosixTimeZone {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(
            f,
            "{}{}",
            AbbreviationDisplay(self.std_abbrev),
            self.std_offset
        )?;
        if let Some(ref dst) = self.dst {
            dst.display(self.std_offset, f)?;
        }
        Ok(())
    }
}

/// The daylight saving time (DST) info for a POSIX time zone in a particular
/// year.
#[derive(Debug, Eq, PartialEq)]
struct DstInfo<'a> {
    /// The DST transition rule that generated this info.
    dst: &'a PosixDst,
    /// The start time (inclusive) that DST begins.
    ///
    /// Note that this may be greater than `end`. This tends to happen in the
    /// southern hemisphere.
    ///
    /// Note also that this may be in UTC or in wall clock civil
    /// time. It depends on whether `PosixTimeZone::dst_info_utc` or
    /// `PosixTimeZone::dst_info_wall` was used.
    start: DateTime,
    /// The end time (exclusive) that DST ends.
    ///
    /// Note that this may be less than `start`. This tends to happen in the
    /// southern hemisphere.
    ///
    /// Note also that this may be in UTC or in wall clock civil
    /// time. It depends on whether `PosixTimeZone::dst_info_utc` or
    /// `PosixTimeZone::dst_info_wall` was used.
    end: DateTime,
}

impl<'a> DstInfo<'a> {
    /// Returns true if and only if the given civil datetime ought to be
    /// considered in DST.
    fn in_dst(&self, utc_dt: DateTime) -> bool {
        if self.start <= self.end {
            self.start <= utc_dt && utc_dt < self.end
        } else {
            !(self.end <= utc_dt && utc_dt < self.start)
        }
    }

    /// Returns the earlier and later times for this DST info.
    fn ordered(&self) -> (DateTime, DateTime) {
        if self.start <= self.end {
            (self.start, self.end)
        } else {
            (self.end, self.start)
        }
    }

    /// Returns the DST offset.
    fn offset(&self) -> Offset {
        self.dst.offset.offset()
    }
}

/// The daylight-saving-time abbreviation, offset and rule for this time zone.
///
/// Unlike what POSIX specifies, this requires a rule.
#[derive(Clone, Debug, Eq, PartialEq)]
struct PosixDst {
    abbrev: Abbreviation,
    offset: PosixOffset,
    rule: Rule,
}

impl PosixDst {
    /// Converts from the shared-but-internal API for use in proc macros.
    #[cfg(feature = "alloc")]
    fn from_shared_owned(sh: &shared::PosixDst<Abbreviation>) -> PosixDst {
        let abbrev = sh.abbrev;
        let offset = PosixOffset {
            offset: SpanZoneOffset::new(sh.offset)
                .expect("expected dst offset in range"),
        };
        let rule = Rule::from_shared(&sh.rule);
        PosixDst { abbrev, offset, rule }
    }

    /// Converts from the shared-but-internal API for use in proc macros.
    ///
    /// This works in a `const` context by requiring that the time zone
    /// abbreviations are `static` strings. This is used when converting
    /// code generated by a proc macro to this Jiff internal type.
    const fn from_shared_const(
        sh: &shared::PosixDst<&'static str>,
    ) -> PosixDst {
        use crate::util::constant::unwrap;

        let abbrev = unwrap!(
            Abbreviation::new(sh.abbrev),
            "expected short enough dst tz abbreviation"
        );
        let offset = PosixOffset {
            offset: unwrap!(
                SpanZoneOffset::new_const(sh.offset),
                "expected dst offset in range",
            ),
        };
        let rule = Rule::from_shared(&sh.rule);
        PosixDst { abbrev, offset, rule }
    }

    fn display(
        &self,
        std_offset: PosixOffset,
        f: &mut core::fmt::Formatter,
    ) -> core::fmt::Result {
        write!(f, "{}", AbbreviationDisplay(self.abbrev))?;
        // The overwhelming common case is that DST is exactly one hour ahead
        // of standard time. So common that this is the default. So don't write
        // the offset if we don't need to.
        let default =
            PosixOffset { offset: std_offset.offset + t::SECONDS_PER_HOUR };
        if self.offset != default {
            write!(f, "{}", self.offset)?;
        }
        write!(f, ",{}", self.rule)?;
        Ok(())
    }
}

/// The offset from UTC for standard-time or daylight-saving-time for this
/// time zone.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PosixOffset {
    offset: SpanZoneOffset,
}

impl PosixOffset {
    fn offset(&self) -> Offset {
        Offset::from_seconds_ranged(self.offset)
    }
}

impl core::fmt::Display for PosixOffset {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        let offset = self.offset();
        // Yes, this is backwards. Blame POSIX.
        // N.B. `+` is the default, so we don't
        // need to write that out.
        if offset.seconds() > 0 {
            write!(f, "-")?;
        }
        let h = offset.part_hours_ranged().get().unsigned_abs();
        let m = offset.part_minutes_ranged().get().unsigned_abs();
        let s = offset.part_seconds_ranged().get().unsigned_abs();
        write!(f, "{h}")?;
        if m != 0 || s != 0 {
            write!(f, ":{m:02}")?;
            if s != 0 {
                write!(f, ":{s:02}")?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
impl From<Offset> for PosixOffset {
    fn from(offset: Offset) -> PosixOffset {
        PosixOffset { offset: offset.seconds_ranged() }
    }
}

/// The rule for when a DST transition starts and ends.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Rule {
    start: PosixDateTimeSpec,
    end: PosixDateTimeSpec,
}

impl Rule {
    /// Converts from the shared-but-internal API for use in proc macros.
    const fn from_shared(sh: &shared::PosixRule) -> Rule {
        let start = PosixDateTimeSpec::from_shared(&sh.start);
        let end = PosixDateTimeSpec::from_shared(&sh.end);
        Rule { start, end }
    }
}

impl core::fmt::Display for Rule {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "{},{}", self.start, self.end)
    }
}

/// A specification for the day and an optional time at which a DST
/// transition occurs.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PosixDateTimeSpec {
    date: PosixDateSpec,
    time: PosixTimeSpec,
}

impl PosixDateTimeSpec {
    /// Converts from the shared-but-internal API for use in proc macros.
    const fn from_shared(sh: &shared::PosixDayTime) -> PosixDateTimeSpec {
        PosixDateTimeSpec {
            date: PosixDateSpec::from_shared(&sh.date),
            time: PosixTimeSpec::from_shared(sh.time),
        }
    }

    /// Turns this POSIX datetime spec into a civil datetime in the year given
    /// with the given offset. The datetimes returned are offset by the given
    /// offset. For wall clock time, an offset of `0` should be given. For
    /// UTC time, the offset (standard or DST) corresponding to this time
    /// spec should be given.
    ///
    /// The datetime returned is guaranteed to have a year component equal
    /// to the year given. This guarantee is upheld even when the datetime
    /// specification (combined with the offset) would extend past the end of
    /// the year (or before the start of the year). In this case, the maximal
    /// (or minimal) datetime for the given year is returned.
    fn to_datetime(&self, year: impl RInto<Year>, offset: Offset) -> DateTime {
        let year = year.rinto();
        let mkmin = || {
            Date::new_ranged(year, C(1), C(1)).unwrap().to_datetime(Time::MIN)
        };
        let mkmax = || {
            Date::new_ranged(year, C(12), C(31))
                .unwrap()
                .to_datetime(Time::MAX)
        };

        let Some(date) = self.date.to_civil_date(year) else { return mkmax() };
        let mut dt = date.to_datetime(Time::MIN);
        let dur = self.time().to_duration() - SignedDuration::from(offset);
        dt = dt.checked_add(dur).unwrap_or_else(|_| {
            if dur.is_negative() {
                mkmin()
            } else {
                mkmax()
            }
        });
        if dt.date().year() < year {
            mkmin()
        } else if dt.date().year() > year {
            mkmax()
        } else {
            dt
        }
    }

    /// Returns the time for this spec, falling back to the default of 2:00:00
    /// as specified by POSIX.
    fn time(self) -> PosixTimeSpec {
        self.time
    }
}

impl core::fmt::Display for PosixDateTimeSpec {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "{}", self.date)?;
        // This is the default time, so don't write it if we
        // don't need to.
        if self.time != PosixTimeSpec::DEFAULT {
            write!(f, "/{}", self.time)?;
        }
        Ok(())
    }
}

/// A specification for the day at which a DST transition occurs.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PosixDateSpec {
    /// POSIX says:
    ///
    /// > The Julian day n (`1 <= n <= 365`). Leap days shall not be counted.
    /// > That is, in all years-including leap years-February 28 is day 59
    /// > and March 1 is day 60. It is impossible to refer explicitly to the
    /// > occasional February 29.
    JulianOne(PosixJulianDayNoLeap),
    /// POSIX says:
    ///
    /// > The zero-based Julian day (`0 <= n <= 365`). Leap days shall be
    /// > counted, and it is possible to refer to February 29.
    JulianZero(PosixJulianDayWithLeap),
    /// The nth weekday of a particular month.
    WeekdayOfMonth(WeekdayOfMonth),
}

impl PosixDateSpec {
    /// Converts from the shared-but-internal API for use in proc macros.
    const fn from_shared(sh: &shared::PosixDay) -> PosixDateSpec {
        use crate::util::constant::unwrap;

        match *sh {
            shared::PosixDay::JulianOne(doy) => {
                let doy = unwrap!(
                    PosixJulianDayNoLeap::new_const(doy),
                    "expected 1-based Julian day in range"
                );
                PosixDateSpec::JulianOne(doy)
            }
            shared::PosixDay::JulianZero(doy) => {
                let doy = unwrap!(
                    PosixJulianDayWithLeap::new_const(doy),
                    "expected 0-based Julian day in range"
                );
                PosixDateSpec::JulianZero(doy)
            }
            shared::PosixDay::WeekdayOfMonth { month, week, weekday } => {
                let month = unwrap!(
                    Month::new_const(month),
                    "expected weekday-of-month month in range"
                );
                let week = unwrap!(
                    PosixWeek::new_const(week),
                    "expected weekday-of-month week in range"
                );
                let weekday = match weekday {
                    0 => Weekday::Sunday,
                    1 => Weekday::Monday,
                    2 => Weekday::Tuesday,
                    3 => Weekday::Wednesday,
                    4 => Weekday::Thursday,
                    5 => Weekday::Friday,
                    6 => Weekday::Saturday,
                    _ => panic!("expected weekday-of-month weekday in range"),
                };
                PosixDateSpec::WeekdayOfMonth(WeekdayOfMonth {
                    month,
                    week,
                    weekday,
                })
            }
        }
    }

    /// Convert this date specification to a civil date in the year given.
    ///
    /// If this date specification couldn't be turned into a date in the year
    /// given, then `None` is returned. This happens when `366` is given as
    /// a day, but the year given is not a leap year. In this case, callers may
    /// want to assume a datetime that is maximal for the year given.
    fn to_civil_date(&self, year: impl RInto<Year>) -> Option<Date> {
        match *self {
            PosixDateSpec::JulianOne(day) => {
                let first = Date::new_ranged(year, C(1), C(1)).unwrap();
                // Parsing validates that our day is 1-365 which will always
                // succeed for all possible year values. That is, every valid
                // year has a December 31.
                Some(
                    first
                        .with()
                        .day_of_year_no_leap(day.get())
                        .build()
                        .expect("Julian 'J day' should be in bounds"),
                )
            }
            PosixDateSpec::JulianZero(day) => {
                let first = Date::new_ranged(year, C(1), C(1)).unwrap();
                // OK because our value for `day` is validated to be `0..=365`,
                // and since it is an `i16`, it is always valid to add 1.
                let off1 = day.get().checked_add(1).unwrap();
                // While `off1` is guaranteed to be in `1..=366`, it is
                // possible that `366` is invalid. In this case, we throw
                // our hands up, and ask the caller to make a decision for
                // how to deal with it. Why does POSIX go out of its way to
                // specifically not specify behavior in error cases?
                first.with().day_of_year(off1).build().ok()
            }
            PosixDateSpec::WeekdayOfMonth(wom) => {
                let first = Date::new_ranged(year, wom.month, C(1)).unwrap();
                // This is maybe non-obvious, but this will always succeed
                // because it can only fail when the week number is one of {-5,
                // 0, 5}. Since we've validated that 'wom.week' is in 1..=5, we
                // know it can't be 0. Moreover, `wom.week()` never returns `5`
                // since `5` actually means "last weekday of month." That is,
                // `wom.week()` is guaranteed to return -1 or 1..=4.
                //
                // Also, I looked at how other libraries deal with this case,
                // and almost all of them just do a bunch of inline hairy
                // arithmetic here. I suppose I could be reduced to such
                // things if perf called for it, but we have a nice civil date
                // abstraction. So use it, god damn it.
                let week = wom.week();
                debug_assert!(week == -1 || (1..=4).contains(&week));
                Some(
                    first
                        .nth_weekday_of_month(week, wom.weekday)
                        .expect("nth weekday always exists"),
                )
            }
        }
    }
}

impl core::fmt::Display for PosixDateSpec {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match *self {
            PosixDateSpec::JulianOne(n) => write!(f, "J{n}"),
            PosixDateSpec::JulianZero(n) => write!(f, "{n}"),
            PosixDateSpec::WeekdayOfMonth(wk) => write!(f, "{wk}"),
        }
    }
}

/// A specification for the day of the month at which a DST transition occurs.
/// POSIX says:
///
/// > The `d`'th day (`0 <= d <= 6`) of week `n` of month `m` of the year (`1
/// > <= n <= 5`, `1 <= m <= 12`, where week `5` means "the last `d` day in
/// > month `m`" which may occur in either the fourth or the fifth week). Week
/// > `1` is the first week in which the `d`'th day occurs. Day zero is Sunday.
///
/// The interesting thing to note here (or my interpretation anyway), is that
/// a week of `4` means the "4th weekday in a month" where as a week of `5`
/// means the "last weekday in a month, even if it's the 4th weekday."
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct WeekdayOfMonth {
    month: Month,
    week: PosixWeek,
    weekday: Weekday,
}

impl WeekdayOfMonth {
    /// Returns the week number.
    ///
    /// This converts a week number of `5` to `-1`, which more sensible
    /// represents the "last week of the month."
    fn week(&self) -> i8 {
        if self.week == 5 {
            -1
        } else {
            self.week.get()
        }
    }
}

impl core::fmt::Display for WeekdayOfMonth {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(
            f,
            "M{month}.{week}.{weekday}",
            month = self.month,
            week = self.week,
            weekday = self.weekday.to_sunday_zero_offset(),
        )
    }
}

/// A specification for "time" in a POSIX time zone, with optional minute and
/// second components.
///
/// Note that this is more of a duration than a "time." While POSIX limits the
/// hour range to `0..=24` (and therefore looks _almost_ like a time), the
/// IANA tzfile v3+ format expands the range to `-167..=167`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PosixTimeSpec {
    duration: PosixTimeSeconds,
}

impl PosixTimeSpec {
    const DEFAULT: PosixTimeSpec = PosixTimeSpec {
        duration: PosixTimeSeconds::new_unchecked(2 * 60 * 60),
    };

    /// Converts from the shared-but-internal API for use in proc macros.
    const fn from_shared(seconds: i32) -> PosixTimeSpec {
        let duration = crate::util::constant::unwrap!(
            PosixTimeSeconds::new_const(seconds),
            "expected POSIX time spec seconds in range",
        );
        PosixTimeSpec { duration }
    }

    fn to_duration(&self) -> SignedDuration {
        SignedDuration::from_secs(self.duration.get().into())
    }
}

impl core::fmt::Display for PosixTimeSpec {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        let duration = self.to_duration();
        if duration.is_negative() {
            write!(f, "-")?;
            // The default is positive, so when
            // positive, we write nothing.
        }
        let h = duration.as_hours().unsigned_abs();
        let m = duration.as_mins().unsigned_abs() % 60;
        let s = duration.as_secs().unsigned_abs() % 60;
        write!(f, "{h}")?;
        if m != 0 || s != 0 {
            write!(f, ":{m:02}")?;
            if s != 0 {
                write!(f, ":{s:02}")?;
            }
        }
        Ok(())
    }
}

/// A helper type for formatting a time zone abbreviation.
///
/// Basically, this will write the `<` and `>` quotes if necessary, and
/// otherwise write out the abbreviation in its unquoted form.
#[derive(Debug)]
struct AbbreviationDisplay(Abbreviation);

impl core::fmt::Display for AbbreviationDisplay {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        let s = self.0.as_str();
        if s.chars().any(|ch| ch == '+' || ch == '-') {
            write!(f, "<{s}>")
        } else {
            write!(f, "{s}")
        }
    }
}

// The tests below all require parsing which requires alloc.
#[cfg(feature = "alloc")]
#[cfg(test)]
mod tests {
    use alloc::string::ToString;

    use crate::{civil::date, tz::offset};

    use super::*;

    fn posix_time_zone(input: impl AsRef<[u8]>) -> PosixTimeZone {
        let input = core::str::from_utf8(input.as_ref()).unwrap();
        let tz = PosixTimeZone::parse(input).unwrap();
        // While we're here, assert that converting the TZ back
        // to a string matches what we got. In the original version
        // of the POSIX TZ parser, we were very meticulous about
        // capturing the exact AST of the time zone. But I've
        // since simplified the data structure considerably such
        // that it is lossy in terms of what was actually parsed
        // (but of course, not lossy in terms of the semantic
        // meaning of the time zone).
        //
        // So to account for this, we serialize to a string and
        // then parse it back. We should get what we started with.
        let reparsed = PosixTimeZone::parse(tz.to_string()).unwrap();
        assert_eq!(tz, reparsed);
        assert_eq!(tz.to_string(), reparsed.to_string());
        tz
    }

    #[test]
    fn to_dst_civil_datetime_utc_range() {
        let tz = posix_time_zone("WART4WARST,J1/-3,J365/20");
        let dst_info = DstInfo {
            // We test this in other places. It's too annoying to write this
            // out here, and I didn't adopt snapshot testing until I had
            // written out these tests by hand. ¯\_(ツ)_/¯
            dst: tz.dst.as_ref().unwrap(),
            start: date(2024, 1, 1).at(1, 0, 0, 0),
            end: date(2024, 12, 31).at(23, 0, 0, 0),
        };
        assert_eq!(tz.dst_info_utc(C(2024)), Some(dst_info));

        let tz = posix_time_zone("WART4WARST,J1/-4,J365/21");
        let dst_info = DstInfo {
            dst: tz.dst.as_ref().unwrap(),
            start: date(2024, 1, 1).at(0, 0, 0, 0),
            end: date(2024, 12, 31).at(23, 59, 59, 999_999_999),
        };
        assert_eq!(tz.dst_info_utc(C(2024)), Some(dst_info));

        let tz = posix_time_zone("EST5EDT,M3.2.0,M11.1.0");
        let dst_info = DstInfo {
            dst: tz.dst.as_ref().unwrap(),
            start: date(2024, 3, 10).at(7, 0, 0, 0),
            end: date(2024, 11, 3).at(6, 0, 0, 0),
        };
        assert_eq!(tz.dst_info_utc(C(2024)), Some(dst_info));
    }

    #[test]
    fn reasonable() {
        assert!(PosixTimeZone::parse("EST5").is_ok());
        assert!(PosixTimeZone::parse("EST5EDT").is_err());
        assert!(PosixTimeZone::parse("EST5EDT,J1,J365").is_ok());

        let tz = posix_time_zone("EST24EDT,J1,J365");
        assert_eq!(
            tz,
            PosixTimeZone {
                std_abbrev: "EST".into(),
                std_offset: offset(-24).into(),
                dst: Some(PosixDst {
                    abbrev: "EDT".into(),
                    offset: offset(-23).into(),
                    rule: Rule {
                        start: PosixDateTimeSpec {
                            date: PosixDateSpec::JulianOne(C(1).rinto()),
                            time: PosixTimeSpec::DEFAULT,
                        },
                        end: PosixDateTimeSpec {
                            date: PosixDateSpec::JulianOne(C(365).rinto()),
                            time: PosixTimeSpec::DEFAULT,
                        },
                    },
                }),
            },
        );

        let tz = posix_time_zone("EST-24EDT,J1,J365");
        assert_eq!(
            tz,
            PosixTimeZone {
                std_abbrev: "EST".into(),
                std_offset: offset(24).into(),
                dst: Some(PosixDst {
                    abbrev: "EDT".into(),
                    offset: offset(25).into(),
                    rule: Rule {
                        start: PosixDateTimeSpec {
                            date: PosixDateSpec::JulianOne(C(1).rinto()),
                            time: PosixTimeSpec::DEFAULT,
                        },
                        end: PosixDateTimeSpec {
                            date: PosixDateSpec::JulianOne(C(365).rinto()),
                            time: PosixTimeSpec::DEFAULT,
                        },
                    },
                }),
            },
        );
    }

    #[test]
    fn posix_date_time_spec_to_datetime() {
        // For this test, we just keep the offset to zero to simplify things
        // a bit. We get coverage for non-zero offsets in higher level tests.
        let to_datetime = |spec: &PosixDateTimeSpec, year: i16| {
            let year = Year::new(year).unwrap();
            spec.to_datetime(year, crate::tz::offset(0))
        };

        let tz = posix_time_zone("EST5EDT,J1,J365/5:12:34");
        assert_eq!(
            to_datetime(&tz.rule().start, 2023),
            date(2023, 1, 1).at(2, 0, 0, 0),
        );
        assert_eq!(
            to_datetime(&tz.rule().end, 2023),
            date(2023, 12, 31).at(5, 12, 34, 0),
        );

        let tz = posix_time_zone("EST+5EDT,M3.2.0/2,M11.1.0/2");
        assert_eq!(
            to_datetime(&tz.rule().start, 2024),
            date(2024, 3, 10).at(2, 0, 0, 0),
        );
        assert_eq!(
            to_datetime(&tz.rule().end, 2024),
            date(2024, 11, 3).at(2, 0, 0, 0),
        );

        let tz = posix_time_zone("EST+5EDT,M1.1.1,M12.5.2");
        assert_eq!(
            to_datetime(&tz.rule().start, 2024),
            date(2024, 1, 1).at(2, 0, 0, 0),
        );
        assert_eq!(
            to_datetime(&tz.rule().end, 2024),
            date(2024, 12, 31).at(2, 0, 0, 0),
        );

        let tz = posix_time_zone("EST5EDT,0/0,J365/25");
        assert_eq!(
            to_datetime(&tz.rule().start, 2024),
            date(2024, 1, 1).at(0, 0, 0, 0),
        );
        assert_eq!(
            to_datetime(&tz.rule().end, 2024),
            date(2024, 12, 31).at(23, 59, 59, 999_999_999),
        );

        let tz = posix_time_zone("XXX3EDT4,0/0,J365/23");
        assert_eq!(
            to_datetime(&tz.rule().start, 2024),
            date(2024, 1, 1).at(0, 0, 0, 0),
        );
        assert_eq!(
            to_datetime(&tz.rule().end, 2024),
            date(2024, 12, 31).at(23, 0, 0, 0),
        );

        let tz = posix_time_zone("XXX3EDT4,0/0,365");
        assert_eq!(
            to_datetime(&tz.rule().end, 2023),
            date(2023, 12, 31).at(23, 59, 59, 999_999_999),
        );
        assert_eq!(
            to_datetime(&tz.rule().end, 2024),
            date(2024, 12, 31).at(2, 0, 0, 0),
        );

        let tz = posix_time_zone("XXX3EDT4,J1/-167:59:59,J365/167:59:59");
        assert_eq!(
            to_datetime(&tz.rule().start, 2024),
            date(2024, 1, 1).at(0, 0, 0, 0),
        );
        assert_eq!(
            to_datetime(&tz.rule().end, 2024),
            date(2024, 12, 31).at(23, 59, 59, 999_999_999),
        );
    }

    #[test]
    fn posix_date_time_spec_time() {
        let tz = posix_time_zone("EST5EDT,J1,J365/5:12:34");
        assert_eq!(tz.rule().start.time(), PosixTimeSpec::DEFAULT,);
        assert_eq!(
            tz.rule().end.time(),
            PosixTimeSpec {
                duration: PosixTimeSeconds::new(5 * 60 * 60 + 12 * 60 + 34)
                    .unwrap(),
            },
        );
    }

    #[test]
    fn posix_date_spec_to_date() {
        let tz = posix_time_zone("EST+5EDT,M3.2.0/2,M11.1.0/2");
        let start = tz.rule().start.date.to_civil_date(C(2023));
        assert_eq!(start, Some(date(2023, 3, 12)));
        let end = tz.rule().end.date.to_civil_date(C(2023));
        assert_eq!(end, Some(date(2023, 11, 5)));
        let start = tz.rule().start.date.to_civil_date(C(2024));
        assert_eq!(start, Some(date(2024, 3, 10)));
        let end = tz.rule().end.date.to_civil_date(C(2024));
        assert_eq!(end, Some(date(2024, 11, 3)));

        let tz = posix_time_zone("EST+5EDT,J60,J365");
        let start = tz.rule().start.date.to_civil_date(C(2023));
        assert_eq!(start, Some(date(2023, 3, 1)));
        let end = tz.rule().end.date.to_civil_date(C(2023));
        assert_eq!(end, Some(date(2023, 12, 31)));
        let start = tz.rule().start.date.to_civil_date(C(2024));
        assert_eq!(start, Some(date(2024, 3, 1)));
        let end = tz.rule().end.date.to_civil_date(C(2024));
        assert_eq!(end, Some(date(2024, 12, 31)));

        let tz = posix_time_zone("EST+5EDT,59,365");
        let start = tz.rule().start.date.to_civil_date(C(2023));
        assert_eq!(start, Some(date(2023, 3, 1)));
        let end = tz.rule().end.date.to_civil_date(C(2023));
        assert_eq!(end, None);
        let start = tz.rule().start.date.to_civil_date(C(2024));
        assert_eq!(start, Some(date(2024, 2, 29)));
        let end = tz.rule().end.date.to_civil_date(C(2024));
        assert_eq!(end, Some(date(2024, 12, 31)));

        let tz = posix_time_zone("EST+5EDT,M1.1.1,M12.5.2");
        let start = tz.rule().start.date.to_civil_date(C(2024));
        assert_eq!(start, Some(date(2024, 1, 1)));
        let end = tz.rule().end.date.to_civil_date(C(2024));
        assert_eq!(end, Some(date(2024, 12, 31)));
    }

    #[test]
    fn posix_time_spec_to_civil_time() {
        let tz = posix_time_zone("EST5EDT,J1,J365/5:12:34");
        assert_eq!(
            tz.dst.as_ref().unwrap().rule.start.time().to_duration(),
            SignedDuration::from_hours(2),
        );
        assert_eq!(
            tz.dst.as_ref().unwrap().rule.end.time().to_duration(),
            SignedDuration::new(5 * 60 * 60 + 12 * 60 + 34, 0),
        );

        let tz = posix_time_zone("EST5EDT,J1/23:59:59,J365/24:00:00");
        assert_eq!(
            tz.dst.as_ref().unwrap().rule.start.time().to_duration(),
            SignedDuration::new(23 * 60 * 60 + 59 * 60 + 59, 0),
        );
        assert_eq!(
            tz.dst.as_ref().unwrap().rule.end.time().to_duration(),
            SignedDuration::from_hours(24),
        );

        let tz = posix_time_zone("EST5EDT,J1/-1,J365/167:00:00");
        assert_eq!(
            tz.dst.as_ref().unwrap().rule.start.time().to_duration(),
            SignedDuration::from_hours(-1),
        );
        assert_eq!(
            tz.dst.as_ref().unwrap().rule.end.time().to_duration(),
            SignedDuration::from_hours(167),
        );
    }

    #[test]
    fn posix_time_spec_to_span() {
        let tz = posix_time_zone("EST5EDT,J1,J365/5:12:34");
        assert_eq!(
            tz.dst.as_ref().unwrap().rule.start.time().to_duration(),
            SignedDuration::from_hours(2),
        );
        assert_eq!(
            tz.dst.as_ref().unwrap().rule.end.time().to_duration(),
            SignedDuration::from_secs((5 * 60 * 60) + (12 * 60) + 34),
        );

        let tz = posix_time_zone("EST5EDT,J1/23:59:59,J365/24:00:00");
        assert_eq!(
            tz.dst.as_ref().unwrap().rule.start.time().to_duration(),
            SignedDuration::from_secs((23 * 60 * 60) + (59 * 60) + 59),
        );
        assert_eq!(
            tz.dst.as_ref().unwrap().rule.end.time().to_duration(),
            SignedDuration::from_hours(24),
        );

        let tz = posix_time_zone("EST5EDT,J1/-1,J365/167:00:00");
        assert_eq!(
            tz.dst.as_ref().unwrap().rule.start.time().to_duration(),
            SignedDuration::from_hours(-1),
        );
        assert_eq!(
            tz.dst.as_ref().unwrap().rule.end.time().to_duration(),
            SignedDuration::from_hours(167),
        );
    }

    #[cfg(feature = "tz-system")]
    #[test]
    fn parse_posix_tz() {
        // We used to parse this and then error when we tried to
        // convert to a "reasonable" POSIX time zone with a DST
        // transition rule. We never actually used unreasonable POSIX
        // time zones and it was complicating the type definitions, so
        // now we just reject it outright.
        assert!(PosixTzEnv::parse("EST5EDT").is_err());

        let tz = PosixTzEnv::parse(":EST5EDT").unwrap();
        assert_eq!(tz, PosixTzEnv::Implementation("EST5EDT".into()));

        // We require implementation strings to be UTF-8, because we're
        // sensible.
        assert!(PosixTzEnv::parse(b":EST5\xFFEDT").is_err());
    }

    #[test]
    fn parse_iana() {
        // Ref: https://github.com/chronotope/chrono/issues/1153
        let p = PosixTimeZone::parse("CRAZY5SHORT,M12.5.0/50,0/2").unwrap();
        assert_eq!(
            p,
            PosixTimeZone {
                std_abbrev: "CRAZY".into(),
                std_offset: offset(-5).into(),
                dst: Some(PosixDst {
                    abbrev: "SHORT".into(),
                    offset: offset(-4).into(),
                    rule: Rule {
                        start: PosixDateTimeSpec {
                            date: PosixDateSpec::WeekdayOfMonth(
                                WeekdayOfMonth {
                                    month: C(12).rinto(),
                                    week: C(5).rinto(),
                                    weekday: Weekday::Sunday,
                                },
                            ),
                            time: PosixTimeSpec {
                                duration: PosixTimeSeconds::new(50 * 60 * 60)
                                    .unwrap(),
                            },
                        },
                        end: PosixDateTimeSpec {
                            date: PosixDateSpec::JulianZero(C(0).rinto()),
                            time: PosixTimeSpec {
                                duration: PosixTimeSeconds::new(2 * 60 * 60)
                                    .unwrap(),
                            },
                        },
                    },
                }),
            },
        );

        assert!(PosixTimeZone::parse("America/New_York").is_err());
        assert!(PosixTimeZone::parse(":America/New_York").is_err());
    }
}
