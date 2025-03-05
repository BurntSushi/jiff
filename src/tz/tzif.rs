/*!
This module provides support for TZif binary files from the [Time Zone
Database].

These binary files are the ones commonly found in Unix distributions in the
`/usr/share/zoneinfo` directory.

[Time Zone Database]: https://www.iana.org/time-zones
*/

use core::ops::Range;

#[cfg(feature = "alloc")]
use alloc::{string::String, vec::Vec};

use crate::{
    civil::DateTime,
    error::{err, Error},
    shared,
    timestamp::Timestamp,
    tz::{
        posix::PosixTimeZone, timezone::TimeZoneAbbreviation, AmbiguousOffset,
        Dst, Offset, TimeZoneOffsetInfo, TimeZoneTransition,
    },
};

/// The owned variant of `Tzif`.
#[cfg(feature = "alloc")]
pub(crate) type TzifOwned = Tzif<String, Vec<LocalTimeType>, Vec<Transition>>;

/// The static variant of `Tzif`.
pub(crate) type TzifStatic =
    Tzif<&'static str, &'static [LocalTimeType], &'static [Transition]>;

/// A time zone based on IANA TZif formatted data.
///
/// TZif is a binary format described by RFC 8536. Its typical structure is to
/// define a single time zone per file in the `/usr/share/zoneinfo` directory
/// on Unix systems. The name of a time zone is its file path with the
/// `/usr/share/zoneinfo/` prefix stripped from it.
///
/// This type doesn't provide any facilities for dealing with files on disk
/// or the `/usr/share/zoneinfo` directory. This type is just for parsing the
/// contents of TZif formatted data in memory, and turning it into a data type
/// that can be used as a time zone.
#[derive(Debug)]
// not part of Jiff's public API
#[doc(hidden)]
// This ensures the alignment of this type is always *at least* 8 bytes. This
// is required for the pointer tagging inside of `TimeZone` to be sound. At
// time of writing (2024-02-24), this explicit `repr` isn't required on 64-bit
// systems since the type definition is such that it will have an alignment of
// at least 8 bytes anyway. But this *is* required for 32-bit systems, where
// the type definition at present only has an alignment of 4 bytes.
#[repr(align(8))]
pub struct Tzif<STRING, TYPES, TRANS> {
    name: Option<STRING>,
    /// An ASCII byte corresponding to the version number. So, 0x50 is '2'.
    ///
    /// This is unused. It's only used in `test` compilation for emitting
    /// diagnostic data about TZif files. If we really need to use this, we
    /// should probably just convert it to an actual integer.
    #[allow(dead_code)]
    version: u8,
    checksum: u32,
    designations: STRING,
    posix_tz: Option<PosixTimeZone>,
    types: TYPES,
    transitions: TRANS,
}

impl TzifStatic {
    /// Converts from the shared-but-internal API for use in proc macros.
    ///
    /// This specifically works in a `const` context. And it requires that
    /// caller to pass in the parsed `Tzif` in its fixed form along with the
    /// variable length local time types and transitions. (Technically, the
    /// TZ identifier and the designations are also variable length despite
    /// being parsed of `TzifFixed`, but in practice they can be handled just
    /// fine via `&'static str`.)
    ///
    /// Notice that the `types` and `transitions` are *not* from the `shared`
    /// API, but rather, from the types defined in this module. They have to
    /// be this way because there's a conversion step that occurs. In practice,
    /// this sort of thing is embedded as a literal in source code via a proc
    /// macro. Like this:
    ///
    /// ```text
    /// static TZIF: Tzif<&str, &[LocalTimeType], &[Transition]> =
    ///     Tzif::from_shared_const(
    ///         shared::TzifFixed {
    ///             name: Some("America/New_York"),
    ///             version: b'3',
    ///             checksum: 0xDEADBEEF,
    ///             designations: "ESTEDT",
    ///             posix_tz: None,
    ///         },
    ///         &[
    ///             shared::TzifLocalTimeType {
    ///                 offset: -5 * 60 * 60,
    ///                 is_dst: false,
    ///                 designation: 0..3,
    ///                 indicator: shared::TzifIndicator::LocalWall,
    ///             }.to_jiff(),
    ///         ],
    ///         &[
    ///             shared::TzifTransition {
    ///                 timestamp: 123456789,
    ///                 type_index: 0,
    ///             }.to_jiff(-5, -5),
    ///         ],
    ///     );
    /// ```
    ///
    /// Or something like that anyway. The point is, our `static` slices are
    /// variable length and they need to be the right types. At least, I
    /// couldn't see a simpler way to arrange this.
    pub(crate) const fn from_shared_const(
        sh: &shared::TzifFixed<&'static str, &'static str>,
        types: &'static [LocalTimeType],
        transitions: &'static [Transition],
    ) -> TzifStatic {
        let name = sh.name;
        let version = sh.version;
        let checksum = sh.checksum;
        let designations = sh.designations;
        let posix_tz = match sh.posix_tz {
            None => None,
            Some(ref tz) => Some(tz.to_jiff()),
        };
        // Unlike in the owned case, we specifically do not check that the
        // POSIX time zone is consistent with the last transition. This is
        // because it would require making a lot of code in Jiff `const`
        // that is difficult to make `const`. Moreover, this constructor is
        // generally only used with the `jiff-static` proc-macros, and those
        // go through the owned APIs at compile time. And thus, it is already
        // validated that the POSIX time zone is consistent with the last
        // transition.
        Tzif {
            name,
            version,
            checksum,
            designations,
            posix_tz,
            types,
            transitions,
        }
    }
}

#[cfg(feature = "alloc")]
impl TzifOwned {
    /// Parses the given data as a TZif formatted file.
    ///
    /// The name given is attached to the `Tzif` value returned, but is
    /// otherwise not significant.
    ///
    /// If the given data is not recognized to be valid TZif, then an error is
    /// returned.
    ///
    /// In general, callers may assume that it is safe to pass arbitrary or
    /// even untrusted data to this function and count on it not panicking
    /// or using resources that aren't limited to a small constant factor of
    /// the size of the data itself. That is, callers can reliably limit the
    /// resources used by limiting the size of the data given to this parse
    /// function.
    pub(crate) fn parse(
        name: Option<String>,
        bytes: &[u8],
    ) -> Result<Self, Error> {
        let sh =
            shared::TzifOwned::parse(name, bytes).map_err(Error::shared)?;
        let tzif = TzifOwned::from_shared_owned(&sh)?;
        Ok(tzif)
    }

    /// Converts from the shared-but-internal API for use in proc macros.
    ///
    /// This is not `const` since it accepts owned `String` and `Vec` values
    /// for variable length data inside `Tzif`.
    pub(crate) fn from_shared_owned(
        sh: &shared::TzifOwned,
    ) -> Result<TzifOwned, Error> {
        let name = sh.fixed.name.clone();
        let version = sh.fixed.version;
        let checksum = sh.fixed.checksum;
        let designations = sh.fixed.designations.clone();
        let posix_tz =
            sh.fixed.posix_tz.as_ref().map(PosixTimeZone::from_shared_owned);
        let types: Vec<LocalTimeType> =
            sh.types.iter().map(shared::TzifLocalTimeType::to_jiff).collect();
        let mut transitions = Vec::with_capacity(sh.transitions.len());
        for (i, this) in sh.transitions.iter().enumerate() {
            let prev = &sh.transitions[i.saturating_sub(1)];
            let prev_offset = sh.types[usize::from(prev.type_index)].offset;
            let this_offset = sh.types[usize::from(this.type_index)].offset;
            transitions.push(this.to_jiff(prev_offset, this_offset));
        }
        let tzif = Tzif {
            name,
            version,
            checksum,
            designations,
            posix_tz,
            types,
            transitions,
        };
        tzif.verify_posix_time_zone_consistency()?;
        Ok(tzif)
    }

    /// Validates that the POSIX TZ string we parsed (if one exists) is
    /// consistent with the last transition in this time zone. This is
    /// required by RFC 8536.
    ///
    /// RFC 8536 says, "If the string is nonempty and one or more
    /// transitions appear in the version 2+ data, the string MUST be
    /// consistent with the last version 2+ transition."
    fn verify_posix_time_zone_consistency(&self) -> Result<(), Error> {
        // We need to be a little careful, since we always have at least one
        // transition (accounting for the dummy `Timestamp::MIN` transition).
        // So if we only have 1 transition and a POSIX TZ string, then we
        // should not validate it since it's equivalent to the case of 0
        // transitions and a POSIX TZ string.
        if self.transitions.len() <= 1 {
            return Ok(());
        }
        let Some(ref tz) = self.posix_tz else {
            return Ok(());
        };
        let last = self.transitions.last().expect("last transition");
        let typ = self.local_time_type(last);
        let info = tz.to_offset_info(last.timestamp);
        if info.offset() != typ.offset {
            return Err(err!(
                "expected last transition to have DST offset \
                 of {expected_offset}, but got {got_offset} \
                 according to POSIX TZ string {tz}",
                expected_offset = typ.offset,
                got_offset = info.offset(),
                tz = tz,
            ));
        }
        if info.dst() != typ.is_dst {
            return Err(err!(
                "expected last transition to have is_dst={expected_dst}, \
                 but got is_dst={got_dst} according to POSIX TZ \
                 string {tz}",
                expected_dst = typ.is_dst.is_dst(),
                got_dst = info.dst().is_dst(),
                tz = tz,
            ));
        }
        if info.abbreviation() != self.designation(&typ) {
            return Err(err!(
                "expected last transition to have \
                 designation={expected_abbrev}, \
                 but got designation={got_abbrev} according to POSIX TZ \
                 string {tz}",
                expected_abbrev = self.designation(&typ),
                got_abbrev = info.abbreviation(),
                tz = tz,
            ));
        }
        Ok(())
    }
}

impl<
        STRING: AsRef<str>,
        TYPES: AsRef<[LocalTimeType]>,
        TRANS: AsRef<[Transition]>,
    > Tzif<STRING, TYPES, TRANS>
{
    /// Returns the name given to this TZif data in its constructor.
    pub(crate) fn name(&self) -> Option<&str> {
        self.name.as_ref().map(|n| n.as_ref())
    }

    /// Returns the appropriate time zone offset to use for the given
    /// timestamp.
    pub(crate) fn to_offset(&self, timestamp: Timestamp) -> Offset {
        match self.to_local_time_type(timestamp) {
            Ok(typ) => typ.offset,
            Err(tz) => tz.to_offset(timestamp),
        }
    }

    /// Returns the appropriate time zone offset to use for the given
    /// timestamp.
    ///
    /// This also includes whether the offset returned should be considered to
    /// be DST or not, along with the time zone abbreviation (e.g., EST for
    /// standard time in New York, and EDT for DST in New York).
    pub(crate) fn to_offset_info(
        &self,
        timestamp: Timestamp,
    ) -> TimeZoneOffsetInfo<'_> {
        let typ = match self.to_local_time_type(timestamp) {
            Ok(typ) => typ,
            Err(tz) => return tz.to_offset_info(timestamp),
        };
        let abbreviation =
            TimeZoneAbbreviation::Borrowed(self.designation(typ));
        TimeZoneOffsetInfo {
            offset: typ.offset,
            dst: typ.is_dst,
            abbreviation,
        }
    }

    /// Returns the local time type for the timestamp given.
    ///
    /// If one could not be found, then this implies that the caller should
    /// use the POSIX time zone returned in the error variant.
    fn to_local_time_type(
        &self,
        timestamp: Timestamp,
    ) -> Result<&LocalTimeType, &PosixTimeZone> {
        // This is guaranteed because we always push at least one transition.
        // This isn't guaranteed by TZif since it might have 0 transitions,
        // but we always add a "dummy" first transition with our minimum
        // `Timestamp` value. TZif doesn't do this because there is no
        // universal minimum timestamp. (`i64::MIN` is a candidate, but that's
        // likely to cause overflow in readers that don't do error checking.)
        //
        // The result of the dummy transition is that the code below is simpler
        // with fewer special cases.
        assert!(!self.transitions().is_empty(), "transitions is non-empty");
        let index = if timestamp > self.transitions().last().unwrap().timestamp
        {
            self.transitions().len() - 1
        } else {
            let search = self
                .transitions()
                // It is an optimization to compare only by the second instead
                // of the second and the nanosecond. This works for two
                // reasons. Firstly, the timestamps in TZif are limited to
                // second precision. Secondly, this may result in two
                // timestamps comparing equal when they would otherwise be
                // unequal (for example, when a timestamp given falls on a
                // transition, but has non-zero fractional seconds). But this
                // is okay, because it would otherwise get an `Err(i)`, and
                // access `i-1`. i.e., The timestamp it compared equal to.
                .binary_search_by_key(&timestamp.as_second(), |t| {
                    t.timestamp.as_second()
                });
            match search {
                // Since the first transition is always Timestamp::MIN, it's
                // impossible for any timestamp to sort before it.
                Err(0) => {
                    unreachable!("impossible to come before Timestamp::MIN")
                }
                Ok(i) => i,
                // i points to the position immediately after the matching
                // timestamp. And since we know that i>0 because of the i==0
                // check above, we can safely subtract 1.
                Err(i) => i.checked_sub(1).expect("i is non-zero"),
            }
        };
        // Our index is always in bounds. The only way it couldn't be is if
        // binary search returns an Err(len) for a time greater than the
        // maximum transition. But we account for that above by converting
        // Err(len) to Err(len-1).
        assert!(index < self.transitions().len());
        // RFC 8536 says: "Local time for timestamps on or after the last
        // transition is specified by the TZ string in the footer (Section 3.3)
        // if present and nonempty; otherwise, it is unspecified."
        //
        // Subtracting 1 is OK because we know self.transitions is not empty.
        let t = if index < self.transitions().len() - 1 {
            // This is the typical case in "fat" TZif files: we found a
            // matching transition.
            &self.transitions()[index]
        } else {
            match self.posix_tz.as_ref() {
                // This is the typical case in "slim" TZif files, where the
                // last transition is, as I understand it, the transition at
                // which a consistent rule started that a POSIX TZ string can
                // fully describe. For example, (as of 2024-03-27) the last
                // transition in the "fat" America/New_York TZif file is
                // in 2037, where as in the "slim" version it is 2007.
                //
                // This is likely why some things break with the "slim"
                // version: they don't support POSIX TZ strings (or don't
                // support them correctly).
                Some(tz) => return Err(tz),
                // This case is technically unspecified, but I think the
                // typical thing to do is to just use the last transition.
                // I'm not 100% sure on this one.
                None => &self.transitions()[index],
            }
        };
        Ok(self.local_time_type(t))
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
        // This implementation very nearly mirrors `to_offset` above in the
        // beginning: we do a binary search to find transition applicable for
        // the given datetime. Except, we do it on wall clock times instead
        // of timestamps. And in particular, each transition begins with a
        // possibly ambiguous range of wall clock times corresponding to either
        // a "gap" or "fold" in time.
        assert!(!self.transitions().is_empty(), "transitions is non-empty");
        let search =
            self.transitions().binary_search_by_key(&dt, |t| t.wall.start());
        let this_index = match search {
            Err(0) => unreachable!("impossible to come before DateTime::MIN"),
            Ok(i) => i,
            Err(i) => i.checked_sub(1).expect("i is non-zero"),
        };
        assert!(this_index < self.transitions().len());

        let this = &self.transitions()[this_index];
        let this_offset = self.local_time_type(this).offset;
        // This is a little tricky, but we need to check for ambiguous civil
        // datetimes before possibly using the POSIX TZ string. Namely, a
        // datetime could be ambiguous with respect to the last transition,
        // and we should handle that according to the gap/fold determined for
        // that transition. We cover this case in tests in tz/mod.rs for the
        // Pacific/Honolulu time zone, whose last transition begins with a gap.
        match this.wall {
            TransitionWall::Gap { end, .. } if dt < end => {
                // A gap/fold can only appear when there exists a previous
                // transition.
                let prev_index = this_index.checked_sub(1).unwrap();
                let prev = &self.transitions()[prev_index];
                let prev_offset = self.local_time_type(prev).offset;
                return AmbiguousOffset::Gap {
                    before: prev_offset,
                    after: this_offset,
                };
            }
            TransitionWall::Fold { end, .. } if dt < end => {
                // A gap/fold can only appear when there exists a previous
                // transition.
                let prev_index = this_index.checked_sub(1).unwrap();
                let prev = &self.transitions()[prev_index];
                let prev_offset = self.local_time_type(prev).offset;
                return AmbiguousOffset::Fold {
                    before: prev_offset,
                    after: this_offset,
                };
            }
            _ => {}
        }
        // The datetime given is not ambiguous with respect to any of the
        // transitions in the TZif data. But, if we matched at or after the
        // last transition, then we need to use the POSIX TZ string (which
        // could still return an ambiguous offset).
        if this_index == self.transitions().len() - 1 {
            if let Some(tz) = self.posix_tz.as_ref() {
                return tz.to_ambiguous_kind(dt);
            }
            // This case is unspecified according to RFC 8536. It means that
            // the given datetime exceeds all transitions *and* there is no
            // POSIX TZ string. So this can happen in V1 files for example.
            // But those should hopefully be essentially non-existent nowadays
            // (2024-03). In any case, we just fall through to using the last
            // transition, which does seem likely to be wrong ~half the time
            // in time zones with DST. But there really isn't much else we can
            // do I think.
        }
        AmbiguousOffset::Unambiguous { offset: this_offset }
    }

    /// Returns the timestamp of the most recent time zone transition prior
    /// to the timestamp given. If one doesn't exist, `None` is returned.
    pub(crate) fn previous_transition(
        &self,
        ts: Timestamp,
    ) -> Option<TimeZoneTransition> {
        assert!(!self.transitions().is_empty(), "transitions is non-empty");
        let search =
            self.transitions().binary_search_by_key(&ts, |t| t.timestamp);
        let index = match search {
            Ok(i) | Err(i) => i.checked_sub(1)?,
        };
        let trans = if index == 0 {
            // The first transition is a dummy that we insert, so if we land on
            // it here, treat it as if it doesn't exist.
            return None;
        } else if index == self.transitions().len() - 1 {
            if let Some(ref posix_tz) = self.posix_tz {
                // Since the POSIX TZ must be consistent with the last
                // transition, it must be the case that tzif_last <=
                // posix_prev_trans in all cases. So the transition according
                // to the POSIX TZ is always correct here.
                //
                // What if this returns `None` though? I'm not sure in which
                // cases that could matter, and I think it might be a violation
                // of the TZif format if it does.
                return posix_tz.previous_transition(ts);
            }
            &self.transitions()[index]
        } else {
            &self.transitions()[index]
        };
        let typ = &self.types()[usize::from(trans.type_index)];
        Some(TimeZoneTransition {
            timestamp: trans.timestamp,
            offset: typ.offset,
            abbrev: self.designation(typ),
            dst: typ.is_dst,
        })
    }

    /// Returns the timestamp of the soonest time zone transition after the
    /// timestamp given. If one doesn't exist, `None` is returned.
    pub(crate) fn next_transition(
        &self,
        ts: Timestamp,
    ) -> Option<TimeZoneTransition> {
        assert!(!self.transitions().is_empty(), "transitions is non-empty");
        let search =
            self.transitions().binary_search_by_key(&ts, |t| t.timestamp);
        let index = match search {
            Ok(i) => i.checked_add(1)?,
            Err(i) => i,
        };
        let trans = if index == 0 {
            // The first transition is a dummy that we insert, so if we land on
            // it here, treat it as if it doesn't exist.
            return None;
        } else if index >= self.transitions().len() - 1 {
            if let Some(ref posix_tz) = self.posix_tz {
                // Since the POSIX TZ must be consistent with the last
                // transition, it must be the case that next.timestamp <=
                // posix_next_tans in all cases. So the transition according to
                // the POSIX TZ is always correct here.
                //
                // What if this returns `None` though? I'm not sure in which
                // cases that could matter, and I think it might be a violation
                // of the TZif format if it does.
                return posix_tz.next_transition(ts);
            }
            self.transitions().last().expect("last transition")
        } else {
            &self.transitions()[index]
        };
        let typ = &self.types()[usize::from(trans.type_index)];
        Some(TimeZoneTransition {
            timestamp: trans.timestamp,
            offset: typ.offset,
            abbrev: self.designation(typ),
            dst: typ.is_dst,
        })
    }

    fn designation(&self, typ: &LocalTimeType) -> &str {
        // OK because we verify that the designation range on every local
        // time type is a valid range into `self.designations`.
        &self.designations()[typ.designation()]
    }

    fn local_time_type(&self, transition: &Transition) -> &LocalTimeType {
        // OK because we require that `type_index` always points to a valid
        // local time type.
        &self.types()[usize::from(transition.type_index)]
    }

    fn designations(&self) -> &str {
        self.designations.as_ref()
    }

    fn types(&self) -> &[LocalTimeType] {
        self.types.as_ref()
    }

    fn transitions(&self) -> &[Transition] {
        self.transitions.as_ref()
    }
}

impl<STRING: AsRef<str>, TYPES, TRANS> Eq for Tzif<STRING, TYPES, TRANS> {}

impl<STRING: AsRef<str>, TYPES, TRANS> PartialEq
    for Tzif<STRING, TYPES, TRANS>
{
    fn eq(&self, rhs: &Self) -> bool {
        self.name.as_ref().map(|n| n.as_ref())
            == rhs.name.as_ref().map(|n| n.as_ref())
            && self.checksum == rhs.checksum
    }
}

/// A transition to a different offset.
#[derive(Clone, Debug, Eq, PartialEq)]
#[doc(hidden)] // not part of Jiff's public API
pub struct Transition {
    /// The UNIX leap time at which the transition starts. The transition
    /// continues up to and _not_ including the next transition.
    timestamp: Timestamp,
    /// The wall clock time for when this transition begins. This includes
    /// boundary conditions for quickly determining if a given wall clock time
    /// is ambiguous (i.e., falls in a gap or a fold).
    wall: TransitionWall,
    /// The index into the sequence of local time type records. This is what
    /// provides the correct offset (from UTC) that is active beginning at
    /// this transition.
    type_index: u8,
}

impl Transition {
    /// Converts from the shared-but-internal API for use in proc macros.
    pub(crate) const fn from_shared(
        sh: &shared::TzifTransition,
        prev_offset: i32,
        this_offset: i32,
    ) -> Transition {
        let timestamp = Timestamp::constant(sh.timestamp, 0);
        let wall = TransitionWall::new(sh.timestamp, prev_offset, this_offset);
        let type_index = sh.type_index;
        Transition { timestamp, wall, type_index }
    }
}

/// The wall clock time for when a transition begins.
///
/// This explicitly represents ambiguous wall clock times that occur at the
/// boundaries of transitions.
///
/// The start of the wall clock time is always the earlier possible wall clock
/// time that could occur with this transition's corresponding offset. For a
/// gap, it's the previous transition's offset. For a fold, it's the current
/// transition's offset.
///
/// For example, DST for `America/New_York` began on `2024-03-10T07:00:00+00`.
/// The offset prior to this instant in time is `-05`, corresponding
/// to standard time (EST). Thus, in wall clock time, DST began at
/// `2024-03-10T02:00:00`. And since this is a DST transition that jumps ahead
/// an hour, the start of DST also corresponds to the start of a gap. That is,
/// the times `02:00:00` through `02:59:59` never appear on a clock for this
/// hour. The question is thus: which offset should we apply to `02:00:00`?
/// We could apply the offset from the earlier transition `-05` and get
/// `2024-03-10T01:00:00-05` (that's `2024-03-10T06:00:00+00`), or we could
/// apply the offset from the later transition `-04` and get
/// `2024-03-10T03:00:00-04` (that's `2024-03-10T07:00:00+00`).
///
/// So in the above, we would have a `Gap` variant where `start` (inclusive) is
/// `2024-03-10T02:00:00` and `end` (exclusive) is `2024-03-10T03:00:00`.
///
/// The fold case is the same idea, but where the same time is repeated.
/// For example, in `America/New_York`, standard time began on
/// `2024-11-03T06:00:00+00`. The offset prior to this instant in time
/// is `-04`, corresponding to DST (EDT). Thus, in wall clock time, DST
/// ended at `2024-11-03T02:00:00`. However, since this is a fold, the
/// actual set of ambiguous times begins at `2024-11-03T01:00:00` and
/// ends at `2024-11-03T01:59:59.999999999`. That is, the wall clock time
/// `2024-11-03T02:00:00` is unambiguous.
///
/// So in the fold case above, we would have a `Fold` variant where
/// `start` (inclusive) is `2024-11-03T01:00:00` and `end` (exclusive) is
/// `2024-11-03T02:00:00`.
///
/// Since this gets bundled in with the sorted sequence of transitions, we'll
/// use the "start" time in all three cases as our target of binary search.
/// Once we land on a transition, we'll know our given wall clock time is
/// greater than or equal to its start wall clock time. At that point, to
/// determine if there is ambiguity, we merely need to determine if the given
/// wall clock time is less than the corresponding `end` time. If it is, then
/// it falls in a gap or fold. Otherwise, it's unambiguous.
///
/// Note that we could compute these datetime values while searching for the
/// correct transition, but there's a fair bit of math involved in going
/// between timestamps (which is what TZif gives us) and calendar datetimes
/// (which is what we're given as input). It is also necessary that we offset
/// the timestamp given in TZif at some point, since it is in UTC and the
/// datetime given is in wall clock time. So I decided it would be worth
/// pre-computing what we need in terms of what the input is. This way, we
/// don't need to do any conversions, or indeed, any arithmetic at all, for
/// time zone lookups. We *could* store these as transitions, but then the
/// input datetime would need to be converted to a timestamp before searching
/// the transitions.
#[derive(Clone, Debug, Eq, PartialEq)]
enum TransitionWall {
    /// This transition cannot possibly lead to an unambiguous offset because
    /// its offset is equivalent to the offset of the previous transition.
    Unambiguous {
        /// The civil datetime corresponding to the beginning of this
        /// transition, inclusive.
        start: DateTime,
    },
    /// This occurs when this transition's offset is strictly greater than the
    /// previous transition's offset. This effectively results in a "gap" of
    /// time equal to the difference in the offsets between the two
    /// transitions.
    Gap {
        /// The start of a gap (inclusive) in wall clock time.
        start: DateTime,
        /// The end of the gap (exclusive) in wall clock time.
        end: DateTime,
    },
    /// This occurs when this transition's offset is strictly less than the
    /// previous transition's offset. This results in a "fold" of time where
    /// the two transitions have an overlap where it is ambiguous which one
    /// applies given a wall clock time. In effect, a span of time equal to the
    /// difference in the offsets is repeated.
    Fold {
        /// The start of the fold (inclusive) in wall clock time.
        start: DateTime,
        /// The end of the fold (exclusive) in wall clock time.
        end: DateTime,
    },
}

impl TransitionWall {
    /// Creates transition data based on wall-clock time.
    ///
    /// This data isn't directly part of TZif, but can be derived from it.
    /// It is principally done so that TZ lookups for civil datetime are
    /// faster. That is, we pre-compute whatever we can here.
    ///
    /// `timestamp` corresponds to the timestamp of the respective transition.
    /// `this_offset` is the offset associated with that transition (via the
    /// corresponding local time type), and `prev_offset` is the offset of the
    /// previous transition (also through its corresponding local time type).
    const fn new(
        timestamp: i64,
        prev_offset: i32,
        this_offset: i32,
    ) -> TransitionWall {
        const fn to_datetime(timestamp: i64, offset: i32) -> DateTime {
            use crate::shared::util::itime::{IOffset, ITimestamp};
            let its = ITimestamp { second: timestamp, nanosecond: 0 };
            let ioff = IOffset { second: offset };
            let idt = its.to_datetime(ioff);
            DateTime::from_idatetime_const(idt)
        }

        if prev_offset == this_offset {
            // Equivalent offsets means there can never be any ambiguity.
            let start = to_datetime(timestamp, prev_offset);
            TransitionWall::Unambiguous { start }
        } else if prev_offset < this_offset {
            // When the offset of the previous transition is less, that
            // means there is some non-zero amount of time that is
            // "skipped" when moving to the next transition. Thus, we have
            // a gap. The start of the gap is the offset which gets us the
            // earliest time, i.e., the smaller of the two offsets.
            let start = to_datetime(timestamp, prev_offset);
            let end = to_datetime(timestamp, this_offset);
            TransitionWall::Gap { start, end }
        } else {
            // When the offset of the previous transition is greater, that
            // means there is some non-zero amount of time that will be
            // replayed on a wall clock in this time zone. Thus, we have
            // a fold. The start of the gold is the offset which gets us
            // the earliest time, i.e., the smaller of the two offsets.
            assert!(prev_offset > this_offset);
            let start = to_datetime(timestamp, this_offset);
            let end = to_datetime(timestamp, prev_offset);
            TransitionWall::Fold { start, end }
        }
    }

    fn start(&self) -> DateTime {
        match *self {
            TransitionWall::Unambiguous { start } => start,
            TransitionWall::Gap { start, .. } => start,
            TransitionWall::Fold { start, .. } => start,
        }
    }
}

/// A single local time type.
///
/// Basically, this is what transition times map to. Once you have a local time
/// type, then you know the offset, whether it's in DST and the corresponding
/// abbreviation. (There is also an "indicator," but I have no clue what it
/// means. See the `Indicator` type for a rant.)
#[derive(Clone, Debug, Eq, PartialEq)]
#[doc(hidden)] // not part of Jiff's public API
pub struct LocalTimeType {
    offset: Offset,
    is_dst: Dst,
    designation: Range<u8>,
    indicator: Indicator,
}

impl LocalTimeType {
    /// Converts from the shared-but-internal API for use in proc macros.
    pub(crate) const fn from_shared(
        sh: &shared::TzifLocalTimeType,
    ) -> LocalTimeType {
        let offset = Offset::constant_seconds(sh.offset);
        let is_dst = if sh.is_dst { Dst::Yes } else { Dst::No };
        let designation = sh.designation.0..sh.designation.1;
        let indicator = Indicator::from_shared(&sh.indicator);
        LocalTimeType { offset, is_dst, designation, indicator }
    }

    fn designation(&self) -> Range<usize> {
        usize::from(self.designation.start)..usize::from(self.designation.end)
    }
}

/// This enum corresponds to the possible indicator values for standard/wall
/// and UT/local.
///
/// Note that UT+Wall is not allowed.
///
/// I honestly have no earthly clue what they mean. I've read the section about
/// them in RFC 8536 several times and I can't make sense of it. I've even
/// looked at data files that have these set and still can't make sense of
/// them. I've even looked at what other datetime libraries do with these, and
/// they all seem to just ignore them. Like, WTF. I've spent the last couple
/// months of my life steeped in time, and I just cannot figure this out. Am I
/// just dumb?
///
/// Anyway, we parse them, but otherwise ignore them because that's what all
/// the cool kids do.
///
/// The default is `LocalWall`, which also occurs when no indicators are
/// present.
///
/// I tried again and still don't get it. Here's a dump for `Pacific/Honolulu`:
///
/// ```text
/// $ ./scripts/jiff-debug tzif /usr/share/zoneinfo/Pacific/Honolulu
/// TIME ZONE NAME
///   /usr/share/zoneinfo/Pacific/Honolulu
/// LOCAL TIME TYPES
///   000: offset=-10:31:26, is_dst=false, designation=LMT, indicator=local/wall
///   001: offset=-10:30, is_dst=false, designation=HST, indicator=local/wall
///   002: offset=-09:30, is_dst=true, designation=HDT, indicator=local/wall
///   003: offset=-09:30, is_dst=true, designation=HWT, indicator=local/wall
///   004: offset=-09:30, is_dst=true, designation=HPT, indicator=ut/std
///   005: offset=-10, is_dst=false, designation=HST, indicator=local/wall
/// TRANSITIONS
///   0000: -9999-01-02T01:59:59 :: -377705023201 :: type=0, -10:31:26, is_dst=false, LMT, local/wall
///   0001: 1896-01-13T22:31:26 :: -2334101314 :: type=1, -10:30, is_dst=false, HST, local/wall
///   0002: 1933-04-30T12:30:00 :: -1157283000 :: type=2, -09:30, is_dst=true, HDT, local/wall
///   0003: 1933-05-21T21:30:00 :: -1155436200 :: type=1, -10:30, is_dst=false, HST, local/wall
///   0004: 1942-02-09T12:30:00 :: -880198200 :: type=3, -09:30, is_dst=true, HWT, local/wall
///   0005: 1945-08-14T23:00:00 :: -769395600 :: type=4, -09:30, is_dst=true, HPT, ut/std
///   0006: 1945-09-30T11:30:00 :: -765376200 :: type=1, -10:30, is_dst=false, HST, local/wall
///   0007: 1947-06-08T12:30:00 :: -712150200 :: type=5, -10, is_dst=false, HST, local/wall
/// POSIX TIME ZONE STRING
///   HST10
/// ```
///
/// See how type 004 has a ut/std indicator? What the fuck does that mean?
/// All transitions are defined in terms of UTC. I confirmed this with `zdump`:
///
/// ```text
/// $ zdump -v Pacific/Honolulu | rg 1945
/// Pacific/Honolulu  Tue Aug 14 22:59:59 1945 UT = Tue Aug 14 13:29:59 1945 HWT isdst=1 gmtoff=-34200
/// Pacific/Honolulu  Tue Aug 14 23:00:00 1945 UT = Tue Aug 14 13:30:00 1945 HPT isdst=1 gmtoff=-34200
/// Pacific/Honolulu  Sun Sep 30 11:29:59 1945 UT = Sun Sep 30 01:59:59 1945 HPT isdst=1 gmtoff=-34200
/// Pacific/Honolulu  Sun Sep 30 11:30:00 1945 UT = Sun Sep 30 01:00:00 1945 HST isdst=0 gmtoff=-37800
/// ```
///
/// The times match up. All of them. The indicators don't seem to make a
/// difference. I'm clearly missing something.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Indicator {
    LocalWall,
    LocalStandard,
    UTStandard,
}

impl Indicator {
    /// Converts from the shared-but-internal API for use in proc macros.
    pub(crate) const fn from_shared(sh: &shared::TzifIndicator) -> Indicator {
        match *sh {
            shared::TzifIndicator::LocalWall => Indicator::LocalWall,
            shared::TzifIndicator::LocalStandard => Indicator::LocalStandard,
            shared::TzifIndicator::UTStandard => Indicator::UTStandard,
        }
    }
}

impl core::fmt::Display for Indicator {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match *self {
            Indicator::LocalWall => write!(f, "local/wall"),
            Indicator::LocalStandard => write!(f, "local/std"),
            Indicator::UTStandard => write!(f, "ut/std"),
        }
    }
}

/// Does a quick check that returns true if the data might be in TZif format.
///
/// It is possible that this returns true even if the given data is not in TZif
/// format. However, it is impossible for this to return false when the given
/// data is TZif. That is, a false positive is allowed but a false negative is
/// not.
#[cfg(feature = "tzdb-zoneinfo")]
pub(crate) fn is_possibly_tzif(data: &[u8]) -> bool {
    data.starts_with(b"TZif")
}

#[cfg(all(test, feature = "alloc"))]
mod tests {
    use alloc::{string::ToString, vec};

    #[cfg(not(miri))]
    use crate::tz::testdata::TZIF_TEST_FILES;

    use super::*;

    /// This converts TZif data into a human readable format.
    ///
    /// This is useful for debugging (via `./scripts/jiff-debug tzif`), but we
    /// also use it for snapshot testing to make reading the test output at
    /// least *somewhat* comprehensible for humans. Otherwise, one needs to
    /// read and understand Unix timestamps. That ain't going to fly.
    ///
    /// For this to work, we make sure everything in a `Tzif` value is
    /// represented in some way in this output.
    fn tzif_to_human_readable(tzif: &TzifOwned) -> String {
        use std::io::Write;

        let mut out = tabwriter::TabWriter::new(vec![])
            .alignment(tabwriter::Alignment::Left);

        writeln!(out, "TIME ZONE NAME").unwrap();
        writeln!(out, "  {}", tzif.name().unwrap_or("UNNAMED")).unwrap();

        writeln!(out, "TIME ZONE VERSION").unwrap();
        writeln!(out, "  {}", char::try_from(tzif.version).unwrap()).unwrap();

        writeln!(out, "LOCAL TIME TYPES").unwrap();
        for (i, typ) in tzif.types.iter().enumerate() {
            writeln!(
                out,
                "  {i:03}:\toffset={off}\t\
                   designation={desig}\t{dst}\tindicator={ind}",
                off = typ.offset,
                desig = tzif.designation(&typ),
                dst = if typ.is_dst.is_dst() { "dst" } else { "" },
                ind = typ.indicator,
            )
            .unwrap();
        }
        if !tzif.transitions.is_empty() {
            writeln!(out, "TRANSITIONS").unwrap();
            for (i, t) in tzif.transitions.iter().enumerate() {
                let dt = Offset::UTC.to_datetime(t.timestamp);
                let typ = &tzif.types[usize::from(t.type_index)];
                let wall = alloc::format!("{:?}", t.wall.start());
                let ambiguous = match t.wall {
                    TransitionWall::Unambiguous { .. } => {
                        "unambiguous".to_string()
                    }
                    TransitionWall::Gap { end, .. } => {
                        alloc::format!(" gap-until({end:?})")
                    }
                    TransitionWall::Fold { end, .. } => {
                        alloc::format!("fold-until({end:?})")
                    }
                };

                writeln!(
                    out,
                    "  {i:04}:\t{dt:?}Z\tunix={ts}\twall={wall}\t\
                       {ambiguous}\t\
                       type={type_index}\t{off}\t\
                       {desig}\t{dst}",
                    ts = t.timestamp.as_second(),
                    type_index = t.type_index,
                    off = typ.offset,
                    desig = tzif.designation(typ),
                    dst = if typ.is_dst.is_dst() { "dst" } else { "" },
                )
                .unwrap();
            }
        }
        if let Some(ref posix_tz) = tzif.posix_tz {
            writeln!(out, "POSIX TIME ZONE STRING").unwrap();
            writeln!(out, "  {}", posix_tz).unwrap();
        }
        String::from_utf8(out.into_inner().unwrap()).unwrap()
    }

    /// DEBUG COMMAND
    ///
    /// Takes environment variable `JIFF_DEBUG_TZIF_PATH` as input, and treats
    /// the value as a TZif file path. This test will open the file, parse it
    /// as a TZif and then dump debug data about the file in a human readable
    /// plain text format.
    #[cfg(feature = "std")]
    #[test]
    fn debug_tzif() -> anyhow::Result<()> {
        use anyhow::Context;

        let _ = crate::logging::Logger::init();

        const ENV: &str = "JIFF_DEBUG_TZIF_PATH";
        let Some(val) = std::env::var_os(ENV) else { return Ok(()) };
        let Ok(val) = val.into_string() else {
            anyhow::bail!("{ENV} has invalid UTF-8")
        };
        let bytes =
            std::fs::read(&val).with_context(|| alloc::format!("{val:?}"))?;
        let tzif = Tzif::parse(Some(val.to_string()), &bytes)?;
        std::eprint!("{}", tzif_to_human_readable(&tzif));
        Ok(())
    }

    #[cfg(not(miri))]
    #[test]
    fn tzif_parse_v2plus() {
        for tzif_test in TZIF_TEST_FILES {
            insta::assert_snapshot!(
                alloc::format!("{}_v2+", tzif_test.name),
                tzif_to_human_readable(&tzif_test.parse())
            );
        }
    }

    #[cfg(not(miri))]
    #[test]
    fn tzif_parse_v1() {
        for tzif_test in TZIF_TEST_FILES {
            insta::assert_snapshot!(
                alloc::format!("{}_v1", tzif_test.name),
                tzif_to_human_readable(&tzif_test.parse_v1())
            );
        }
    }

    /// This tests walks the /usr/share/zoneinfo directory (if it exists) and
    /// tries to parse every TZif formatted file it can find. We don't really
    /// do much with it other than to ensure we don't panic or return an error.
    /// That is, we check that we can parse each file, but not that we do so
    /// correctly.
    #[cfg(not(miri))]
    #[cfg(feature = "tzdb-zoneinfo")]
    #[cfg(target_os = "linux")]
    #[test]
    fn zoneinfo() {
        const TZDIR: &str = "/usr/share/zoneinfo";

        for result in walkdir::WalkDir::new(TZDIR) {
            // Just skip if we got an error traversing the directory tree.
            // These aren't related to our parsing, so it's some other problem
            // (like the directory not existing).
            let Ok(dent) = result else { continue };
            // This test can take some time in debug mode, so skip parsing
            // some of the less frequently used TZif files.
            let Some(name) = dent.path().to_str() else { continue };
            if name.contains("right/") || name.contains("posix/") {
                continue;
            }
            // Again, skip if we can't read. Not my monkeys, not my circus.
            let Ok(bytes) = std::fs::read(dent.path()) else { continue };
            if !is_possibly_tzif(&bytes) {
                continue;
            }
            let tzname = dent
                .path()
                .strip_prefix(TZDIR)
                .unwrap_or_else(|_| {
                    panic!("all paths in TZDIR have {TZDIR:?} prefix")
                })
                .to_str()
                .expect("all paths to be valid UTF-8")
                .to_string();
            // OK at this point, we're pretty sure `bytes` should be a TZif
            // binary file. So try to parse it and fail the test if it fails.
            if let Err(err) = Tzif::parse(Some(tzname), &bytes) {
                panic!("failed to parse TZif file {:?}: {err}", dent.path());
            }
        }
    }
}
