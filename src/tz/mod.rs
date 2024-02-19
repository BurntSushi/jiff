use alloc::{
    boxed::Box,
    string::{String, ToString},
    sync::Arc,
};

use crate::{
    civil::DateTime,
    error::Error,
    instant::{Instant, TimeScale, Unix},
    span::{Span, TimeDuration},
    util::{
        alloc::MaybeBox,
        rangeint::{RFrom, RInto, TryRFrom},
        t::{self, C},
    },
    zoned::Zoned,
};

use self::{posix::ReasonablePosixTimeZone, tzif::Tzif};

pub use self::{
    db::{db, TimeZoneDatabase},
    offset::{Dst, Offset},
};

mod db;
mod offset;
mod posix;
#[cfg(test)]
pub(crate) mod testdata;
mod tzif;
// See module comment for WIP status. :-(
// mod zic;

// BREADCRUMBS: I guess start building out the tzdb abstraction? Then do
// localtime. And then build out the Zoned type (finally). Also think
// about leap seconds. I guess make tzdb itself an enum. Put BinaryTzdb in
// iana/binary.
//
// I think we need a `TimeZone::id` method in addition to `TimeZone::name`.
// The `id` method is like `name`, but is used for equality. This means we need
// to include the specific revision of the IANA database in use.
//
// But, it doesn't look like there is a reliable way to determine the
// version. macOS has a /usr/share/zoneinfo/+VERSION file. And my Archlinux
// installation puts the version in a comment at the top of tzdata.zi. But...
// that's it. Wow. Frustrating.
//
// I suppose the "version" can just be the path to the database on disk?
//
// The reason for this is that we want some notion of time zone equality so
// that we can return errors when computing durations between Zoned values in
// different time zones.
//
// But wait, our duration routines don't do any rounding and just return
// seconds. Which is always okay. The problem occurs when rounding a duration
// relative to a Zoned value, but we only ever do it with respect to a single
// zoned value. So there is less ambiguity than in Temporal's APIs I think. So
// maybe we don't need time zone equality as much as we think? Still, it's
// probably good to have...
//
// No, actually, what about computing spans between two Zoned values? What do
// we do when different time zones are used?
//
// Another thought is to compute a hash/checksum and use that to determine
// equality. Hmmm.

#[derive(Clone)]
pub struct TimeZone {
    kind: Option<Arc<TimeZoneKind>>,
}

impl TimeZone {
    pub const UTC: TimeZone = TimeZone { kind: None };

    pub fn fixed(offset: Offset) -> TimeZone {
        if offset == Offset::UTC {
            return TimeZone::UTC;
        }
        let fixed = TimeZoneFixed::new(offset);
        let kind = TimeZoneKind::Fixed(fixed);
        TimeZone { kind: Some(Arc::new(kind)) }
    }

    pub fn posix(posix_tz_string: &str) -> Result<TimeZone, Error> {
        let posix = TimeZonePosix::new(posix_tz_string)?;
        let kind = TimeZoneKind::Posix(posix);
        Ok(TimeZone { kind: Some(Arc::new(kind)) })
    }

    pub fn tzif(name: &str, data: &[u8]) -> Result<TimeZone, Error> {
        let tzif = TimeZoneTzif::new(name, data)?;
        let kind = TimeZoneKind::Tzif(tzif);
        Ok(TimeZone { kind: Some(Arc::new(kind)) })
    }

    pub fn name(&self) -> &str {
        let Some(ref kind) = self.kind else { return "UTC" };
        match **kind {
            TimeZoneKind::Fixed(ref tz) => tz.name(),
            TimeZoneKind::Posix(ref tz) => tz.name(),
            TimeZoneKind::Tzif(ref tz) => tz.name(),
        }
    }

    pub fn iana_name(&self) -> Option<&str> {
        let Some(ref kind) = self.kind else { return Some("UTC") };
        match **kind {
            TimeZoneKind::Tzif(ref tz) => Some(tz.name()),
            _ => None,
        }
    }

    pub fn to_datetime<S: TimeScale>(&self, instant: Instant<S>) -> DateTime {
        let (offset, _, _) = self.to_offset(instant);
        offset.to_datetime(instant)
    }

    pub fn to_offset<S: TimeScale>(
        &self,
        instant: Instant<S>,
    ) -> (Offset, Dst, &str) {
        let Some(ref kind) = self.kind else {
            return (Offset::UTC, Dst::No, "UTC");
        };
        match **kind {
            TimeZoneKind::Fixed(ref tz) => (tz.offset(), Dst::No, tz.name()),
            TimeZoneKind::Posix(ref tz) => tz.to_offset(instant),
            TimeZoneKind::Tzif(ref tz) => tz.to_offset(instant),
        }
    }

    pub fn to_zoned(&self, dt: DateTime) -> Result<Zoned, Error> {
        self.to_zoned_with_scale(dt)
    }

    pub fn to_zoned_with_scale<S: TimeScale>(
        &self,
        dt: DateTime,
    ) -> Result<Zoned<S>, Error> {
        self.to_ambiguous_instant(dt).compatible_with_scale()
    }

    pub(crate) fn to_instant(&self, dt: DateTime) -> Result<Instant, Error> {
        self.to_zoned(dt).map(|zdt| zdt.to_instant())
    }

    pub(crate) fn to_instant_with_scale<S: TimeScale>(
        &self,
        dt: DateTime,
    ) -> Result<Instant<S>, Error> {
        self.to_zoned_with_scale(dt).map(|zdt| zdt.to_instant())
    }

    pub fn to_ambiguous_instant(&self, dt: DateTime) -> AmbiguousInstant {
        let ambiguous_kind = match self.kind {
            None => AmbiguousInstantKind::Unambiguous { offset: Offset::UTC },
            Some(ref kind) => match **kind {
                TimeZoneKind::Fixed(ref tz) => {
                    AmbiguousInstantKind::Unambiguous { offset: tz.offset() }
                }
                TimeZoneKind::Posix(ref tz) => {
                    tz.to_ambiguous_instant_kind(dt)
                }
                TimeZoneKind::Tzif(ref tz) => tz.to_ambiguous_instant_kind(dt),
            },
        };
        AmbiguousInstant::new(self.clone(), dt, ambiguous_kind)
    }

    fn fixed_offset(&self) -> Option<Offset> {
        let Some(ref kind) = self.kind else { return Some(Offset::UTC) };
        match **kind {
            TimeZoneKind::Fixed(ref tz) => Some(tz.offset),
            _ => None,
        }
    }
}

impl core::fmt::Debug for TimeZone {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        let field: &dyn core::fmt::Debug = match self.kind {
            None => &"UTC",
            Some(ref kind) => match &**kind {
                TimeZoneKind::Fixed(ref tz) => tz,
                TimeZoneKind::Posix(ref tz) => tz,
                TimeZoneKind::Tzif(ref tz) => tz,
            },
        };
        f.debug_tuple("TimeZone").field(field).finish()
    }
}

impl Eq for TimeZone {}

/// When two time zones are equal, they are guaranteed to produce the same
/// offsets in all cases.
///
/// The inverse is not necessarily true. That is, it may be the case that
/// two time zones `tz1` and `tz2` produce the same offsets in all cases but
/// do _not_ compare equal.
///
/// The primary reason for why equality is defined this way is that it
/// is impractical to do a true time zone comparison. Moreover, even if
/// two different time zones are equivalent in every way, they may be
/// geo-politically distinct.
///
/// TODO: Show an example here with a tzdb's cache being updated and that
/// resulting in two otherwise equivalent time zones comparing unequal.
impl PartialEq for TimeZone {
    fn eq(&self, rhs: &TimeZone) -> bool {
        use self::TimeZoneKind::*;

        match (self.fixed_offset(), rhs.fixed_offset()) {
            (Some(off1), Some(off2)) => return off1 == off2,
            (None, Some(_)) => return false,
            (Some(_), None) => return false,
            _ => {}
        }
        Arc::ptr_eq(self.kind.as_ref().unwrap(), rhs.kind.as_ref().unwrap())
    }
}

#[derive(Debug)]
enum TimeZoneKind {
    Fixed(TimeZoneFixed),
    Posix(TimeZonePosix),
    Tzif(TimeZoneTzif),
}

#[derive(Clone)]
struct TimeZoneFixed {
    offset: Offset,
    name: Box<str>,
}

impl TimeZoneFixed {
    fn new(offset: Offset) -> TimeZoneFixed {
        let name = offset.to_string().into();
        TimeZoneFixed { offset, name }
    }

    fn name(&self) -> &str {
        &self.name
    }

    fn offset(&self) -> Offset {
        self.offset
    }
}

impl core::fmt::Debug for TimeZoneFixed {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_tuple("Fixed").field(&self.offset()).finish()
    }
}

struct TimeZonePosix {
    name: Box<str>,
    posix: ReasonablePosixTimeZone,
}

impl TimeZonePosix {
    fn new(s: &str) -> Result<TimeZonePosix, Error> {
        let name: Box<str> = s.to_string().into();
        let iana_tz = posix::IanaTz::parse_v3plus(&*name)?;
        Ok(TimeZonePosix { name, posix: iana_tz.into_tz() })
    }

    fn name(&self) -> &str {
        &self.name
    }

    fn to_offset<S: TimeScale>(
        &self,
        instant: Instant<S>,
    ) -> (Offset, Dst, &str) {
        self.posix.to_offset(instant)
    }

    fn to_ambiguous_instant_kind(&self, dt: DateTime) -> AmbiguousInstantKind {
        self.posix.to_ambiguous_instant_kind(dt)
    }
}

// This is implemented by hand because dumping out the full representation of
// a `ReasonablePosixTimeZone` is way too much noise for users of Jiff.
impl core::fmt::Debug for TimeZonePosix {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_tuple("Posix").field(&self.posix.as_str()).finish()
    }
}

struct TimeZoneTzif {
    tzif: Tzif,
}

impl TimeZoneTzif {
    fn new(
        name: impl Into<String>,
        bytes: &[u8],
    ) -> Result<TimeZoneTzif, Error> {
        let tzif = Tzif::parse(name, bytes)?;
        Ok(TimeZoneTzif { tzif })
    }

    fn name(&self) -> &str {
        self.tzif.name()
    }

    fn to_offset<S: TimeScale>(
        &self,
        instant: Instant<S>,
    ) -> (Offset, Dst, &str) {
        self.tzif.to_offset(instant)
    }

    fn to_ambiguous_instant_kind(&self, dt: DateTime) -> AmbiguousInstantKind {
        self.tzif.to_ambiguous_instant_kind(dt)
    }
}

// This is implemented by hand because dumping out the full representation of
// all TZif data is too much noise for users of Jiff.
impl core::fmt::Debug for TimeZoneTzif {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_tuple("Tzif").field(&self.name()).finish()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AmbiguousInstant {
    tz: TimeZone,
    dt: DateTime,
    kind: AmbiguousInstantKind,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AmbiguousInstantKind {
    /// The offset for a particular civil datetime and time zone is
    /// unambiguous.
    ///
    /// This is the overwhelmingly common case. In general, the only time this
    /// case does not occur is when there is a transition to a different time
    /// zone (rare) or to/from daylight savings time (occurs for 1 hour twice
    /// in year in many geographic locations).
    Unambiguous {
        /// The offset from UTC for the corresponding civil datetime given. The
        /// offset is determined via the relevant time zone data, and in this
        /// case, there is only one possible offset that could be applied to
        /// the given civil datetime.
        offset: Offset,
    },
    /// The offset for a particular civil datetime and time zone is ambiguous
    /// because there is a gap.
    ///
    /// This most commonly occurs when a civil datetime corresponds to an hour
    /// that was "skipped" in a jump to DST (daylight savings time).
    Gap {
        /// The offset corresponding to the time before a gap.
        ///
        /// For example, given a time zone of `America/Los_Angeles`, the offset
        /// for time immediately preceding `2020-03-08T02:00:00` is `-08`.
        before: Offset,
        /// The offset corresponding to the later time in a gap.
        ///
        /// For example, given a time zone of `America/Los_Angeles`, the offset
        /// for time immediately following `2020-03-08T02:59:59` is `-07`.
        after: Offset,
    },
    /// The offset for a particular civil datetime and time zone is ambiguous
    /// because there is a fold.
    ///
    /// This most commonly occurs when a civil datetime corresponds to an hour
    /// that was "repeated" in a jump to standard time from DST (daylight
    /// savings time).
    Fold {
        /// The offset corresponding to the earlier time in a fold.
        ///
        /// For example, given a time zone of `America/Los_Angeles`, the offset
        /// for time on the first `2020-11-01T01:00:00` is `-07`.
        before: Offset,
        /// The offset corresponding to the earlier time in a fold.
        ///
        /// For example, given a time zone of `America/Los_Angeles`, the offset
        /// for time on the second `2020-11-01T01:00:00` is `-07`.
        after: Offset,
    },
}

impl AmbiguousInstant {
    pub fn new(
        tz: TimeZone,
        dt: DateTime,
        kind: AmbiguousInstantKind,
    ) -> AmbiguousInstant {
        AmbiguousInstant { dt, tz, kind }
    }

    pub fn time_zone(&self) -> &TimeZone {
        &self.tz
    }

    pub fn datetime(&self) -> DateTime {
        self.dt
    }

    pub fn kind(&self) -> &AmbiguousInstantKind {
        &self.kind
    }

    pub fn compatible(self) -> Result<Zoned, Error> {
        self.compatible_with_scale()
    }

    pub fn earlier(self) -> Result<Zoned, Error> {
        self.earlier_with_scale()
    }

    pub fn later(self) -> Result<Zoned, Error> {
        self.later_with_scale()
    }

    pub fn unambiguous(self) -> Result<Zoned, Error> {
        self.unambiguous_with_scale()
    }

    pub fn compatible_with_scale<S: TimeScale>(
        self,
    ) -> Result<Zoned<S>, Error> {
        let offset = match *self.kind() {
            AmbiguousInstantKind::Unambiguous { offset } => offset,
            AmbiguousInstantKind::Gap { before, .. } => before,
            AmbiguousInstantKind::Fold { before, .. } => before,
        };
        offset
            .to_instant_with_scale(self.dt)
            .map(|instant| Zoned::new(instant, self.tz))
    }

    pub fn earlier_with_scale<S: TimeScale>(self) -> Result<Zoned<S>, Error> {
        let offset = match *self.kind() {
            AmbiguousInstantKind::Unambiguous { offset } => offset,
            AmbiguousInstantKind::Gap { after, .. } => after,
            AmbiguousInstantKind::Fold { before, .. } => before,
        };
        offset
            .to_instant_with_scale(self.dt)
            .map(|instant| Zoned::new(instant, self.tz))
    }

    pub fn later_with_scale<S: TimeScale>(self) -> Result<Zoned<S>, Error> {
        let offset = match *self.kind() {
            AmbiguousInstantKind::Unambiguous { offset } => offset,
            AmbiguousInstantKind::Gap { before, .. } => before,
            AmbiguousInstantKind::Fold { after, .. } => after,
        };
        offset
            .to_instant_with_scale(self.dt)
            .map(|instant| Zoned::new(instant, self.tz))
    }

    pub fn unambiguous_with_scale<S: TimeScale>(
        self,
    ) -> Result<Zoned<S>, Error> {
        let offset = match *self.kind() {
            AmbiguousInstantKind::Unambiguous { offset } => offset,
            AmbiguousInstantKind::Gap { before, after } => {
                return Err(Error::ambiguous_gap(
                    self.tz, self.dt, before, after,
                ));
            }
            AmbiguousInstantKind::Fold { before, after } => {
                return Err(Error::ambiguous_fold(
                    self.tz, self.dt, before, after,
                ));
            }
        };
        offset
            .to_instant_with_scale(self.dt)
            .map(|instant| Zoned::new(instant, self.tz))
    }

    pub fn is_ambiguous(&self) -> bool {
        !matches!(*self.kind(), AmbiguousInstantKind::Unambiguous { .. })
    }
}

#[cfg(test)]
mod tests {
    use crate::tz::testdata::TzifTestFile;

    use super::*;

    fn unambiguous(offset_hours: i8) -> AmbiguousInstantKind {
        let offset = Offset::constant(offset_hours);
        o_unambiguous(offset)
    }

    fn gap(
        earlier_offset_hours: i8,
        later_offset_hours: i8,
    ) -> AmbiguousInstantKind {
        let earlier = Offset::constant(earlier_offset_hours);
        let later = Offset::constant(later_offset_hours);
        o_gap(earlier, later)
    }

    fn fold(
        earlier_offset_hours: i8,
        later_offset_hours: i8,
    ) -> AmbiguousInstantKind {
        let earlier = Offset::constant(earlier_offset_hours);
        let later = Offset::constant(later_offset_hours);
        o_fold(earlier, later)
    }

    fn o_unambiguous(offset: Offset) -> AmbiguousInstantKind {
        AmbiguousInstantKind::Unambiguous { offset }
    }

    fn o_gap(earlier: Offset, later: Offset) -> AmbiguousInstantKind {
        AmbiguousInstantKind::Gap { before: earlier, after: later }
    }

    fn o_fold(earlier: Offset, later: Offset) -> AmbiguousInstantKind {
        AmbiguousInstantKind::Fold { before: earlier, after: later }
    }

    #[test]
    fn time_zone_tzif_to_ambiguous_instant() {
        let tests: &[(&str, &[_])] = &[
            (
                "America/New_York",
                &[
                    ((1969, 12, 31, 19, 0, 0, 0), unambiguous(-5)),
                    ((2024, 3, 10, 1, 59, 59, 999_999_999), unambiguous(-5)),
                    ((2024, 3, 10, 2, 0, 0, 0), gap(-5, -4)),
                    ((2024, 3, 10, 2, 59, 59, 999_999_999), gap(-5, -4)),
                    ((2024, 3, 10, 3, 0, 0, 0), unambiguous(-4)),
                    ((2024, 11, 3, 0, 59, 59, 999_999_999), unambiguous(-4)),
                    ((2024, 11, 3, 1, 0, 0, 0), fold(-4, -5)),
                    ((2024, 11, 3, 1, 59, 59, 999_999_999), fold(-4, -5)),
                    ((2024, 11, 3, 2, 0, 0, 0), unambiguous(-5)),
                ],
            ),
            (
                "Europe/Dublin",
                &[
                    ((1970, 1, 1, 0, 0, 0, 0), unambiguous(1)),
                    ((2024, 3, 31, 0, 59, 59, 999_999_999), unambiguous(0)),
                    ((2024, 3, 31, 1, 0, 0, 0), gap(0, 1)),
                    ((2024, 3, 31, 1, 59, 59, 999_999_999), gap(0, 1)),
                    ((2024, 3, 31, 2, 0, 0, 0), unambiguous(1)),
                    ((2024, 10, 27, 0, 59, 59, 999_999_999), unambiguous(1)),
                    ((2024, 10, 27, 1, 0, 0, 0), fold(1, 0)),
                    ((2024, 10, 27, 1, 59, 59, 999_999_999), fold(1, 0)),
                    ((2024, 10, 27, 2, 0, 0, 0), unambiguous(0)),
                ],
            ),
            (
                "Australia/Tasmania",
                &[
                    ((1970, 1, 1, 11, 0, 0, 0), unambiguous(11)),
                    ((2024, 4, 7, 1, 59, 59, 999_999_999), unambiguous(11)),
                    ((2024, 4, 7, 2, 0, 0, 0), fold(11, 10)),
                    ((2024, 4, 7, 2, 59, 59, 999_999_999), fold(11, 10)),
                    ((2024, 4, 7, 3, 0, 0, 0), unambiguous(10)),
                    ((2024, 10, 6, 1, 59, 59, 999_999_999), unambiguous(10)),
                    ((2024, 10, 6, 2, 0, 0, 0), gap(10, 11)),
                    ((2024, 10, 6, 2, 59, 59, 999_999_999), gap(10, 11)),
                    ((2024, 10, 6, 3, 0, 0, 0), unambiguous(11)),
                ],
            ),
            (
                "Antarctica/Troll",
                &[
                    ((1970, 1, 1, 0, 0, 0, 0), unambiguous(0)),
                    // test the gap
                    ((2024, 3, 31, 0, 59, 59, 999_999_999), unambiguous(0)),
                    ((2024, 3, 31, 1, 0, 0, 0), gap(0, 2)),
                    ((2024, 3, 31, 1, 59, 59, 999_999_999), gap(0, 2)),
                    // still in the gap!
                    ((2024, 3, 31, 2, 0, 0, 0), gap(0, 2)),
                    ((2024, 3, 31, 2, 59, 59, 999_999_999), gap(0, 2)),
                    // finally out
                    ((2024, 3, 31, 3, 0, 0, 0), unambiguous(2)),
                    // test the fold
                    ((2024, 10, 27, 0, 59, 59, 999_999_999), unambiguous(2)),
                    ((2024, 10, 27, 1, 0, 0, 0), fold(2, 0)),
                    ((2024, 10, 27, 1, 59, 59, 999_999_999), fold(2, 0)),
                    // still in the fold!
                    ((2024, 10, 27, 2, 0, 0, 0), fold(2, 0)),
                    ((2024, 10, 27, 2, 59, 59, 999_999_999), fold(2, 0)),
                    // finally out
                    ((2024, 10, 27, 3, 0, 0, 0), unambiguous(0)),
                ],
            ),
            (
                "America/St_Johns",
                &[
                    (
                        (1969, 12, 31, 20, 30, 0, 0),
                        o_unambiguous(-Offset::hms(3, 30, 0)),
                    ),
                    (
                        (2024, 3, 10, 1, 59, 59, 999_999_999),
                        o_unambiguous(-Offset::hms(3, 30, 0)),
                    ),
                    (
                        (2024, 3, 10, 2, 0, 0, 0),
                        o_gap(-Offset::hms(3, 30, 0), -Offset::hms(2, 30, 0)),
                    ),
                    (
                        (2024, 3, 10, 2, 59, 59, 999_999_999),
                        o_gap(-Offset::hms(3, 30, 0), -Offset::hms(2, 30, 0)),
                    ),
                    (
                        (2024, 3, 10, 3, 0, 0, 0),
                        o_unambiguous(-Offset::hms(2, 30, 0)),
                    ),
                    (
                        (2024, 11, 3, 0, 59, 59, 999_999_999),
                        o_unambiguous(-Offset::hms(2, 30, 0)),
                    ),
                    (
                        (2024, 11, 3, 1, 0, 0, 0),
                        o_fold(-Offset::hms(2, 30, 0), -Offset::hms(3, 30, 0)),
                    ),
                    (
                        (2024, 11, 3, 1, 59, 59, 999_999_999),
                        o_fold(-Offset::hms(2, 30, 0), -Offset::hms(3, 30, 0)),
                    ),
                    (
                        (2024, 11, 3, 2, 0, 0, 0),
                        o_unambiguous(-Offset::hms(3, 30, 0)),
                    ),
                ],
            ),
            // This time zone has an interesting transition where it jumps
            // backwards a full day at 1867-10-19T15:30:00.
            (
                "America/Sitka",
                &[
                    ((1969, 12, 31, 16, 0, 0, 0), unambiguous(-8)),
                    (
                        (-9999, 1, 2, 16, 58, 46, 0),
                        o_unambiguous(Offset::hms(14, 58, 47)),
                    ),
                    (
                        (1867, 10, 18, 15, 29, 59, 0),
                        o_unambiguous(Offset::hms(14, 58, 47)),
                    ),
                    (
                        (1867, 10, 18, 15, 30, 0, 0),
                        // A fold of 24 hours!!!
                        o_fold(
                            Offset::hms(14, 58, 47),
                            -Offset::hms(9, 1, 13),
                        ),
                    ),
                    (
                        (1867, 10, 19, 15, 29, 59, 999_999_999),
                        // Still in the fold...
                        o_fold(
                            Offset::hms(14, 58, 47),
                            -Offset::hms(9, 1, 13),
                        ),
                    ),
                    (
                        (1867, 10, 19, 15, 30, 0, 0),
                        // Finally out.
                        o_unambiguous(-Offset::hms(9, 1, 13)),
                    ),
                ],
            ),
            // As with to_datetime, we test every possible transition
            // point here since this time zone has a small number of them.
            (
                "Pacific/Honolulu",
                &[
                    (
                        (1896, 1, 13, 11, 59, 59, 0),
                        o_unambiguous(-Offset::hms(10, 31, 26)),
                    ),
                    (
                        (1896, 1, 13, 12, 0, 0, 0),
                        o_gap(
                            -Offset::hms(10, 31, 26),
                            -Offset::hms(10, 30, 0),
                        ),
                    ),
                    (
                        (1896, 1, 13, 12, 1, 25, 0),
                        o_gap(
                            -Offset::hms(10, 31, 26),
                            -Offset::hms(10, 30, 0),
                        ),
                    ),
                    (
                        (1896, 1, 13, 12, 1, 26, 0),
                        o_unambiguous(-Offset::hms(10, 30, 0)),
                    ),
                    (
                        (1933, 4, 30, 1, 59, 59, 0),
                        o_unambiguous(-Offset::hms(10, 30, 0)),
                    ),
                    (
                        (1933, 4, 30, 2, 0, 0, 0),
                        o_gap(-Offset::hms(10, 30, 0), -Offset::hms(9, 30, 0)),
                    ),
                    (
                        (1933, 4, 30, 2, 59, 59, 0),
                        o_gap(-Offset::hms(10, 30, 0), -Offset::hms(9, 30, 0)),
                    ),
                    (
                        (1933, 4, 30, 3, 0, 0, 0),
                        o_unambiguous(-Offset::hms(9, 30, 0)),
                    ),
                    (
                        (1933, 5, 21, 10, 59, 59, 0),
                        o_unambiguous(-Offset::hms(9, 30, 0)),
                    ),
                    (
                        (1933, 5, 21, 11, 0, 0, 0),
                        o_fold(
                            -Offset::hms(9, 30, 0),
                            -Offset::hms(10, 30, 0),
                        ),
                    ),
                    (
                        (1933, 5, 21, 11, 59, 59, 0),
                        o_fold(
                            -Offset::hms(9, 30, 0),
                            -Offset::hms(10, 30, 0),
                        ),
                    ),
                    (
                        (1933, 5, 21, 12, 0, 0, 0),
                        o_unambiguous(-Offset::hms(10, 30, 0)),
                    ),
                    (
                        (1942, 2, 9, 1, 59, 59, 0),
                        o_unambiguous(-Offset::hms(10, 30, 0)),
                    ),
                    (
                        (1942, 2, 9, 2, 0, 0, 0),
                        o_gap(-Offset::hms(10, 30, 0), -Offset::hms(9, 30, 0)),
                    ),
                    (
                        (1942, 2, 9, 2, 59, 59, 0),
                        o_gap(-Offset::hms(10, 30, 0), -Offset::hms(9, 30, 0)),
                    ),
                    (
                        (1942, 2, 9, 3, 0, 0, 0),
                        o_unambiguous(-Offset::hms(9, 30, 0)),
                    ),
                    (
                        (1945, 8, 14, 13, 29, 59, 0),
                        o_unambiguous(-Offset::hms(9, 30, 0)),
                    ),
                    (
                        (1945, 8, 14, 13, 30, 0, 0),
                        o_unambiguous(-Offset::hms(9, 30, 0)),
                    ),
                    (
                        (1945, 8, 14, 13, 30, 1, 0),
                        o_unambiguous(-Offset::hms(9, 30, 0)),
                    ),
                    (
                        (1945, 9, 30, 0, 59, 59, 0),
                        o_unambiguous(-Offset::hms(9, 30, 0)),
                    ),
                    (
                        (1945, 9, 30, 1, 0, 0, 0),
                        o_fold(
                            -Offset::hms(9, 30, 0),
                            -Offset::hms(10, 30, 0),
                        ),
                    ),
                    (
                        (1945, 9, 30, 1, 59, 59, 0),
                        o_fold(
                            -Offset::hms(9, 30, 0),
                            -Offset::hms(10, 30, 0),
                        ),
                    ),
                    (
                        (1945, 9, 30, 2, 0, 0, 0),
                        o_unambiguous(-Offset::hms(10, 30, 0)),
                    ),
                    (
                        (1947, 6, 8, 1, 59, 59, 0),
                        o_unambiguous(-Offset::hms(10, 30, 0)),
                    ),
                    (
                        (1947, 6, 8, 2, 0, 0, 0),
                        o_gap(-Offset::hms(10, 30, 0), -Offset::constant(10)),
                    ),
                    (
                        (1947, 6, 8, 2, 29, 59, 0),
                        o_gap(-Offset::hms(10, 30, 0), -Offset::constant(10)),
                    ),
                    ((1947, 6, 8, 2, 30, 0, 0), unambiguous(-10)),
                ],
            ),
        ];
        for &(tzname, datetimes_to_ambiguous) in tests {
            let test_file = TzifTestFile::get(tzname);
            let tz = TimeZone::tzif(test_file.name, test_file.data).unwrap();
            for &(datetime, ref ambiguous_kind) in datetimes_to_ambiguous {
                let (year, month, day, hour, min, sec, nano) = datetime;
                let dt =
                    DateTime::constant(year, month, day, hour, min, sec, nano);
                let got = tz.to_ambiguous_instant(dt);
                assert_eq!(
                    got.kind(),
                    ambiguous_kind,
                    "\nTZ: {tzname}\ndatetime: \
                     {year:04}-{month:02}-{day:02}T\
                     {hour:02}:{min:02}:{sec:02}.{nano:09}",
                );
            }
        }
    }

    #[test]
    fn time_zone_tzif_to_datetime() {
        let o = |hours| Offset::constant(hours);
        let tests: &[(&str, &[_])] = &[
            (
                "America/New_York",
                &[
                    ((0, 0), o(-5), "EST", (1969, 12, 31, 19, 0, 0, 0)),
                    (
                        (1710052200, 0),
                        o(-5),
                        "EST",
                        (2024, 3, 10, 1, 30, 0, 0),
                    ),
                    (
                        (1710053999, 999_999_999),
                        o(-5),
                        "EST",
                        (2024, 3, 10, 1, 59, 59, 999_999_999),
                    ),
                    ((1710054000, 0), o(-4), "EDT", (2024, 3, 10, 3, 0, 0, 0)),
                    (
                        (1710055800, 0),
                        o(-4),
                        "EDT",
                        (2024, 3, 10, 3, 30, 0, 0),
                    ),
                    ((1730610000, 0), o(-4), "EDT", (2024, 11, 3, 1, 0, 0, 0)),
                    (
                        (1730611800, 0),
                        o(-4),
                        "EDT",
                        (2024, 11, 3, 1, 30, 0, 0),
                    ),
                    (
                        (1730613599, 999_999_999),
                        o(-4),
                        "EDT",
                        (2024, 11, 3, 1, 59, 59, 999_999_999),
                    ),
                    ((1730613600, 0), o(-5), "EST", (2024, 11, 3, 1, 0, 0, 0)),
                    (
                        (1730615400, 0),
                        o(-5),
                        "EST",
                        (2024, 11, 3, 1, 30, 0, 0),
                    ),
                ],
            ),
            (
                "Australia/Tasmania",
                &[
                    ((0, 0), o(11), "AEDT", (1970, 1, 1, 11, 0, 0, 0)),
                    (
                        (1728142200, 0),
                        o(10),
                        "AEST",
                        (2024, 10, 6, 1, 30, 0, 0),
                    ),
                    (
                        (1728143999, 999_999_999),
                        o(10),
                        "AEST",
                        (2024, 10, 6, 1, 59, 59, 999_999_999),
                    ),
                    (
                        (1728144000, 0),
                        o(11),
                        "AEDT",
                        (2024, 10, 6, 3, 0, 0, 0),
                    ),
                    (
                        (1728145800, 0),
                        o(11),
                        "AEDT",
                        (2024, 10, 6, 3, 30, 0, 0),
                    ),
                    ((1712415600, 0), o(11), "AEDT", (2024, 4, 7, 2, 0, 0, 0)),
                    (
                        (1712417400, 0),
                        o(11),
                        "AEDT",
                        (2024, 4, 7, 2, 30, 0, 0),
                    ),
                    (
                        (1712419199, 999_999_999),
                        o(11),
                        "AEDT",
                        (2024, 4, 7, 2, 59, 59, 999_999_999),
                    ),
                    ((1712419200, 0), o(10), "AEST", (2024, 4, 7, 2, 0, 0, 0)),
                    (
                        (1712421000, 0),
                        o(10),
                        "AEST",
                        (2024, 4, 7, 2, 30, 0, 0),
                    ),
                ],
            ),
            // Pacific/Honolulu is small eough that we just test every
            // possible instant before, at and after each transition.
            (
                "Pacific/Honolulu",
                &[
                    (
                        (-2334101315, 0),
                        -Offset::hms(10, 31, 26),
                        "LMT",
                        (1896, 1, 13, 11, 59, 59, 0),
                    ),
                    (
                        (-2334101314, 0),
                        -Offset::hms(10, 30, 0),
                        "HST",
                        (1896, 1, 13, 12, 1, 26, 0),
                    ),
                    (
                        (-2334101313, 0),
                        -Offset::hms(10, 30, 0),
                        "HST",
                        (1896, 1, 13, 12, 1, 27, 0),
                    ),
                    (
                        (-1157283001, 0),
                        -Offset::hms(10, 30, 0),
                        "HST",
                        (1933, 4, 30, 1, 59, 59, 0),
                    ),
                    (
                        (-1157283000, 0),
                        -Offset::hms(9, 30, 0),
                        "HDT",
                        (1933, 4, 30, 3, 0, 0, 0),
                    ),
                    (
                        (-1157282999, 0),
                        -Offset::hms(9, 30, 0),
                        "HDT",
                        (1933, 4, 30, 3, 0, 1, 0),
                    ),
                    (
                        (-1155436201, 0),
                        -Offset::hms(9, 30, 0),
                        "HDT",
                        (1933, 5, 21, 11, 59, 59, 0),
                    ),
                    (
                        (-1155436200, 0),
                        -Offset::hms(10, 30, 0),
                        "HST",
                        (1933, 5, 21, 11, 0, 0, 0),
                    ),
                    (
                        (-1155436199, 0),
                        -Offset::hms(10, 30, 0),
                        "HST",
                        (1933, 5, 21, 11, 0, 1, 0),
                    ),
                    (
                        (-880198201, 0),
                        -Offset::hms(10, 30, 0),
                        "HST",
                        (1942, 2, 9, 1, 59, 59, 0),
                    ),
                    (
                        (-880198200, 0),
                        -Offset::hms(9, 30, 0),
                        "HWT",
                        (1942, 2, 9, 3, 0, 0, 0),
                    ),
                    (
                        (-880198199, 0),
                        -Offset::hms(9, 30, 0),
                        "HWT",
                        (1942, 2, 9, 3, 0, 1, 0),
                    ),
                    (
                        (-769395601, 0),
                        -Offset::hms(9, 30, 0),
                        "HWT",
                        (1945, 8, 14, 13, 29, 59, 0),
                    ),
                    (
                        (-769395600, 0),
                        -Offset::hms(9, 30, 0),
                        "HPT",
                        (1945, 8, 14, 13, 30, 0, 0),
                    ),
                    (
                        (-769395599, 0),
                        -Offset::hms(9, 30, 0),
                        "HPT",
                        (1945, 8, 14, 13, 30, 1, 0),
                    ),
                    (
                        (-765376201, 0),
                        -Offset::hms(9, 30, 0),
                        "HPT",
                        (1945, 9, 30, 1, 59, 59, 0),
                    ),
                    (
                        (-765376200, 0),
                        -Offset::hms(10, 30, 0),
                        "HST",
                        (1945, 9, 30, 1, 0, 0, 0),
                    ),
                    (
                        (-765376199, 0),
                        -Offset::hms(10, 30, 0),
                        "HST",
                        (1945, 9, 30, 1, 0, 1, 0),
                    ),
                    (
                        (-712150201, 0),
                        -Offset::hms(10, 30, 0),
                        "HST",
                        (1947, 6, 8, 1, 59, 59, 0),
                    ),
                    // At this point, we hit the last transition and the POSIX
                    // TZ string takes over.
                    (
                        (-712150200, 0),
                        -Offset::hms(10, 0, 0),
                        "HST",
                        (1947, 6, 8, 2, 30, 0, 0),
                    ),
                    (
                        (-712150199, 0),
                        -Offset::hms(10, 0, 0),
                        "HST",
                        (1947, 6, 8, 2, 30, 1, 0),
                    ),
                ],
            ),
            // This time zone has an interesting transition where it jumps
            // backwards a full day at 1867-10-19T15:30:00.
            (
                "America/Sitka",
                &[
                    ((0, 0), o(-8), "PST", (1969, 12, 31, 16, 0, 0, 0)),
                    (
                        (-377705023201, 0),
                        Offset::hms(14, 58, 47),
                        "LMT",
                        (-9999, 1, 2, 16, 58, 46, 0),
                    ),
                    (
                        (-3225223728, 0),
                        Offset::hms(14, 58, 47),
                        "LMT",
                        (1867, 10, 19, 15, 29, 59, 0),
                    ),
                    // Notice the 24 hour time jump backwards a whole day!
                    (
                        (-3225223727, 0),
                        -Offset::hms(9, 1, 13),
                        "LMT",
                        (1867, 10, 18, 15, 30, 0, 0),
                    ),
                    (
                        (-3225223726, 0),
                        -Offset::hms(9, 1, 13),
                        "LMT",
                        (1867, 10, 18, 15, 30, 1, 0),
                    ),
                ],
            ),
        ];
        for &(tzname, instants_to_datetimes) in tests {
            let test_file = TzifTestFile::get(tzname);
            let tz = TimeZone::tzif(test_file.name, test_file.data).unwrap();
            for &((unix_sec, unix_nano), offset, abbrev, datetime) in
                instants_to_datetimes
            {
                let (year, month, day, hour, min, sec, nano) = datetime;
                let instant = Instant::from_unix(unix_sec, unix_nano).unwrap();
                let (got_offset, _, got_abbrev) = tz.to_offset(instant);
                assert_eq!(
                    got_offset, offset,
                    "\nTZ={tzname}, timestamp({unix_sec}, {unix_nano})",
                );
                assert_eq!(
                    got_abbrev, abbrev,
                    "\nTZ={tzname}, timestamp({unix_sec}, {unix_nano})",
                );
                assert_eq!(
                    got_offset.to_datetime(instant),
                    DateTime::constant(year, month, day, hour, min, sec, nano),
                    "\nTZ={tzname}, timestamp({unix_sec}, {unix_nano})",
                );
            }
        }
    }

    #[test]
    fn time_zone_posix_to_ambiguous_instant() {
        let tests: &[(&str, &[_])] = &[
            // America/New_York, but a utopia in which DST is abolished.
            (
                "EST5",
                &[
                    ((1969, 12, 31, 19, 0, 0, 0), unambiguous(-5)),
                    ((2024, 3, 10, 2, 0, 0, 0), unambiguous(-5)),
                ],
            ),
            // The standard DST rule for America/New_York.
            (
                "EST5EDT,M3.2.0,M11.1.0",
                &[
                    ((1969, 12, 31, 19, 0, 0, 0), unambiguous(-5)),
                    ((2024, 3, 10, 1, 59, 59, 999_999_999), unambiguous(-5)),
                    ((2024, 3, 10, 2, 0, 0, 0), gap(-5, -4)),
                    ((2024, 3, 10, 2, 59, 59, 999_999_999), gap(-5, -4)),
                    ((2024, 3, 10, 3, 0, 0, 0), unambiguous(-4)),
                    ((2024, 11, 3, 0, 59, 59, 999_999_999), unambiguous(-4)),
                    ((2024, 11, 3, 1, 0, 0, 0), fold(-4, -5)),
                    ((2024, 11, 3, 1, 59, 59, 999_999_999), fold(-4, -5)),
                    ((2024, 11, 3, 2, 0, 0, 0), unambiguous(-5)),
                ],
            ),
            // A bit of a nonsensical America/New_York that has DST, but whose
            // offset is equivalent to standard time. Having the same offset
            // means there's never any ambiguity.
            (
                "EST5EDT5,M3.2.0,M11.1.0",
                &[
                    ((1969, 12, 31, 19, 0, 0, 0), unambiguous(-5)),
                    ((2024, 3, 10, 1, 59, 59, 999_999_999), unambiguous(-5)),
                    ((2024, 3, 10, 2, 0, 0, 0), unambiguous(-5)),
                    ((2024, 3, 10, 2, 59, 59, 999_999_999), unambiguous(-5)),
                    ((2024, 3, 10, 3, 0, 0, 0), unambiguous(-5)),
                    ((2024, 11, 3, 0, 59, 59, 999_999_999), unambiguous(-5)),
                    ((2024, 11, 3, 1, 0, 0, 0), unambiguous(-5)),
                    ((2024, 11, 3, 1, 59, 59, 999_999_999), unambiguous(-5)),
                    ((2024, 11, 3, 2, 0, 0, 0), unambiguous(-5)),
                ],
            ),
            // This is Europe/Dublin's rule. It's interesting because its
            // DST is an offset behind standard time. (DST is usually one hour
            // ahead of standard time.)
            (
                "IST-1GMT0,M10.5.0,M3.5.0/1",
                &[
                    ((1970, 1, 1, 0, 0, 0, 0), unambiguous(0)),
                    ((2024, 3, 31, 0, 59, 59, 999_999_999), unambiguous(0)),
                    ((2024, 3, 31, 1, 0, 0, 0), gap(0, 1)),
                    ((2024, 3, 31, 1, 59, 59, 999_999_999), gap(0, 1)),
                    ((2024, 3, 31, 2, 0, 0, 0), unambiguous(1)),
                    ((2024, 10, 27, 0, 59, 59, 999_999_999), unambiguous(1)),
                    ((2024, 10, 27, 1, 0, 0, 0), fold(1, 0)),
                    ((2024, 10, 27, 1, 59, 59, 999_999_999), fold(1, 0)),
                    ((2024, 10, 27, 2, 0, 0, 0), unambiguous(0)),
                ],
            ),
            // This is Australia/Tasmania's rule. We chose this because it's
            // in the southern hemisphere where DST still skips ahead one hour,
            // but it usually starts in the fall and ends in the spring.
            (
                "AEST-10AEDT,M10.1.0,M4.1.0/3",
                &[
                    ((1970, 1, 1, 11, 0, 0, 0), unambiguous(11)),
                    ((2024, 4, 7, 1, 59, 59, 999_999_999), unambiguous(11)),
                    ((2024, 4, 7, 2, 0, 0, 0), fold(11, 10)),
                    ((2024, 4, 7, 2, 59, 59, 999_999_999), fold(11, 10)),
                    ((2024, 4, 7, 3, 0, 0, 0), unambiguous(10)),
                    ((2024, 10, 6, 1, 59, 59, 999_999_999), unambiguous(10)),
                    ((2024, 10, 6, 2, 0, 0, 0), gap(10, 11)),
                    ((2024, 10, 6, 2, 59, 59, 999_999_999), gap(10, 11)),
                    ((2024, 10, 6, 3, 0, 0, 0), unambiguous(11)),
                ],
            ),
            // This is Antarctica/Troll's rule. We chose this one because its
            // DST transition is 2 hours instead of the standard 1 hour. This
            // means gaps and folds are twice as long as they usually are. And
            // it means there are 22 hour and 26 hour days, respectively. Wow!
            (
                "<+00>0<+02>-2,M3.5.0/1,M10.5.0/3",
                &[
                    ((1970, 1, 1, 0, 0, 0, 0), unambiguous(0)),
                    // test the gap
                    ((2024, 3, 31, 0, 59, 59, 999_999_999), unambiguous(0)),
                    ((2024, 3, 31, 1, 0, 0, 0), gap(0, 2)),
                    ((2024, 3, 31, 1, 59, 59, 999_999_999), gap(0, 2)),
                    // still in the gap!
                    ((2024, 3, 31, 2, 0, 0, 0), gap(0, 2)),
                    ((2024, 3, 31, 2, 59, 59, 999_999_999), gap(0, 2)),
                    // finally out
                    ((2024, 3, 31, 3, 0, 0, 0), unambiguous(2)),
                    // test the fold
                    ((2024, 10, 27, 0, 59, 59, 999_999_999), unambiguous(2)),
                    ((2024, 10, 27, 1, 0, 0, 0), fold(2, 0)),
                    ((2024, 10, 27, 1, 59, 59, 999_999_999), fold(2, 0)),
                    // still in the fold!
                    ((2024, 10, 27, 2, 0, 0, 0), fold(2, 0)),
                    ((2024, 10, 27, 2, 59, 59, 999_999_999), fold(2, 0)),
                    // finally out
                    ((2024, 10, 27, 3, 0, 0, 0), unambiguous(0)),
                ],
            ),
            // This is America/St_Johns' rule, which has an offset with
            // non-zero minutes *and* a DST transition rule. (Indian Standard
            // Time is the one I'm more familiar with, but it turns out IST
            // does not have DST!)
            (
                "NST3:30NDT,M3.2.0,M11.1.0",
                &[
                    (
                        (1969, 12, 31, 20, 30, 0, 0),
                        o_unambiguous(-Offset::hms(3, 30, 0)),
                    ),
                    (
                        (2024, 3, 10, 1, 59, 59, 999_999_999),
                        o_unambiguous(-Offset::hms(3, 30, 0)),
                    ),
                    (
                        (2024, 3, 10, 2, 0, 0, 0),
                        o_gap(-Offset::hms(3, 30, 0), -Offset::hms(2, 30, 0)),
                    ),
                    (
                        (2024, 3, 10, 2, 59, 59, 999_999_999),
                        o_gap(-Offset::hms(3, 30, 0), -Offset::hms(2, 30, 0)),
                    ),
                    (
                        (2024, 3, 10, 3, 0, 0, 0),
                        o_unambiguous(-Offset::hms(2, 30, 0)),
                    ),
                    (
                        (2024, 11, 3, 0, 59, 59, 999_999_999),
                        o_unambiguous(-Offset::hms(2, 30, 0)),
                    ),
                    (
                        (2024, 11, 3, 1, 0, 0, 0),
                        o_fold(-Offset::hms(2, 30, 0), -Offset::hms(3, 30, 0)),
                    ),
                    (
                        (2024, 11, 3, 1, 59, 59, 999_999_999),
                        o_fold(-Offset::hms(2, 30, 0), -Offset::hms(3, 30, 0)),
                    ),
                    (
                        (2024, 11, 3, 2, 0, 0, 0),
                        o_unambiguous(-Offset::hms(3, 30, 0)),
                    ),
                ],
            ),
        ];
        for &(posix_tz, datetimes_to_ambiguous) in tests {
            let tz = TimeZone::posix(posix_tz).unwrap();
            for &(datetime, ref ambiguous_kind) in datetimes_to_ambiguous {
                let (year, month, day, hour, min, sec, nano) = datetime;
                let dt =
                    DateTime::constant(year, month, day, hour, min, sec, nano);
                let got = tz.to_ambiguous_instant(dt);
                assert_eq!(
                    got.kind(),
                    ambiguous_kind,
                    "\nTZ: {posix_tz}\ndatetime: \
                     {year:04}-{month:02}-{day:02}T\
                     {hour:02}:{min:02}:{sec:02}.{nano:09}",
                );
            }
        }
    }

    #[test]
    fn time_zone_posix_to_datetime() {
        let o = |hours| Offset::constant(hours);
        let tests: &[(&str, &[_])] = &[
            ("EST5", &[((0, 0), o(-5), (1969, 12, 31, 19, 0, 0, 0))]),
            (
                // From America/New_York
                "EST5EDT,M3.2.0,M11.1.0",
                &[
                    ((0, 0), o(-5), (1969, 12, 31, 19, 0, 0, 0)),
                    ((1710052200, 0), o(-5), (2024, 3, 10, 1, 30, 0, 0)),
                    (
                        (1710053999, 999_999_999),
                        o(-5),
                        (2024, 3, 10, 1, 59, 59, 999_999_999),
                    ),
                    ((1710054000, 0), o(-4), (2024, 3, 10, 3, 0, 0, 0)),
                    ((1710055800, 0), o(-4), (2024, 3, 10, 3, 30, 0, 0)),
                    ((1730610000, 0), o(-4), (2024, 11, 3, 1, 0, 0, 0)),
                    ((1730611800, 0), o(-4), (2024, 11, 3, 1, 30, 0, 0)),
                    (
                        (1730613599, 999_999_999),
                        o(-4),
                        (2024, 11, 3, 1, 59, 59, 999_999_999),
                    ),
                    ((1730613600, 0), o(-5), (2024, 11, 3, 1, 0, 0, 0)),
                    ((1730615400, 0), o(-5), (2024, 11, 3, 1, 30, 0, 0)),
                ],
            ),
            (
                // From Australia/Tasmania
                //
                // We chose this because it's a time zone in the southern
                // hemisphere with DST. Unlike the northern hemisphere, its DST
                // starts in the fall and ends in the spring. In the northern
                // hemisphere, we typically start DST in the spring and end it
                // in the fall.
                "AEST-10AEDT,M10.1.0,M4.1.0/3",
                &[
                    ((0, 0), o(11), (1970, 1, 1, 11, 0, 0, 0)),
                    ((1728142200, 0), o(10), (2024, 10, 6, 1, 30, 0, 0)),
                    (
                        (1728143999, 999_999_999),
                        o(10),
                        (2024, 10, 6, 1, 59, 59, 999_999_999),
                    ),
                    ((1728144000, 0), o(11), (2024, 10, 6, 3, 0, 0, 0)),
                    ((1728145800, 0), o(11), (2024, 10, 6, 3, 30, 0, 0)),
                    ((1712415600, 0), o(11), (2024, 4, 7, 2, 0, 0, 0)),
                    ((1712417400, 0), o(11), (2024, 4, 7, 2, 30, 0, 0)),
                    (
                        (1712419199, 999_999_999),
                        o(11),
                        (2024, 4, 7, 2, 59, 59, 999_999_999),
                    ),
                    ((1712419200, 0), o(10), (2024, 4, 7, 2, 0, 0, 0)),
                    ((1712421000, 0), o(10), (2024, 4, 7, 2, 30, 0, 0)),
                ],
            ),
            (
                // Uses the maximum possible offset. A sloppy read of POSIX
                // seems to indicate the maximum offset is 24:59:59, but since
                // DST defaults to 1 hour ahead of standard time, it's possible
                // to use 24:59:59 for standard time, omit the DST offset, and
                // thus get a DST offset of 25:59:59.
                "XXX-24:59:59YYY,M3.2.0,M11.1.0",
                &[
                    // 2024-01-05T00:00:00+00
                    (
                        (1704412800, 0),
                        Offset::hms(24, 59, 59),
                        (2024, 1, 6, 0, 59, 59, 0),
                    ),
                    // 2024-06-05T00:00:00+00 (DST)
                    (
                        (1717545600, 0),
                        Offset::hms(25, 59, 59),
                        (2024, 6, 6, 1, 59, 59, 0),
                    ),
                ],
            ),
        ];
        for &(posix_tz, instants_to_datetimes) in tests {
            let tz = TimeZone::posix(posix_tz).unwrap();
            for &((unix_sec, unix_nano), offset, datetime) in
                instants_to_datetimes
            {
                let (year, month, day, hour, min, sec, nano) = datetime;
                let instant = Instant::from_unix(unix_sec, unix_nano).unwrap();
                assert_eq!(
                    tz.to_offset(instant).0,
                    offset,
                    "\ntimestamp({unix_sec}, {unix_nano})",
                );
                assert_eq!(
                    tz.to_datetime(instant),
                    DateTime::constant(year, month, day, hour, min, sec, nano),
                    "\ntimestamp({unix_sec}, {unix_nano})",
                );
            }
        }
    }

    #[test]
    fn time_zone_fixed_to_datetime() {
        let tz = TimeZone::fixed(Offset::constant(-5));
        let unix_epoch = Instant::from_unix(0, 0).unwrap();
        assert_eq!(
            tz.to_datetime(unix_epoch),
            DateTime::constant(1969, 12, 31, 19, 0, 0, 0),
        );

        let tz = TimeZone::fixed(Offset::constant_seconds(93_599));
        let instant = Instant::from_unix(253402207200, 999_999_999).unwrap();
        assert_eq!(
            tz.to_datetime(instant),
            DateTime::constant(9999, 12, 31, 23, 59, 59, 999_999_999),
        );

        let tz = TimeZone::fixed(Offset::constant_seconds(-93_599));
        let instant = Instant::from_unix(-377705023201, 0).unwrap();
        assert_eq!(
            tz.to_datetime(instant),
            DateTime::constant(-9999, 1, 1, 0, 0, 0, 0),
        );
    }

    #[test]
    fn time_zone_fixed_to_instant() {
        let tz = TimeZone::fixed(Offset::constant(-5));
        let dt = DateTime::constant(1969, 12, 31, 19, 0, 0, 0);
        assert_eq!(
            tz.to_instant(dt).unwrap(),
            Instant::from_unix(0, 0).unwrap()
        );

        let tz = TimeZone::fixed(Offset::constant_seconds(93_599));
        let dt = DateTime::constant(9999, 12, 31, 23, 59, 59, 999_999_999);
        assert_eq!(
            tz.to_instant(dt).unwrap(),
            Instant::from_unix(253402207200, 999_999_999).unwrap(),
        );
        let tz = TimeZone::fixed(Offset::constant_seconds(93_598));
        assert!(tz.to_instant(dt).is_err());

        let tz = TimeZone::fixed(Offset::constant_seconds(-93_599));
        let dt = DateTime::constant(-9999, 1, 1, 0, 0, 0, 0);
        assert_eq!(
            tz.to_instant(dt).unwrap(),
            Instant::from_unix(-377705023201, 0).unwrap(),
        );
        let tz = TimeZone::fixed(Offset::constant_seconds(-93_598));
        assert!(tz.to_instant(dt).is_err());
    }

    /// This tests that the size of a time zone is kept at a single word.
    ///
    /// This is important because every jiff::Zoned has a TimeZone inside of
    /// it, and we want to keep its size as small as we can.
    #[test]
    fn time_zone_size() {
        let word = core::mem::size_of::<usize>();
        assert_eq!(word, core::mem::size_of::<TimeZone>());
    }
}
