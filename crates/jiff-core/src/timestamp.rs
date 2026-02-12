use crate::{
    bounds::{self as b, RangeError},
    civil::{DateTime, TimeSecond, UnixEpochDay},
    constants as c,
    macros::{rbail, rtry, unwrapr},
};

/// An instant in time represented as the number of nanoseconds since the Unix
/// epoch.
///
/// A timestamp is always in the Unix timescale with a UTC offset of zero.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct Timestamp {
    second: i64,
    nanosecond: i32,
}

impl Timestamp {
    /// The minimum allow Unix timestamp.
    pub const MIN: Timestamp = Timestamp {
        second: b::UnixEpochSeconds::MIN,
        nanosecond: b::SubsecNanosecond::MIN,
    };

    /// The maximum allow Unix timestamp.
    pub const MAX: Timestamp = Timestamp {
        second: b::UnixEpochSeconds::MAX,
        nanosecond: b::SubsecNanosecond::MAX,
    };

    /// The Unix epoch represented as a timestamp.
    pub const UNIX_EPOCH: Timestamp = Timestamp { second: 0, nanosecond: 0 };

    /// Create a new timestamp from the given number of seconds and its
    /// sub-second component.
    ///
    /// This returns an error if `nanos` is not in the range specified by
    /// [`SignedSubsecNanosecond`](b::SignedSubsecNanosecond). An error
    /// is also returned when `secs` is not in the range specified by
    /// [`UnixEpochSeconds`](b::UnixEpochSeconds).
    #[inline]
    pub const fn new(secs: i64, nanos: i32) -> Result<Timestamp, RangeError> {
        let mut secs = rtry!(b::UnixEpochSeconds::checkc(secs));
        let mut nanos = rtry!(b::SignedSubsecNanosecond::checkc(nanos as i64));
        if secs == b::UnixEpochSeconds::MIN && nanos < 0 {
            rbail!(b::UnixEpochSeconds::error());
        }
        // At this point, we're done if either unit is zero or if they have the
        // same sign.
        if nanos == 0 || secs == 0 || secs.signum() == (nanos.signum() as i64)
        {
            return Ok(Timestamp::new_unchecked(secs, nanos));
        }
        // Otherwise, the only work we have to do is to balance negative nanos
        // into positive seconds, or positive nanos into negative seconds.
        if secs < 0 {
            debug_assert!(nanos > 0);
            // Never wraps because adding +1 to a negative i64 never overflows.
            //
            // MSRV(1.79): Consider using `unchecked_add` here.
            secs += 1;
            // Never wraps because subtracting +1_000_000_000 from a positive
            // i32 never overflows.
            //
            // MSRV(1.79): Consider using `unchecked_sub` here.
            nanos -= c::NANOS_PER_SEC_32;
        } else {
            debug_assert!(secs > 0);
            debug_assert!(nanos < 0);
            // Never wraps because subtracting +1 from a positive i64 never
            // overflows.
            //
            // MSRV(1.79): Consider using `unchecked_add` here.
            secs -= 1;
            // Never wraps because adding +1_000_000_000 to a negative i32
            // never overflows.
            //
            // MSRV(1.79): Consider using `unchecked_add` here.
            nanos += c::NANOS_PER_SEC_32;
        }
        Ok(Timestamp::new_unchecked(secs, nanos))
    }

    /// Creates a new `Timestamp` without bounds checks.
    ///
    /// Note that this should not be made public *and* safe.
    #[inline]
    pub(crate) const fn new_unchecked(secs: i64, nanos: i32) -> Timestamp {
        debug_assert!(b::UnixEpochSeconds::checkc(secs).is_ok());
        debug_assert!(b::SignedSubsecNanosecond::checkc(nanos as i64).is_ok());
        debug_assert!(secs != b::UnixEpochSeconds::MIN || nanos >= 0);
        debug_assert!(
            nanos == 0
                || secs == 0
                || secs.signum() == (nanos.signum() as i64)
        );
        Timestamp { second: secs, nanosecond: nanos }
    }

    /// Constructs a timestamp from seconds since the Unix epoch.
    ///
    /// This is preferred to [`Timestamp::new`] when it is known that the
    /// sub-second component is always `0`. In particular, this generates
    /// less code and is likely to be faster.
    ///
    /// An error is returned when `second` is not in the range specified by
    /// [`UnixEpochSeconds`](b::UnixEpochSeconds).
    #[inline]
    pub const fn from_second(second: i64) -> Result<Timestamp, RangeError> {
        let second = rtry!(b::UnixEpochSeconds::checkc(second));
        Ok(Timestamp::new_unchecked(second, 0))
    }

    /// Constructs a timestamp from milliseconds since the Unix epoch.
    ///
    /// An error is returned when `millisecond` is not in the range specified by
    /// [`UnixEpochMilliseconds`](b::UnixEpochMilliseconds).
    #[inline]
    pub const fn from_millisecond(
        millisecond: i64,
    ) -> Result<Timestamp, RangeError> {
        let millisecond = rtry!(b::UnixEpochMilliseconds::checkc(millisecond));
        // OK because MILLIS_PER_SEC!={-1,0}.
        let secs = millisecond / c::MILLIS_PER_SEC;
        // OK because MILLIS_PER_SEC!={-1,0} and because
        // millis % MILLIS_PER_SEC can be at most 999, and 999 * 1_000_000
        // never overflows i32.
        let nanos =
            (millisecond % c::MILLIS_PER_SEC) as i32 * c::NANOS_PER_MILLI_32;
        // OK because we've already verified that `millisecond` is in range.
        Ok(Timestamp::new_unchecked(secs, nanos))
    }

    /// Constructs a timestamp from microseconds since the Unix epoch.
    ///
    /// An error is returned when `microsecond` is not in the range specified
    /// by [`UnixEpochMicroseconds`](b::UnixEpochMicroseconds).
    #[inline]
    pub const fn from_microsecond(
        microsecond: i64,
    ) -> Result<Timestamp, RangeError> {
        let microsecond = rtry!(b::UnixEpochMicroseconds::checkc(microsecond));
        // OK because MILLIS_PER_SEC!={-1,0}.
        let secs = microsecond / c::MICROS_PER_SEC;
        // OK because MILLIS_PER_SEC!={-1,0} and because
        // millis % MILLIS_PER_SEC can be at most 999, and 999 * 1_000_000
        // never overflows i32.
        let nanos =
            (microsecond % c::MICROS_PER_SEC) as i32 * c::NANOS_PER_MICRO_32;
        // OK because we've already verified that `millisecond` is in range.
        Ok(Timestamp::new_unchecked(secs, nanos))
    }

    /// Constructs a timestamp from nanoseconds since the Unix epoch.
    ///
    /// An error is returned when `nanosecond` refers to a timestamp outside
    /// of the range [`Timestamp::MIN`] to [`Timestamp::MAX`].
    #[inline]
    pub const fn from_nanosecond(
        nanosecond: i128,
    ) -> Result<Timestamp, RangeError> {
        const NANOS_PER_SEC: i128 = c::NANOS_PER_SEC as i128;
        // OK because NANOS_PER_SEC!={-1,0}.
        let secs = nanosecond / NANOS_PER_SEC;
        // RUST: Use `i64::try_from` when available in `const`.
        if !(i64::MIN as i128 <= secs && secs <= i64::MAX as i128) {
            rbail!(b::SpecialBoundsError::UnixEpochNanoseconds);
        }
        let secs64 = secs as i64;
        // OK because NANOS_PER_SEC!={-1,0}.
        let nanosecond = (nanosecond % NANOS_PER_SEC) as i32;
        Ok(Timestamp::new_unchecked(secs64, nanosecond))
    }

    /// Returns this timestamp as a number of seconds since the Unix epoch.
    ///
    /// This only returns the number of whole seconds. That is, if there are
    /// any fractional seconds in this timestamp, then they are truncated.
    #[inline]
    pub const fn as_second(self) -> i64 {
        self.second
    }

    /// Returns this timestamp as a number of milliseconds since the Unix
    /// epoch.
    ///
    /// This only returns the number of whole milliseconds. That is, if there
    /// are any fractional milliseconds in this timestamp, then they are
    /// truncated.
    #[inline]
    pub const fn as_millisecond(self) -> i64 {
        // OK because the range of `Timestamp` guarantees that its
        // representation as milliseconds fits into an i64.
        let millis = self.as_second() * c::MILLIS_PER_SEC;
        // OK because subsec_millis maxes out at 999, and adding that to
        // b::UnixSeconds::MAX*1_000 will never overflow an i64.
        millis + (self.subsec_millisecond() as i64)
    }

    /// Returns this timestamp as a number of microseconds since the Unix
    /// epoch.
    ///
    /// This only returns the number of whole microseconds. That is, if there
    /// are any fractional microseconds in this timestamp, then they are
    /// truncated.
    #[inline]
    pub const fn as_microsecond(self) -> i64 {
        // OK because the range of `Timestamp` guarantees that its
        // representation as microseconds fits into an i64.
        let micros = self.as_second() * c::MICROS_PER_SEC;
        // OK because subsec_micros maxes out at 999_999, and adding that to
        // b::UnixSeconds::MAX*1_000_000 will never overflow an i64.
        micros + (self.subsec_microsecond() as i64)
    }

    /// Returns this timestamp as a number of nanoseconds since the Unix
    /// epoch.
    #[inline]
    pub const fn as_nanosecond(self) -> i128 {
        // OK because 1_000_000_000 times any i64 will never overflow i128.
        let nanos = (self.second as i128) * (c::NANOS_PER_SEC as i128);
        // OK because nanosecond maxes out at 999_999_999, and adding that to
        // i64::MAX*1_000_000_000 will never overflow a i128.
        nanos + (self.nanosecond as i128)
    }

    /// Returns the fractional second component of this timestamp in units of
    /// microseconds.
    ///
    /// The value returned is negative when the timestamp is negative. It is
    /// guaranteed that the range of the value returned is in the inclusive
    /// range `-999_999..=999_999`.
    #[inline]
    pub const fn subsec_millisecond(&self) -> i32 {
        // OK because NANOS_PER_MILLI!={-1,0}.
        self.nanosecond / c::NANOS_PER_MILLI_32
    }

    /// Returns the fractional second component of this timestamp in units of
    /// milliseconds.
    ///
    /// The value returned is negative when the timestamp is negative. It is
    /// guaranteed that the range of the value returned is in the inclusive
    /// range `-999..=999`.
    #[inline]
    pub const fn subsec_microsecond(&self) -> i32 {
        // OK because NANOS_PER_MICRO!={-1,0}.
        self.nanosecond / c::NANOS_PER_MICRO_32
    }

    /// Returns the fractional second component of this timestamp in units of
    /// nanoseconds.
    ///
    /// The value returned is negative when the timestamp is negative. It is
    /// guaranteed that the range of the value returned is in the inclusive
    /// range `-999,999,999..=999,999,999`.
    #[inline]
    pub const fn subsec_nanosecond(&self) -> i32 {
        self.nanosecond
    }

    /// Returns a number that represents the sign of this timestamp.
    ///
    /// * When [`Timestamp::is_zero`] is true, this returns `0`.
    /// * When [`Timestamp::is_positive`] is true, this returns `1`.
    /// * When [`Timestamp::is_negative`] is true, this returns `-1`.
    ///
    /// The above cases are mutually exclusive.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff_core::Timestamp;
    ///
    /// assert_eq!(0, Timestamp::UNIX_EPOCH.signum());
    ///
    /// let ts = Timestamp::new(5, -999_999_999)?;
    /// assert_eq!(ts.signum(), 1);
    /// // The mixed signs were normalized away!
    /// assert_eq!(ts.as_second(), 4);
    /// assert_eq!(ts.subsec_nanosecond(), 1);
    ///
    /// // The same applies for negative timestamps.
    /// let ts = Timestamp::new(-5, 999_999_999)?;
    /// assert_eq!(ts.signum(), -1);
    /// assert_eq!(ts.as_second(), -4);
    /// assert_eq!(ts.subsec_nanosecond(), -1);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub const fn signum(self) -> i8 {
        if self.is_zero() {
            0
        } else if self.is_positive() {
            1
        } else {
            debug_assert!(self.is_negative());
            -1
        }
    }

    /// Returns true if and only if this timestamp corresponds to the instant
    /// in time known as the Unix epoch.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff_core::Timestamp;
    ///
    /// assert!(Timestamp::UNIX_EPOCH.is_zero());
    /// ```
    #[inline]
    pub const fn is_zero(self) -> bool {
        self.second == 0 && self.nanosecond == 0
    }

    /// Returns true when this timestamp is positive. That is, after the Unix
    /// epoch.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff_core::Timestamp;
    ///
    /// let ts = Timestamp::new(0, 1)?;
    /// assert!(ts.is_positive());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub const fn is_positive(&self) -> bool {
        self.second.is_positive() || self.nanosecond.is_positive()
    }

    /// Returns true when this timestamp is negative. That is, before the Unix
    /// epoch.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff_core::Timestamp;
    ///
    /// let ts = Timestamp::new(0, -1)?;
    /// assert!(ts.is_negative());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub const fn is_negative(&self) -> bool {
        self.second.is_negative() || self.nanosecond.is_negative()
    }

    /// Converts a Unix timestamp with an offset to a Gregorian datetime.
    ///
    /// The offset should correspond to the number of seconds required to
    /// add to this timestamp to get the local time.
    #[inline]
    pub const fn to_datetime(&self, offset: Offset) -> DateTime {
        let Timestamp { second, mut nanosecond } = *self;

        // Shift second comfortably into the postive domain
        // so that division and remainder can use unsigned math
        // which is much faster.
        // 30 * 400 years: 12,000 yr range > [-9,999..1970]
        // (146097 being the number of days per 400 years).
        const DAY_SHIFT: i32 = 30 * 146097;
        const SEC_SHIFT: i64 = (DAY_SHIFT as i64) * 86_400;

        let pos_sec = (second + (offset.second as i64) + SEC_SHIFT) as u64;
        let mut epoch_day = (pos_sec / 86_400) as i32;
        let mut second = (pos_sec % 86_400) as i32;

        if nanosecond < 0 {
            if second > 0 {
                second -= 1;
                nanosecond += 1_000_000_000;
            } else {
                epoch_day -= 1;
                second += 86_399;
                nanosecond += 1_000_000_000;
            }
        }

        epoch_day -= DAY_SHIFT;

        // We should check whether having unchecked APIs
        // would be beneficial here. In particular, the
        // math above, coupled with the ranges allowed on
        // `Timestamp` and `Offset` (by design) guarantee
        // that our resulting datetime will always be in
        // range.
        let date = unwrapr!(
            UnixEpochDay::new(epoch_day),
            "always valid Unix epoch day",
        )
        .to_date();
        let time = unwrapr!(
            unwrapr!(
                TimeSecond::new(second),
                "always valid civil second time"
            )
            .to_time()
            .with_subsec_nanosecond(nanosecond),
            "always valid civil subsecond"
        );
        DateTime::from_parts(date, time)
    }
}

impl Default for Timestamp {
    #[inline]
    fn default() -> Timestamp {
        Timestamp::UNIX_EPOCH
    }
}

#[cfg(test)]
impl quickcheck::Arbitrary for Timestamp {
    fn arbitrary(g: &mut quickcheck::Gen) -> Timestamp {
        let secs = b::UnixEpochSeconds::arbitrary(g);
        let mut nanos = b::SignedSubsecNanosecond::arbitrary(g);
        // nanoseconds must be zero for the minimum second value,
        // so just clamp it to 0.
        if secs == b::UnixEpochSeconds::MIN && nanos < 0 {
            nanos = 0;
        }
        Timestamp::new(secs, nanos).unwrap_or(Timestamp::UNIX_EPOCH)
    }

    fn shrink(&self) -> alloc::boxed::Box<dyn Iterator<Item = Self>> {
        let secs = self.as_second();
        let nanos = self.subsec_nanosecond();
        alloc::boxed::Box::new((secs, nanos).shrink().filter_map(
            |(secs, nanos)| {
                let secs = b::UnixEpochSeconds::check(secs).ok()?;
                let nanos = b::SignedSubsecNanosecond::check(nanos).ok()?;
                if secs == b::UnixEpochSeconds::MIN && nanos > 0 {
                    None
                } else {
                    Timestamp::new(secs, nanos).ok()
                }
            },
        ))
    }
}

/// A fixed offset, in seconds, from UTC.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct Offset {
    second: i32,
}

impl Offset {
    /// The minimum possible offset from UTC.
    pub const MIN: Offset = Offset { second: b::OffsetTotalSeconds::MIN };

    /// The maximum possible offset from UTC.
    pub const MAX: Offset = Offset { second: b::OffsetTotalSeconds::MAX };

    /// The UTC offset.
    pub const UTC: Offset = Offset { second: 0 };

    /// Returns a new time zone offset from UTC given its representation in
    /// seconds.
    ///
    /// An error is also returned when `second` is not in the range specified
    /// by [`OffsetTotalSeconds`](b::OffsetTotalSeconds).
    #[inline]
    pub const fn new(second: i32) -> Result<Offset, RangeError> {
        let second = rtry!(b::OffsetTotalSeconds::checkc(second as i64));
        Ok(Offset { second })
    }

    /// Returns the second value corresponding to this time zone offset.
    #[inline]
    pub const fn second(self) -> i32 {
        self.second
    }
}

#[cfg(test)]
impl quickcheck::Arbitrary for Offset {
    fn arbitrary(g: &mut quickcheck::Gen) -> Offset {
        let secs = b::OffsetTotalSeconds::arbitrary(g);
        Offset::new(secs).unwrap_or(Offset::UTC)
    }

    fn shrink(&self) -> alloc::boxed::Box<dyn Iterator<Item = Self>> {
        let secs = self.second();
        alloc::boxed::Box::new(secs.shrink().filter_map(|secs| {
            let secs = b::OffsetTotalSeconds::check(secs).ok()?;
            Offset::new(secs).ok()
        }))
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AmbiguousOffset {
    Unambiguous { offset: Offset },
    Gap { before: Offset, after: Offset },
    Fold { before: Offset, after: Offset },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[track_caller]
    fn datetime(
        year: i16,
        month: i8,
        day: i8,
        hour: i8,
        minute: i8,
        second: i8,
        subsec_nanosecond: i32,
    ) -> DateTime {
        DateTime::new(
            year,
            month,
            day,
            hour,
            minute,
            second,
            subsec_nanosecond,
        )
        .unwrap()
    }

    #[track_caller]
    fn stamp(second: i64, subsec: i32) -> Timestamp {
        Timestamp::new(second, subsec).unwrap()
    }

    #[track_caller]
    fn offset(second: i32) -> Offset {
        Offset::new(second).unwrap()
    }

    #[test]
    fn new_ok() {
        let ts = stamp(0, 0);
        assert_eq!(ts, Timestamp::UNIX_EPOCH);

        let ts = stamp(0, 123_000_000);
        assert_eq!(ts.as_second(), 0);
        assert_eq!(ts.subsec_nanosecond(), 123_000_000);

        let ts = stamp(0, -123_000_000);
        assert_eq!(ts.as_second(), 0);
        assert_eq!(ts.subsec_nanosecond(), -123_000_000);

        let ts = stamp(1, 0);
        assert_eq!(ts.as_second(), 1);
        assert_eq!(ts.subsec_nanosecond(), 0);

        let ts = stamp(-1, 0);
        assert_eq!(ts.as_second(), -1);
        assert_eq!(ts.subsec_nanosecond(), 0);

        let ts = stamp(1, 123_000_000);
        assert_eq!(ts.as_second(), 1);
        assert_eq!(ts.subsec_nanosecond(), 123_000_000);

        let ts = stamp(-1, -123_000_000);
        assert_eq!(ts.as_second(), -1);
        assert_eq!(ts.subsec_nanosecond(), -123_000_000);

        let ts = stamp(1, -123_000_000);
        assert_eq!(ts.as_second(), 0);
        assert_eq!(ts.subsec_nanosecond(), 877_000_000);

        let ts = stamp(-1, 123_000_000);
        assert_eq!(ts.as_second(), 0);
        assert_eq!(ts.subsec_nanosecond(), -877_000_000);

        let ts = stamp(-377705023201, 0);
        assert_eq!(ts, Timestamp::MIN);

        let ts = stamp(253402207200, 999_999_999);
        assert_eq!(ts, Timestamp::MAX);
    }

    #[test]
    fn new_err() {
        assert!(Timestamp::new(0, 1_000_000_000).is_err());
        assert!(Timestamp::new(0, -1_000_000_000).is_err());
        assert!(Timestamp::new(1, 1_000_000_000).is_err());
        assert!(Timestamp::new(1, -1_000_000_000).is_err());
        assert!(Timestamp::new(-1, 1_000_000_000).is_err());
        assert!(Timestamp::new(-1, -1_000_000_000).is_err());
        assert!(Timestamp::new(0, i32::MAX).is_err());
        assert!(Timestamp::new(0, i32::MIN).is_err());
        assert!(Timestamp::new(-377705023201, -1).is_err());
        assert!(Timestamp::new(253402207201, 0).is_err());
    }

    #[test]
    fn to_datetime_no_subsec() {
        let dt = datetime(1970, 1, 1, 0, 0, 0, 0);
        assert_eq!(stamp(0, 0).to_datetime(offset(0)), dt);
        assert_eq!(stamp(-3600, 0).to_datetime(offset(3600)), dt);
        assert_eq!(stamp(3600, 0).to_datetime(offset(-3600)), dt);

        let dt = datetime(1969, 12, 31, 23, 30, 0, 0);
        assert_eq!(stamp(-1800, 0).to_datetime(offset(0)), dt);
        assert_eq!(stamp(-5400, 0).to_datetime(offset(3600)), dt);
        assert_eq!(stamp(1800, 0).to_datetime(offset(-3600)), dt);

        let dt = datetime(1970, 1, 1, 0, 30, 0, 0);
        assert_eq!(stamp(1800, 0).to_datetime(offset(0)), dt);
        assert_eq!(stamp(-1800, 0).to_datetime(offset(3600)), dt);
        assert_eq!(stamp(5400, 0).to_datetime(offset(-3600)), dt);
    }

    #[test]
    fn to_datetime_with_subsec() {
        let dt = datetime(1970, 1, 1, 0, 0, 0, 123);
        assert_eq!(stamp(0, 123).to_datetime(offset(0)), dt);
        assert_eq!(stamp(-3599, -999_999_877).to_datetime(offset(3600)), dt);
        assert_eq!(stamp(3600, 123).to_datetime(offset(-3600)), dt);

        let dt = datetime(1969, 12, 31, 23, 30, 0, 123);
        assert_eq!(stamp(-1799, -999_999_877).to_datetime(offset(0)), dt);
        assert_eq!(stamp(-5399, -999_999_877).to_datetime(offset(3600)), dt);
        assert_eq!(stamp(1800, 123).to_datetime(offset(-3600)), dt);

        let dt = datetime(1970, 1, 1, 0, 30, 0, 123);
        assert_eq!(stamp(1800, 123).to_datetime(offset(0)), dt);
        assert_eq!(stamp(-1799, -999_999_877).to_datetime(offset(3600)), dt);
        assert_eq!(stamp(5400, 123).to_datetime(offset(-3600)), dt);
    }

    #[test]
    fn to_datetime_limits() {
        assert_eq!(Timestamp::MIN.to_datetime(Offset::MIN), DateTime::MIN);
        assert_eq!(Timestamp::MAX.to_datetime(Offset::MAX), DateTime::MAX);
    }

    quickcheck::quickcheck! {
        fn prop_timestamp_datetime_roundtrip(
            ts: Timestamp,
            offset: Offset
        ) -> bool {
            let dt = ts.to_datetime(offset);
            let got = dt.to_timestamp(offset).unwrap();
            got == ts
        }
    }
}
