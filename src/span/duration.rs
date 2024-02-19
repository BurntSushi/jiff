use core::ops::{Add, AddAssign, Mul, Neg, Sub, SubAssign};

use crate::{
    civil,
    error::Error,
    span::Span,
    util::{
        rangeint::{RFrom, RInto, TryRFrom},
        t::{self, NoUnits128, C},
    },
};

/// Represents a duration in time in units of seconds with a fractional
/// nanosecond part.
///
/// The range of seconds is big enough to represent all possible spans in the
/// range `UnixSeconds::MIN..=UnixSeconds::MAX`. That is, it can represent any
/// span of time with the allowed range of representable times supported by
/// this library. (It can technically represent up to `999_999_999` nanoseconds
/// outside of both the minimum and maximum.)
///
/// # Construction
///
/// Typically construction is done via [`Span::time_parts_to_duration`].
///
/// # Comparison with `std::time::Duration`
///
/// The main operational difference is that this duration can be negative,
/// where as the standard library duration is always positive. Otherwise, this
/// duration is clamped to the specific range of seconds supported by this
/// library, and supports a wider variety of operations tailored to this
/// datetime library.
#[derive(Clone, Copy)]
pub(crate) struct TimeDuration {
    seconds: t::SpanSeconds,
    nanoseconds: t::FractionalNanosecond,
}

impl TimeDuration {
    /// The minimum possible time duration.
    pub(crate) const MIN: TimeDuration = TimeDuration {
        seconds: t::SpanSeconds::MIN_SELF,
        nanoseconds: t::FractionalNanosecond::MIN_SELF,
    };

    /// The maximum possible time duration.
    pub(crate) const MAX: TimeDuration = TimeDuration {
        seconds: t::SpanSeconds::MAX_SELF,
        nanoseconds: t::FractionalNanosecond::MAX_SELF,
    };

    /// The zero duration.
    pub(crate) const ZERO: TimeDuration = TimeDuration {
        seconds: t::SpanSeconds::N::<0>(),
        nanoseconds: t::FractionalNanosecond::N::<0>(),
    };

    /// A duration corresponding to a single civil day. i.e., 86,400 seconds.
    pub(crate) const CIVIL_DAY: TimeDuration = TimeDuration {
        seconds: t::SpanSeconds::N::<86_400>(),
        nanoseconds: t::FractionalNanosecond::N::<0>(),
    };

    /// Create a new duration from the given number of seconds.
    #[inline]
    pub(crate) fn new(
        seconds: impl RInto<t::SpanSeconds>,
        nanoseconds: impl RInto<t::FractionalNanosecond>,
    ) -> TimeDuration {
        let seconds = seconds.rinto();
        let nanoseconds = nanoseconds.rinto();
        if seconds.signum() == nanoseconds.signum()
            || seconds == 0
            || nanoseconds == 0
        {
            return TimeDuration { seconds, nanoseconds };
        }
        let seconds = seconds.without_bounds();
        let nanoseconds = nanoseconds.without_bounds();
        let [delta_seconds, delta_nanos] = t::NoUnits::vary_many(
            [seconds, nanoseconds],
            |[seconds, nanoseconds]| {
                if seconds < 0 && nanoseconds > 0 {
                    [C(1), (-t::NANOS_PER_SECOND).rinto()]
                } else if seconds > 0 && nanoseconds < 0 {
                    [C(-1), t::NANOS_PER_SECOND.rinto()]
                } else {
                    [C(0), C(0)]
                }
            },
        );
        TimeDuration {
            seconds: (seconds + delta_seconds).rinto(),
            nanoseconds: (nanoseconds + delta_nanos).rinto(),
        }
    }

    /// Create a new duration from primitive values.
    ///
    /// # Errors
    ///
    /// This returns an error when either `seconds` exceeds the maximum span
    /// of seconds allowed, or if `nanoseconds` is not in the range
    /// `-999_999_999..=999_999_999`.
    #[inline]
    pub(crate) fn try_new(
        seconds: i64,
        nanoseconds: i32,
    ) -> Result<TimeDuration, Error> {
        let seconds = t::SpanSeconds::try_new("seconds", seconds)?;
        let nanoseconds =
            t::FractionalNanosecond::try_new("nanoseconds", nanoseconds)?;
        Ok(TimeDuration::new(seconds, nanoseconds))
    }

    /// Returns *only* the time parts of the given [`Span`] as a
    /// [`TimeDuration`].
    ///
    /// That is, the `years`, `months`, `weeks` and `days` fields on a span are
    /// ignored.
    ///
    /// # Errors
    ///
    /// This returns an error if this span exceeds what can be represented
    /// in a `SpanSeconds`.
    #[inline]
    pub(crate) fn from_span(span: &Span) -> Result<TimeDuration, Error> {
        let hours = t::SpanSeconds::rfrom(span.get_hours_ranged());
        let minutes = span.get_minutes_ranged();
        let mut seconds: t::SpanSeconds = (hours * t::SECONDS_PER_HOUR)
            .try_checked_add(
                "minutes-to-seconds",
                minutes * t::SECONDS_PER_MINUTE,
            )?
            .try_checked_add("seconds", span.get_seconds_ranged())?;
        let milliseconds = span.get_milliseconds_ranged();
        seconds = seconds.try_checked_add(
            "milliseconds-to-seconds",
            milliseconds.div_ceil(t::MILLIS_PER_SECOND),
        )?;
        let microseconds = span.get_microseconds_ranged();
        seconds = seconds.try_checked_add(
            "microseconds-to-seconds",
            microseconds.div_ceil(t::MICROS_PER_SECOND),
        )?;
        let nanoseconds = span.get_nanoseconds_ranged();
        seconds = seconds.try_checked_add(
            "nanoseconds-to-seconds",
            nanoseconds.div_ceil(t::NANOS_PER_SECOND),
        )?;

        let mut fractional_nanoseconds = t::FractionalNanosecond::rfrom(
            nanoseconds.rem_ceil(t::NANOS_PER_SECOND),
        );
        fractional_nanoseconds +=
            t::NANOS_PER_MICRO * microseconds.rem_ceil(t::MICROS_PER_SECOND);
        fractional_nanoseconds +=
            t::NANOS_PER_MILLI * milliseconds.rem_ceil(t::MILLIS_PER_SECOND);
        seconds += fractional_nanoseconds.div_ceil(t::NANOS_PER_SECOND);
        fractional_nanoseconds =
            fractional_nanoseconds.rem_ceil(t::NANOS_PER_SECOND);
        Ok(TimeDuration::new(seconds, fractional_nanoseconds))
    }

    #[inline]
    pub(crate) fn from_nanoseconds(
        nanoseconds: NoUnits128,
    ) -> Result<TimeDuration, Error> {
        let seconds = t::SpanSeconds::try_rfrom(
            "duration-as-nanoseconds",
            nanoseconds.div_ceil(t::NANOS_PER_SECOND),
        )?;
        let nanoseconds = nanoseconds.rem_ceil(t::NANOS_PER_SECOND);
        Ok(TimeDuration::new(seconds, nanoseconds))
    }

    /// Return a new duration with the number of seconds set to the given
    /// value. The nanoseconds remain the same as in `self`.
    #[inline]
    pub(crate) fn with_seconds(
        self,
        seconds: impl RInto<t::SpanSeconds>,
    ) -> TimeDuration {
        TimeDuration::new(seconds, self.nanoseconds)
    }

    /// Return a new duration with the number of nanoseconds set to the given
    /// value. The seconds remain the same as in `self`.
    #[inline]
    pub(crate) fn with_nanos(
        self,
        nanoseconds: impl RInto<t::FractionalNanosecond>,
    ) -> TimeDuration {
        TimeDuration::new(self.seconds, nanoseconds)
    }

    /// Negate this duration.
    ///
    /// If it was negative, then this will make the duration positive. If it
    /// was positive, then this wil make the duration negative. If the duration
    /// is `0`, then this is a no-op.
    #[inline]
    pub(crate) fn negate(self) -> TimeDuration {
        TimeDuration { seconds: -self.seconds, nanoseconds: -self.nanoseconds }
    }

    /// Returns the absolute value of this duration.
    ///
    /// If the duration was negative, and then this returns the same duration
    /// but with the sign flipped to positive. If the duration was positive,
    /// then this returns the duration as is.
    #[inline]
    pub(crate) fn abs(self) -> TimeDuration {
        TimeDuration {
            seconds: self.seconds.abs(),
            nanoseconds: self.nanoseconds.abs(),
        }
    }

    /// Convert this duration into a `Span`.
    #[inline]
    pub(crate) fn to_span(self) -> Span {
        Span::new()
            .seconds_ranged(self.seconds())
            .nanoseconds_ranged(self.nanoseconds())
    }

    #[inline]
    pub(crate) fn to_nanoseconds(self) -> NoUnits128 {
        let seconds = NoUnits128::rfrom(self.seconds());
        let nanoseconds = NoUnits128::rfrom(self.nanoseconds());
        seconds * t::NANOS_PER_SECOND + nanoseconds
    }

    /// Return the primitive second and nanosecond components of this duration.
    #[inline]
    pub(crate) fn to_parts(self) -> (i64, i32) {
        (self.seconds.get(), self.nanoseconds.get())
    }

    /// Return the ranged second and nanosecond components of this duration.
    #[inline]
    pub(crate) fn to_parts_ranged(
        self,
    ) -> (t::SpanSeconds, t::FractionalNanosecond) {
        (self.seconds, self.nanoseconds)
    }

    /// Returns the number of seconds in this duration.
    #[inline]
    pub(crate) fn seconds(self) -> t::SpanSeconds {
        self.seconds
    }

    /// Returns the number of nanoseconds in this duration.
    ///
    /// As the return type indicates, the number of nanoseconds is always less
    /// than 1 second.
    #[inline]
    pub(crate) fn nanoseconds(self) -> t::FractionalNanosecond {
        self.nanoseconds
    }

    /// Return the sign of this duration.
    #[inline]
    pub(crate) fn signum(self) -> t::Sign {
        let seconds = self.seconds().without_bounds();
        let nanoseconds = self.nanoseconds().without_bounds();
        let [signum] = t::NoUnits::vary_many(
            [seconds, nanoseconds],
            |[seconds, nanoseconds]| {
                if seconds != 0 {
                    [seconds.signum()]
                } else {
                    [nanoseconds.signum()]
                }
            },
        );
        signum.rinto()
    }

    /// Returns true if this duration is precisely equal to zero.
    #[inline]
    pub(crate) fn is_zero(self) -> bool {
        self.seconds() == 0 && self.nanoseconds() == 0
    }

    /// Adds the given right-hand-side duration to this one.
    ///
    /// # Errors
    ///
    /// If the addition of two durations would represent a bigger span of time
    /// than what is supported by this library, then an error is returned.
    #[inline]
    pub(crate) fn checked_add(
        self,
        rhs: TimeDuration,
    ) -> Result<TimeDuration, Error> {
        let seconds =
            self.seconds().try_checked_add("seconds", rhs.seconds())?;
        let nanoseconds = self.nanoseconds().without_bounds()
            + rhs.nanoseconds().without_bounds();
        if let Ok(nanoseconds) =
            t::FractionalNanosecond::try_rfrom("nanoseconds", nanoseconds)
        {
            return Ok(TimeDuration::new(seconds, nanoseconds));
        }
        let seconds = seconds.without_bounds();
        // let nanoseconds = nanoseconds.without_bounds();
        // This is a little tricky, but both our seconds and nanosecond values
        // can change, and that change is dependent on both or either of
        // seconds and nanoseconds. Because of that, we need our range integers
        // to capture the full scope of dependent variation. So we need to
        // calculate how much we're going to change each by. This is also why
        // we convert our nanoseconds to `SpanSeconds`, so that we can vary
        // both values at the same time.
        //
        // It is much simpler to implement this using div/mod (basically,
        // "balancing"), but I theorized that it would be better to use
        // simpler ops here given that this is probably a hot path (since
        // a TimeDuration is the representation of an Instant). I haven't
        // actually benchmarked it though.
        let [delta_seconds, delta_nanos] = t::NoUnits::vary_many(
            [seconds, nanoseconds],
            |[seconds, nanoseconds]| {
                // We generally have two cases to handle here: when the
                // addition of nanoseconds causes it to go out of range (in
                // either direction), or when seconds and nanoseconds have a
                // different sign.
                //
                // The first case is somewhat straightforward. If nanoseconds
                // overflows, then it can overflow by at most 999_999_999. So
                // we add (or subtract) one second, and then add (or subtract)
                // 1_000_000_000 to the leftovers.
                //
                // The second case is handled by the `TimeDuration::new`
                // constructor call below.
                if nanoseconds >= t::NANOS_PER_SECOND {
                    [C(1), (-t::NANOS_PER_SECOND).rinto()]
                } else if nanoseconds <= -t::NANOS_PER_SECOND {
                    [C(-1), t::NANOS_PER_SECOND.rinto()]
                } else {
                    [C(0), C(0)]
                }
            },
        );
        let mut seconds = t::SpanSeconds::rfrom(seconds);
        let mut nanoseconds = t::FractionalNanosecond::rfrom(nanoseconds);
        seconds = seconds.try_checked_add("seconds", delta_seconds)?;
        nanoseconds += delta_nanos;
        Ok(TimeDuration::new(seconds, nanoseconds))
    }

    /// Subtracts the given right-hand-side duration from this one.
    ///
    /// # Errors
    ///
    /// If the subtraction of two durations would represent a bigger span of
    /// time than what is supported by this library, then an error is returned.
    #[inline]
    pub(crate) fn checked_sub(
        self,
        rhs: TimeDuration,
    ) -> Result<TimeDuration, Error> {
        self.checked_add(rhs.negate())
    }

    /// Multiplies this duration by the given factor.
    ///
    /// # Errors
    ///
    /// If the multiplication overflows this duration, then an error is
    /// returned.
    #[inline]
    pub(crate) fn checked_mul(
        self,
        rhs: impl RInto<t::NoUnits>,
    ) -> Result<TimeDuration, Error> {
        let rhs = rhs.rinto();
        let seconds = self.seconds().try_checked_mul("seconds", rhs)?;
        let nanoseconds = self
            .nanoseconds()
            .without_bounds()
            .try_checked_mul("nanoseconds", rhs)?;
        let add_seconds = nanoseconds.div_ceil(t::NANOS_PER_SECOND);
        let nanoseconds = t::FractionalNanosecond::rfrom(
            nanoseconds.rem_ceil(t::NANOS_PER_SECOND),
        );
        let seconds = seconds.try_checked_add("seconds", add_seconds)?;
        Ok(TimeDuration { seconds, nanoseconds })
    }
}

impl Default for TimeDuration {
    #[inline]
    fn default() -> TimeDuration {
        TimeDuration::ZERO
    }
}

impl Eq for TimeDuration {}

impl PartialEq for TimeDuration {
    #[inline]
    fn eq(&self, rhs: &TimeDuration) -> bool {
        self.seconds.get() == rhs.seconds.get()
            && self.nanoseconds.get() == rhs.nanoseconds.get()
    }
}

impl Ord for TimeDuration {
    #[inline]
    fn cmp(&self, rhs: &TimeDuration) -> core::cmp::Ordering {
        (self.seconds.get(), self.nanoseconds.get())
            .cmp(&(rhs.seconds.get(), rhs.nanoseconds.get()))
    }
}

impl PartialOrd for TimeDuration {
    #[inline]
    fn partial_cmp(&self, rhs: &TimeDuration) -> Option<core::cmp::Ordering> {
        Some(self.cmp(rhs))
    }
}

impl Neg for TimeDuration {
    type Output = TimeDuration;

    #[inline]
    fn neg(self) -> Self {
        self.negate()
    }
}

impl Add for TimeDuration {
    type Output = TimeDuration;

    #[inline]
    fn add(self, rhs: TimeDuration) -> Self {
        // See comments in `checked_add` for how this works. The only
        // difference here is that we don't do checked arithmetic. We rely on
        // our range integers to catch boundary bugs.

        let seconds = self.seconds() + rhs.seconds();
        let nanoseconds = self.nanoseconds().without_bounds()
            + rhs.nanoseconds().without_bounds();
        if let Ok(nanoseconds) =
            t::FractionalNanosecond::try_rfrom("nanoseconds", nanoseconds)
        {
            return TimeDuration::new(seconds, nanoseconds);
        }
        let seconds = seconds.without_bounds();
        let [delta_seconds, delta_nanos] = t::NoUnits::vary_many(
            [seconds, nanoseconds],
            |[seconds, nanoseconds]| {
                if nanoseconds >= t::NANOS_PER_SECOND {
                    [C(1), (-t::NANOS_PER_SECOND).rinto()]
                } else if nanoseconds <= -t::NANOS_PER_SECOND {
                    [C(-1), t::NANOS_PER_SECOND.rinto()]
                } else {
                    [C(0), C(0)]
                }
            },
        );
        let mut seconds = t::SpanSeconds::rfrom(seconds);
        let mut nanoseconds = t::FractionalNanosecond::rfrom(nanoseconds);
        seconds += delta_seconds;
        nanoseconds += delta_nanos;
        TimeDuration::new(seconds, nanoseconds)
    }
}

impl AddAssign for TimeDuration {
    #[inline]
    fn add_assign(&mut self, rhs: TimeDuration) {
        *self = *self + rhs;
    }
}

impl Sub for TimeDuration {
    type Output = TimeDuration;

    #[inline]
    fn sub(self, rhs: TimeDuration) -> Self {
        self.add(-rhs)
    }
}

impl SubAssign for TimeDuration {
    #[inline]
    fn sub_assign(&mut self, rhs: TimeDuration) {
        *self = *self - rhs;
    }
}

impl<N: RInto<t::NoUnits>> Mul<N> for TimeDuration {
    type Output = TimeDuration;

    #[inline]
    fn mul(self, rhs: N) -> Self {
        let rhs = rhs.rinto();
        let mut seconds = self.seconds() * rhs;
        let nanoseconds = self.nanoseconds().without_bounds() * rhs;
        let add_seconds = nanoseconds.div_ceil(t::NANOS_PER_SECOND);
        seconds += add_seconds;
        let nanoseconds = t::FractionalNanosecond::rfrom(
            nanoseconds.rem_ceil(t::NANOS_PER_SECOND),
        );
        TimeDuration { seconds, nanoseconds }
    }
}

impl core::fmt::Debug for TimeDuration {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        let minus = if self.signum() >= 0 { "" } else { "-" };
        if self.nanoseconds == 0 {
            write!(f, "{minus}{:?}s", self.seconds.abs().debug())
        } else {
            write!(
                f,
                "{minus}{:?}s{:?}ns",
                self.seconds.abs().debug(),
                self.nanoseconds.abs().debug(),
            )
        }
    }
}

#[cfg(test)]
impl quickcheck::Arbitrary for TimeDuration {
    fn arbitrary(g: &mut quickcheck::Gen) -> TimeDuration {
        let seconds = t::SpanSeconds::arbitrary(g);
        let nanoseconds = t::FractionalNanosecond::arbitrary(g);
        TimeDuration::new(seconds, nanoseconds)
    }

    fn shrink(&self) -> alloc::boxed::Box<dyn Iterator<Item = Self>> {
        alloc::boxed::Box::new((self.seconds, self.nanoseconds).shrink().map(
            |(seconds, nanoseconds)| TimeDuration { seconds, nanoseconds },
        ))
    }
}

#[cfg(test)]
mod tests {
    use crate::ToSpan;

    use super::*;

    fn span_to_time_duration(span: Span) -> Result<(i64, i32), Error> {
        TimeDuration::from_span(&span).map(|d| d.to_parts())
    }

    #[test]
    fn from_span() {
        let d = |span| span_to_time_duration(span).unwrap();

        assert_eq!((1, 0), d(Span::new().seconds(1)));
        assert_eq!((1, 1), d(Span::new().seconds(1).nanoseconds(1)));
        assert_eq!(
            (2, 0),
            d(Span::new().seconds(1).nanoseconds(1_000_000_000))
        );
        assert_eq!(
            (t::SpanSeconds::MAX_REPR, 0),
            d(Span::new().hours(t::SpanHours::MAX_REPR))
        );
        assert_eq!(
            (t::SpanSeconds::MAX_REPR, 999_999_999),
            d(Span::new()
                .hours(t::SpanHours::MAX_REPR)
                .nanoseconds(999_999_999))
        );
        assert_eq!((1, 1_000_000), d(Span::new().milliseconds(1_001)));
        assert_eq!((1, 1_000), d(Span::new().microseconds(1_000_001)));
        assert_eq!(
            (2, 1_001_000),
            d(Span::new().milliseconds(1_001).microseconds(1_000_001))
        );
        assert_eq!(
            (3, 1_001_001),
            d(Span::new()
                .milliseconds(1_001)
                .microseconds(1_000_001)
                .nanoseconds(1_000_000_001))
        );
        assert_eq!(
            (0, 123_456_789),
            d(Span::new()
                .milliseconds(123)
                .microseconds(456)
                .nanoseconds(789))
        );
        assert_eq!(
            (1, 0),
            d(Span::new()
                .milliseconds(900)
                .microseconds(50_000)
                .nanoseconds(50_000_000)),
        );

        // Negative spans.
        assert_eq!((-3, -400), d(Span::new().nanoseconds(-3_000_000_400i64)));

        // Error cases where the `Span` represents a period of time that cannot
        // be represented by a `TimeDuration`.
        let d = |span| span_to_time_duration(span);
        assert!(
            d(Span::new().hours(t::SpanHours::MAX_REPR).minutes(1)).is_err()
        );
        assert!(
            d(Span::new().hours(t::SpanHours::MAX_REPR).seconds(1)).is_err()
        );
        assert!(d(Span::new()
            .hours(t::SpanHours::MAX_REPR)
            .nanoseconds(1_000_000_000))
        .is_err());
    }

    #[test]
    fn checked_add() {
        let add = |(s1, n1), (s2, n2)| {
            let d1 = TimeDuration::try_new(s1, n1).unwrap();
            let d2 = TimeDuration::try_new(s2, n2).unwrap();
            d1.checked_add(d2)
                .map(|d3| (d3.seconds().get(), d3.nanoseconds().get()))
        };
        assert_eq!((0, 0), add((0, 0), (0, 0)).unwrap());
        assert_eq!((3, 999_999_999), add((1, 999_999_998), (2, 1)).unwrap());
        assert_eq!((4, 0), add((1, 999_999_999), (2, 1)).unwrap());
        assert_eq!(
            (4, 999999998),
            add((1, 999_999_999), (2, 999_999_999)).unwrap(),
        );
        assert_eq!(
            (t::SpanSeconds::MAX_REPR, 0),
            add((t::SpanSeconds::MAX_REPR, 0), (0, 0)).unwrap(),
        );
        assert_eq!(
            (t::SpanSeconds::MAX_REPR, 999_999_999),
            add((t::SpanSeconds::MAX_REPR, 0), (0, 999_999_999)).unwrap(),
        );

        // Tests with negatives.
        assert_eq!((2, 0), add((3, 0), (-1, 0)).unwrap());
        // e.g., The nanos are being ADDED here. But if the -1 means the
        // duration is overall negative, then they should be subtracted.
        assert_eq!((1, 1), add((3, 0), (-1, -999_999_999)).unwrap());
        assert_eq!((-7, -5_000), add((3, 0), (-10, -5_000)).unwrap());
        assert_eq!(
            (-6, -999_999_000),
            add((3, 6_000), (-10, -5_000)).unwrap(),
        );

        // Error cases where addition results in a duration that is too big.
        assert!(add((t::SpanSeconds::MAX_REPR, 0), (1, 0)).is_err());
        assert!(add((t::SpanSeconds::MAX_REPR, 1), (0, 999_999_999)).is_err());
        assert!(add(
            (t::SpanSeconds::MAX_REPR, 0),
            (t::SpanSeconds::MAX_REPR, 0)
        )
        .is_err());
    }

    #[test]
    fn add() {
        let add = |(s1, n1), (s2, n2)| {
            let d1 = TimeDuration::new(C(s1), C(n1));
            let d2 = TimeDuration::new(C(s2), C(n2));
            (d1 + d2).to_parts()
        };
        assert_eq!((0, 0), add((0, 0), (0, 0)));
        assert_eq!((3, 999_999_999), add((1, 999_999_998), (2, 1)));
        assert_eq!((4, 0), add((1, 999_999_999), (2, 1)));
        assert_eq!((4, 999999998), add((1, 999_999_999), (2, 999_999_999)));
        assert_eq!(
            (t::SpanSeconds::MAX_REPR, 0),
            add((t::SpanSeconds::MAX_REPR, 0), (0, 0))
        );
        assert_eq!(
            (t::SpanSeconds::MAX_REPR, 999_999_999),
            add((t::SpanSeconds::MAX_REPR, 0), (0, 999_999_999))
        );

        // Tests with negatives.
        assert_eq!((2, 0), add((3, 0), (-1, 0)));
        // e.g., The nanos are being ADDED here. But if the -1 means the
        // duration is overall negative, then they should be subtracted.
        assert_eq!((1, 1), add((3, 0), (-1, -999_999_999)));
        assert_eq!((-7, -5_000), add((3, 0), (-10, -5_000)));
        assert_eq!((-6, -999_999_000), add((3, 6_000), (-10, -5_000)));
    }

    #[test]
    fn checked_sub() {
        let sub = |(s1, n1), (s2, n2)| {
            let d1 = TimeDuration::try_new(s1, n1).unwrap();
            let d2 = TimeDuration::try_new(s2, n2).unwrap();
            d1.checked_sub(d2)
                .map(|d3| (d3.seconds().get(), d3.nanoseconds.get()))
        };
        assert_eq!((0, 0), sub((0, 0), (0, 0)).unwrap());
        assert_eq!((2, 0), sub((5, 0), (3, 0)).unwrap());
        assert_eq!((2, 400), sub((5, 1_000), (3, 600)).unwrap());
        assert_eq!((1, 999_999_900), sub((5, 1_000), (3, 1_100)).unwrap());
        assert_eq!((0, -3), sub((1, 999_999_998), (2, 1)).unwrap());
    }

    #[test]
    fn sub() {
        let sub = |(s1, n1), (s2, n2)| {
            let d1 = TimeDuration::new(C(s1), C(n1));
            let d2 = TimeDuration::new(C(s2), C(n2));
            (d1 - d2).to_parts()
        };
        assert_eq!((0, 0), sub((0, 0), (0, 0)));
        assert_eq!((2, 0), sub((5, 0), (3, 0)));
        assert_eq!((2, 400), sub((5, 1_000), (3, 600)));
        assert_eq!((1, 999_999_900), sub((5, 1_000), (3, 1_100)));
        assert_eq!((0, -3), sub((1, 999_999_998), (2, 1)));
    }

    #[test]
    fn new() {
        let t = TimeDuration::try_new(1, -1).unwrap();
        assert_eq!(t.to_parts(), (0, 999_999_999));

        let t = TimeDuration::try_new(-1, 1).unwrap();
        assert_eq!(t.to_parts(), (0, -999_999_999));

        let t = TimeDuration::try_new(1, 1).unwrap();
        assert_eq!(t.to_parts(), (1, 1));

        let t = TimeDuration::try_new(-1, -1).unwrap();
        assert_eq!(t.to_parts(), (-1, -1));

        let t = TimeDuration::try_new(0, 1).unwrap();
        assert_eq!(t.to_parts(), (0, 1));

        let t = TimeDuration::try_new(0, -1).unwrap();
        assert_eq!(t.to_parts(), (0, -1));

        let t = TimeDuration::try_new(1, 0).unwrap();
        assert_eq!(t.to_parts(), (1, 0));

        let t = TimeDuration::try_new(-1, 0).unwrap();
        assert_eq!(t.to_parts(), (-1, 0));

        let t = TimeDuration::try_new(1, -999_999_999).unwrap();
        assert_eq!(t.to_parts(), (0, 1));

        let t = TimeDuration::try_new(-1, 999_999_999).unwrap();
        assert_eq!(t.to_parts(), (0, -1));

        let t = TimeDuration::try_new(1, 999_999_999).unwrap();
        assert_eq!(t.to_parts(), (1, 999_999_999));

        let t = TimeDuration::try_new(-1, -999_999_999).unwrap();
        assert_eq!(t.to_parts(), (-1, -999_999_999));

        let t = TimeDuration::new(
            t::SpanSeconds::MAX_SELF,
            t::FractionalNanosecond::MIN_SELF,
        );
        assert_eq!(t.to_parts(), (t::SpanSeconds::MAX_REPR - 1, 1));

        let t = TimeDuration::new(
            t::SpanSeconds::MAX_SELF,
            t::FractionalNanosecond::MAX_SELF,
        );
        assert_eq!(t.to_parts(), (t::SpanSeconds::MAX_REPR, 999_999_999));

        let t = TimeDuration::new(
            t::SpanSeconds::MIN_SELF,
            t::FractionalNanosecond::MIN_SELF,
        );
        assert_eq!(t.to_parts(), (t::SpanSeconds::MIN_REPR, -999_999_999));

        let t = TimeDuration::new(
            t::SpanSeconds::MIN_SELF,
            t::FractionalNanosecond::MAX_SELF,
        );
        assert_eq!(t.to_parts(), (t::SpanSeconds::MIN_REPR + 1, -1));
    }

    #[test]
    fn mul() {
        let td = TimeDuration::new(C(5), C(400_000_000));
        let got = td * C(2);
        assert_eq!(got.to_parts(), (10, 800_000_000));

        let td = TimeDuration::new(C(5), C(400_000_000));
        let got = td * C(3);
        assert_eq!(got.to_parts(), (16, 200_000_000));

        let td = TimeDuration::new(C(-5), C(-400_000_000));
        let got = td * C(2);
        assert_eq!(got.to_parts(), (-10, -800_000_000));

        let td = TimeDuration::new(C(-5), C(-400_000_000));
        let got = td * C(3);
        assert_eq!(got.to_parts(), (-16, -200_000_000));

        let td = TimeDuration::new(C(5), C(400_000_000));
        let got = td * C(-2);
        assert_eq!(got.to_parts(), (-10, -800_000_000));

        let td = TimeDuration::new(C(5), C(400_000_000));
        let got = td * C(-3);
        assert_eq!(got.to_parts(), (-16, -200_000_000));

        let td = TimeDuration::new(C(-5), C(-400_000_000));
        let got = td * C(-2);
        assert_eq!(got.to_parts(), (10, 800_000_000));

        let td = TimeDuration::new(C(-5), C(-400_000_000));
        let got = td * C(-3);
        assert_eq!(got.to_parts(), (16, 200_000_000));
    }

    #[test]
    fn checked_mul() {
        let td = TimeDuration::try_new(5, 400_000_000).unwrap();
        let got = td.checked_mul(t::NoUnits::new(2).unwrap()).unwrap();
        assert_eq!(got.to_parts(), (10, 800_000_000));

        let td = TimeDuration::try_new(5, 400_000_000).unwrap();
        let got = td.checked_mul(t::NoUnits::new(3).unwrap()).unwrap();
        assert_eq!(got.to_parts(), (16, 200_000_000));

        let td = TimeDuration::try_new(-5, -400_000_000).unwrap();
        let got = td.checked_mul(t::NoUnits::new(2).unwrap()).unwrap();
        assert_eq!(got.to_parts(), (-10, -800_000_000));

        let td = TimeDuration::try_new(-5, -400_000_000).unwrap();
        let got = td.checked_mul(t::NoUnits::new(3).unwrap()).unwrap();
        assert_eq!(got.to_parts(), (-16, -200_000_000));

        let td = TimeDuration::try_new(5, 400_000_000).unwrap();
        let got = td.checked_mul(t::NoUnits::new(-2).unwrap()).unwrap();
        assert_eq!(got.to_parts(), (-10, -800_000_000));

        let td = TimeDuration::try_new(5, 400_000_000).unwrap();
        let got = td.checked_mul(t::NoUnits::new(-3).unwrap()).unwrap();
        assert_eq!(got.to_parts(), (-16, -200_000_000));

        let td = TimeDuration::try_new(-5, -400_000_000).unwrap();
        let got = td.checked_mul(t::NoUnits::new(-2).unwrap()).unwrap();
        assert_eq!(got.to_parts(), (10, 800_000_000));

        let td = TimeDuration::try_new(-5, -400_000_000).unwrap();
        let got = td.checked_mul(t::NoUnits::new(-3).unwrap()).unwrap();
        assert_eq!(got.to_parts(), (16, 200_000_000));
    }

    quickcheck::quickcheck! {
        fn prop_roundtrip_nanoseconds(td: TimeDuration) -> bool {
            let nanos = td.to_nanoseconds();
            let got = TimeDuration::from_nanoseconds(nanos).unwrap();
            td == got
        }
    }
}
