use crate::{
    civil,
    error::{err, Error},
    round::{Round, Unit},
    span::{Span, TimeDuration},
    tz::{self, Offset, TimeZone},
    util::{
        rangeint::{self, ri64, RFrom, RInto, TryRFrom},
        t::{
            self, CivilDayNanosecond, FractionalNanosecond, NoUnits,
            NoUnits128, SpanSeconds, SubsecNanosecond, UnixEpochDays,
            UnixSeconds, C,
        },
    },
    zoned::Zoned,
};

use self::private::{Nanoseconds, Seconds};

// BREADCRUMBS: If we assume the maximum timezone offset is 86_400 seconds, then
// we can restrict all `Instant` values to be 86_400 seconds smaller than the
// max (or bigger than the min) of civil::DateTime. If we do that, then we
// can guaranteed that all Zoned -> DateTime conversions are infallible. Of
// course, the reverse won't be true, but that seems okay. It seems better to
// be able to guarantee the ability to get a "calendar date" from an instant
// than it does to get an instant from a calendar date.
//
// Otherwise, fill out the civil::DateTime type and then i think we can start
// looking at timezones. Sheeeeeeit. I could fill out Instant first, but I feel
// like it's too inter-connected with Zoned and I'd rather wait. Otherwise the
// examples will likely suffer.
//
// We're still missing duration rounding... but I think we should land timezone
// support first? Otherwise I'm going to have to implement it for civil-only
// times, and then redo some chunk of it with timezone-aware logic. Kind of a
// bummer.
//
// OK, so I got the time-zone offset restriction working, but I stumbled into
// a pretty obvious gaffe in the implementation of Instant pretty quickly: a
// TimeDuration (very intentionally) supports a much greater range than what
// UnixSeconds does. This is a problem when you want to do checked arithmetic.
// This is a bit of a bummer because TimeDuration is kind of a tricky type.
// But it's looking like the simplest thing to do is to just re-implement the
// bits we need here. Some bits on TimeDuration aren't needed here, which is
// nice.

#[derive(Clone, Copy)]
pub struct Instant<S: TimeScale = Unix> {
    scale: core::marker::PhantomData<S>,
    second: S::Seconds,
    nanosecond: FractionalNanosecond,
}

impl Instant {
    pub const UNIX_EPOCH: Instant = Instant {
        scale: core::marker::PhantomData,
        second: UnixSeconds::N::<0>(),
        nanosecond: FractionalNanosecond::N::<0>(),
    };

    pub const MIN: Instant = Instant {
        scale: core::marker::PhantomData,
        second: UnixSeconds::MIN_SELF,
        nanosecond: FractionalNanosecond::N::<0>(),
    };

    pub const MAX: Instant = Instant {
        scale: core::marker::PhantomData,
        second: UnixSeconds::MAX_SELF,
        nanosecond: FractionalNanosecond::MAX_SELF,
    };

    /// Returns the current Unix time.
    ///
    /// # Panics
    ///
    /// This panics if the system clock is set to a time value outside of the
    /// range `-9999-01-01T00:00:00Z..=9999-12-31T11:59:59.999999999Z`. The
    /// justification here is that it is reasonable to expect the system clock
    /// to be set to a somewhat sane, if imprecise, value.
    ///
    /// If you want to get the current Unix time fallibly, use
    /// [`Instant::now_with_scale`] with the [`Unix`] time scale.
    #[cfg(feature = "std")]
    pub fn now() -> Instant {
        Instant::now_with_scale().expect("system time reports valid value")
    }

    pub fn from_unix(
        unix_time_seconds: i64,
        unix_time_nanoseconds: i32,
    ) -> Result<Instant, Error> {
        Instant::from_unix_with_scale(unix_time_seconds, unix_time_nanoseconds)
    }

    #[cfg(feature = "std")]
    pub fn from_unix_duration(
        duration: std::time::Duration,
        sign: i32,
    ) -> Result<Instant, Error> {
        Instant::from_unix_duration_with_scale(duration, sign)
    }
}

impl<S: TimeScale> Instant<S> {
    pub fn to_zoned(
        self,
        iana_time_zone_name: &str,
    ) -> Result<Zoned<S>, Error> {
        let tz = tz::db().get(iana_time_zone_name)?;
        Ok(self.to_zoned_with(tz))
    }

    pub fn to_zoned_with(self, tz: TimeZone) -> Zoned<S> {
        Zoned::new(self, tz)
    }

    pub fn to_datetime(self) -> civil::DateTime {
        self.to_datetime_with_offset(Offset::ZERO)
    }

    pub(crate) fn to_datetime_with_offset(
        self,
        offset: Offset,
    ) -> civil::DateTime {
        let is_leap_second = self.is_leap_second();
        let inst = self
            .add_duration(offset.to_time_duration())
            .expect("offset span is always limited to time components");
        let (mut second, nanosecond) = inst.to_unix_ranged();
        // When we have a leap second, we collapse it backwards as if it were
        // 23:59:59. Later, we'll fixup the resulting `civil::Time` value to
        // be 23:59:60.
        if is_leap_second {
            second = second.saturating_sub(C(1));
        }
        // This is a little tricky. The day, second and nanosecond can all be
        // shifted when nanoseconds are themselves negative. Since all three
        // can vary, we need to shove them into a single `NoUnits::vary_many`
        // closure to make range arithmetic work correctly. We convert them
        // back to their proper units afterwards.
        let day = second.without_bounds().div_floor(t::SECONDS_PER_CIVIL_DAY);
        let second: NoUnits =
            second.without_bounds().rem_floor(t::SECONDS_PER_CIVIL_DAY);
        let nanosecond = nanosecond.without_bounds();
        let [delta_day, delta_second, delta_nanosecond] = NoUnits::vary_many(
            [day, second, nanosecond],
            |[day, second, nanosecond]| {
                if nanosecond >= 0 {
                    [C(0), C(0), C(0)]
                } else if second > 0 {
                    [C(0), C(-1), t::NANOS_PER_SECOND.rinto()]
                } else {
                    [
                        C(-1),
                        t::SECONDS_PER_CIVIL_DAY - C(1),
                        t::NANOS_PER_SECOND.rinto(),
                    ]
                }
            },
        );

        // Given the ranges on UnixSeconds and FractionalNanoseconds, it is
        // technically possible that the subtraction on `day` here could
        // overflow. But! This can only happen when the Unix second is its
        // minimal/maximal value, *and* the number of nanoseconds is non-zero.
        // That case is specifically rejected when constructing a `Instant`
        // value, so it is correct to assert that the overflow can never
        // happen.
        let day = UnixEpochDays::rfrom(day)
            .try_checked_add("day", delta_day)
            .unwrap();
        let second = (second + delta_second) * t::NANOS_PER_SECOND;
        let nanosecond = nanosecond + delta_nanosecond;
        let civil_day_nanosecond = second + nanosecond;
        let date = civil::Date::from_unix_epoch_days(day);
        let mut time =
            civil::Time::from_civil_nanosecond(civil_day_nanosecond);
        if is_leap_second {
            let next_second = time
                .utc_second_ranged()
                .checked_add(C(1))
                .unwrap_or(t::UtcSecond::MIN_SELF);
            time = time.with_second_ranged(next_second);
        }
        civil::DateTime::from_parts(date, time)
    }

    pub fn to_date(self) -> civil::Date {
        let (second, _) = self.to_unix_ranged();
        let days = second.div_floor(t::SECONDS_PER_CIVIL_DAY);
        let date = civil::Date::from_unix_epoch_days(days);
        date
    }

    pub fn from_datetime(dt: civil::DateTime) -> Result<Instant<S>, Error> {
        Instant::from_datetime_zulu(dt)
    }

    pub(crate) fn from_datetime_zulu(
        dt: civil::DateTime,
    ) -> Result<Instant<S>, Error> {
        let td = datetime_zulu_to_time_duration(dt);
        let unix_second =
            UnixSeconds::try_rfrom("instant-seconds", td.seconds())?;
        let second =
            S::from_unix_timestamp(unix_second, dt.time().is_leap_second())?;
        let nanosecond = td.nanoseconds();
        Ok(Instant { scale: core::marker::PhantomData, second, nanosecond })
    }

    pub fn since(self, other: Instant<S>) -> Span {
        self.until(other).negate()
    }

    pub(crate) fn since_with_largest_unit(
        self,
        largest: Unit,
        mut other: Instant<S>,
    ) -> Result<Span, Error> {
        Ok(-self.until_with_largest_unit(largest, other)?)
    }

    pub fn until(self, other: Instant<S>) -> Span {
        // This is OK because `Unit::Second` is valid to use here and because
        // all possible intervals between any two instants can fit into a span
        // whose largest unit is seconds.
        self.until_with_largest_unit(Unit::Second, other)
            .expect("all second intervals between instants fit in a span")
    }

    pub(crate) fn until_with_largest_unit(
        self,
        largest: Unit,
        mut other: Instant<S>,
    ) -> Result<Span, Error> {
        if largest >= Unit::Day {
            return Err(err!(
                "unit {largest} is not supported when computing the \
                 difference between instants (must use units smaller \
                 than 'day')",
                largest = largest.singular(),
            ));
        }
        let nanos1 = self.as_nanosecond_ranged().to_no_units();
        let nanos2 = other.as_nanosecond_ranged().to_no_units();
        let diff = nanos2 - nanos1;
        // This can fail when `largest` is nanoseconds since not all intervals
        // can be represented by a single i64 in units of nanoseconds.
        Span::from_invariant_nanoseconds(largest, diff)
    }

    pub fn checked_add(self, span: Span) -> Result<Instant<S>, Error> {
        // TODO: Audit the error returned here when the span contains units
        // greater than hours.
        let span_time = span.time_parts_to_duration()?;
        self.checked_add_time_duration(span_time)
    }

    pub fn checked_sub(self, span: Span) -> Result<Instant<S>, Error> {
        self.checked_add(span.negate())
    }

    pub fn second(self) -> i64 {
        self.second_ranged().get()
    }

    pub fn nanosecond(self) -> i32 {
        self.nanosecond_ranged().get()
    }

    pub fn as_nanosecond(self) -> i128 {
        self.as_nanosecond_ranged().get()
    }
}

impl<S: TimeScale> Instant<S> {
    #[cfg(feature = "std")]
    pub fn now_with_scale() -> Result<Instant<S>, Error> {
        std::time::SystemTime::now().try_into()
    }

    #[cfg(feature = "std")]
    pub fn from_unix_duration_with_scale(
        duration: std::time::Duration,
        sign: i32,
    ) -> Result<Instant<S>, Error> {
        let seconds = i64::try_from(duration.as_secs()).map_err(|_| {
            Error::unsigned(
                "duration seconds",
                duration.as_secs(),
                UnixSeconds::MIN_REPR,
                UnixSeconds::MAX_REPR,
            )
        })?;
        let nanos = i32::try_from(duration.subsec_nanos())
            .expect("nanoseconds in duration are less than 1,000,000,000");
        // NOTE: Can multiplication actually fail here? I think if `seconds` is
        // `i64::MIN`? But, no, I don't think so. Since `duration` is always
        // positive.
        Instant::from_unix_with_scale(seconds * i64::from(sign), nanos)
    }

    pub fn from_unix_with_scale(
        unix_time_seconds: i64,
        unix_time_nanoseconds: i32,
    ) -> Result<Instant<S>, Error> {
        if unix_time_nanoseconds != 0
            && unix_time_seconds == UnixSeconds::MIN_REPR
        {
            return Err(Error::signed(
                "unix seconds and nanoseconds",
                unix_time_nanoseconds,
                0,
                0,
            ));
        }
        Instant::from_unix_ranged(
            UnixSeconds::try_new("unix time seconds", unix_time_seconds)?,
            FractionalNanosecond::try_new(
                "unix time nanoseconds",
                unix_time_nanoseconds,
            )?,
        )
    }

    pub fn from_timestamp(
        second: i64,
        nanosecond: i32,
    ) -> Result<Instant<S>, Error> {
        if nanosecond != 0 && second == S::Seconds::min_repr() {
            return Err(Error::signed(
                "timestamp seconds and nanoseconds",
                nanosecond,
                0,
                0,
            ));
        }
        let second = S::Seconds::new("timestamp second", second)?;
        let nanosecond =
            FractionalNanosecond::try_new("timestamp nanosecond", nanosecond)?;
        Ok(Instant::from_timestamp_ranged(second, nanosecond))
    }

    pub fn from_nanosecond(nanosecond: i128) -> Result<Instant<S>, Error> {
        let nanosecond =
            S::Nanoseconds::new("nanosecond timestamp", nanosecond)?;
        Ok(Instant::from_nanosecond_ranged(nanosecond))
    }

    pub fn to_unix(&self) -> (i64, i32) {
        let (seconds, nanos) = self.to_unix_ranged();
        (seconds.get(), nanos.get())
    }

    #[cfg(feature = "std")]
    pub fn to_unix_duration(&self) -> (std::time::Duration, i32) {
        let (seconds, nanos) = self.to_unix();
        let (seconds, sign) = match u64::try_from(seconds) {
            Ok(seconds) => (seconds, if seconds == 0 { 0 } else { 1 }),
            Err(_) => {
                let seconds = u64::try_from(seconds.abs())
                    .expect("absolute value of seconds fits in u64");
                (seconds, -1)
            }
        };
        let nanos = u32::try_from(nanos.abs())
            .expect("nanoseconds always fit in a u32");
        (std::time::Duration::new(seconds, nanos), sign)
    }

    pub fn to_unix_scale(self) -> Instant {
        let (second, _) = S::to_unix_timestamp(self.second_ranged());
        Instant {
            scale: core::marker::PhantomData,
            second,
            nanosecond: self.nanosecond_ranged(),
        }
    }

    pub fn convert<T: TimeScale>(self) -> Result<Instant<T>, Error> {
        let (unix_second, is_leap_second) =
            S::to_unix_timestamp(self.second_ranged());
        let second = T::from_unix_timestamp(unix_second, is_leap_second)?;
        Ok(Instant {
            scale: core::marker::PhantomData,
            second,
            nanosecond: self.nanosecond_ranged(),
        })
    }

    pub fn is_leap_second(self) -> bool {
        S::is_leap_second(self.second_ranged())
    }

    /// # Example
    ///
    /// ```
    /// use jiff::{
    ///     civil::DateTime,
    ///     round::{RoundMode, Unit},
    ///     Instant,
    ///     TimeZone,
    /// };
    ///
    /// let dt = DateTime::constant(2019, 3, 30, 2, 45, 59, 999_999_999);
    /// let instant: Instant = dt.to_zoned_with(TimeZone::UTC)?.to_instant();
    ///
    /// let rounded = instant.round(Unit::Second);
    /// assert_eq!(
    ///     rounded.to_datetime(),
    ///     DateTime::constant(2019, 3, 30, 2, 46, 0, 0),
    /// );
    ///
    /// let rounded = instant.round(Unit::Minute.increment(60));
    /// assert_eq!(
    ///     rounded.to_datetime(),
    ///     DateTime::constant(2019, 3, 30, 3, 0, 0, 0),
    /// );
    ///
    /// let rounded = instant.round(
    ///     Unit::Minute.increment(60).mode(RoundMode::Floor)
    /// );
    /// assert_eq!(
    ///     rounded.to_datetime(),
    ///     DateTime::constant(2019, 3, 30, 2, 0, 0, 0),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn round(self, options: impl Into<Round>) -> Instant<S> {
        self.try_round(options).expect("invalid round options")
    }

    #[inline]
    pub fn try_round(
        self,
        options: impl Into<Round>,
    ) -> Result<Instant<S>, Error> {
        options.into().round_instant(self)
    }
}

impl<S: TimeScale> Instant<S> {
    pub(crate) fn from_datetime_zulu_ranged(
        dt: civil::DateTime,
    ) -> Result<Instant<S>, Error> {
        let td = datetime_zulu_to_time_duration(dt);
        let unix_second = UnixSeconds::rfrom(td.seconds());
        let second =
            S::from_unix_timestamp(unix_second, dt.time().is_leap_second())?;
        let nanosecond = td.nanoseconds();
        Ok(Instant { scale: core::marker::PhantomData, second, nanosecond })
    }

    pub(crate) fn checked_add_time_duration(
        self,
        duration: TimeDuration,
    ) -> Result<Instant<S>, Error> {
        Instant::from_time_duration_checked(
            self.to_time_duration().checked_add(duration)?,
        )
    }

    pub(crate) fn checked_sub_time_duration(
        self,
        duration: TimeDuration,
    ) -> Result<Instant<S>, Error> {
        Instant::from_time_duration_checked(
            self.to_time_duration().checked_sub(duration)?,
        )
    }

    pub(crate) fn add_duration(
        self,
        duration: TimeDuration,
    ) -> Result<Instant<S>, Error> {
        Ok(Instant::from_time_duration(self.to_time_duration() + duration))
    }

    pub(crate) fn sub_duration(
        self,
        duration: TimeDuration,
    ) -> Result<Instant<S>, Error> {
        self.add_duration(-duration)
    }

    pub(crate) fn to_unix_ranged(
        &self,
    ) -> (UnixSeconds, FractionalNanosecond) {
        let (second, _) = S::to_unix_timestamp(self.second_ranged());
        (second, self.nanosecond_ranged())
    }

    pub(crate) fn from_unix_ranged(
        unix_time_seconds: impl RInto<UnixSeconds>,
        unix_time_nanoseconds: impl RInto<FractionalNanosecond>,
    ) -> Result<Instant<S>, Error> {
        let unix_time_seconds = unix_time_seconds.rinto();
        let unix_time_nanoseconds = unix_time_nanoseconds.rinto();
        // TODO: The comment below seems wrong now. Audit it.
        //
        // This is a little cheesy since it's technically possible for a caller
        // to provide a minimal UnixSeconds value with a non-zero number of
        // nanoseconds (which would overflow `Instant`). But this is a not a
        // public routine and, in practice, civil datetimes cannot represent
        // invalid `Instant` values. So it should be impossible to see an
        // invalid pair of seconds and nanoseconds here. But we debug_assert it
        // to make it explicit.
        debug_assert!(
            unix_time_nanoseconds == 0
                || UnixSeconds::MIN_SELF < unix_time_seconds,
            "unix time must have zero nanoseconds at \
             minimum second boundary",
        );
        // We convert to a time duration first because it normalizes the
        // seconds and nanoseconds units. e.g., when given `-1s 1ns`, it will
        // correctly change that to `-999,999,999ns`.
        let duration =
            TimeDuration::new(unix_time_seconds, unix_time_nanoseconds);
        let second =
            S::from_unix_timestamp(duration.seconds().rinto(), false)?;
        let nanosecond = duration.nanoseconds();
        Ok(Instant { scale: core::marker::PhantomData, second, nanosecond })
    }

    pub(crate) fn from_timestamp_ranged(
        second: S::Seconds,
        nanosecond: impl RInto<FractionalNanosecond>,
    ) -> Instant<S> {
        let nanosecond = nanosecond.rinto();
        Instant { scale: core::marker::PhantomData, second, nanosecond }
    }

    pub(crate) fn from_nanosecond_ranged(
        nanosecond: S::Nanoseconds,
    ) -> Instant<S> {
        let nanosecond = nanosecond.to_no_units();
        let second = S::Seconds::from_no_units(
            nanosecond.div_ceil(t::NANOS_PER_SECOND).rinto(),
        );
        let nanosecond = nanosecond.rem_ceil(t::NANOS_PER_SECOND);
        Instant::from_timestamp_ranged(second, nanosecond)
    }

    fn to_time_duration(self) -> TimeDuration {
        TimeDuration::new(
            self.second_ranged().to_span_seconds(),
            self.nanosecond_ranged(),
        )
    }

    fn from_time_duration(duration: TimeDuration) -> Instant<S> {
        let second = S::Seconds::from_span_seconds(duration.seconds());
        let nanosecond = duration.nanoseconds();
        Instant { scale: core::marker::PhantomData, second, nanosecond }
    }

    fn from_time_duration_checked(
        duration: TimeDuration,
    ) -> Result<Instant<S>, Error> {
        let second = S::Seconds::try_from_span_seconds(duration.seconds())?;
        let nanosecond = duration.nanoseconds();
        Ok(Instant { scale: core::marker::PhantomData, second, nanosecond })
    }

    pub(crate) fn second_ranged(self) -> S::Seconds {
        self.second
    }

    pub(crate) fn nanosecond_ranged(self) -> FractionalNanosecond {
        self.nanosecond
    }

    pub(crate) fn as_nanosecond_ranged(self) -> S::Nanoseconds {
        let second = NoUnits128::rfrom(self.second_ranged().to_no_units());
        let nanosecond = NoUnits128::rfrom(self.nanosecond_ranged());
        // The minimum value of an instant has the fractional nanosecond set
        // to 0, but otherwise its minimum value is -999_999_999. So to avoid
        // a case where we return a ranged integer with a minimum value less
        // than the actual minimum, we clamp the fractional part to 0 when the
        // second value is the minimum.
        let [second, nanosecond] = NoUnits128::vary_many(
            [second, nanosecond],
            |[second, nanosecond]| {
                if second == S::Seconds::min_repr() {
                    [second, C(0).rinto()]
                } else {
                    [second, nanosecond]
                }
            },
        );
        S::Nanoseconds::from_no_units(
            second * t::NANOS_PER_SECOND + nanosecond,
        )
    }
}

impl<S: TimeScale> Default for Instant<S> {
    fn default() -> Instant<S> {
        Instant::from_timestamp_ranged(S::Seconds::N::<0>(), C(0))
    }
}

impl<S> core::fmt::Debug for Instant<S>
where
    S: TimeScale + core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("Instant")
            .field("scale", &S::name())
            .field("second", &self.second_ranged())
            .field("nanosecond", &self.nanosecond_ranged())
            .finish()
    }
}

impl<S: TimeScale> core::fmt::Display for Instant<S> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        use crate::format::{temporal::DateTimePrinter, FmtWrite};

        static P: DateTimePrinter = DateTimePrinter::new();
        // Printing to `f` should never fail.
        Ok(P.print_instant(self, FmtWrite(f)).unwrap())
    }
}

impl<S: TimeScale> Eq for Instant<S> {}

impl<S: TimeScale> PartialEq for Instant<S> {
    fn eq(&self, rhs: &Instant<S>) -> bool {
        self.second_ranged().get() == rhs.second_ranged().get()
            && self.nanosecond_ranged().get() == rhs.nanosecond_ranged().get()
    }
}

impl<S: TimeScale> Ord for Instant<S> {
    fn cmp(&self, rhs: &Instant<S>) -> core::cmp::Ordering {
        (self.second_ranged().get(), self.nanosecond_ranged().get())
            .cmp(&(rhs.second_ranged().get(), rhs.nanosecond_ranged().get()))
    }
}

impl<S: TimeScale> PartialOrd for Instant<S> {
    fn partial_cmp(&self, rhs: &Instant<S>) -> Option<core::cmp::Ordering> {
        Some(self.cmp(rhs))
    }
}

#[cfg(feature = "std")]
impl<S: TimeScale> TryFrom<std::time::SystemTime> for Instant<S> {
    type Error = Error;

    fn try_from(
        system_time: std::time::SystemTime,
    ) -> Result<Instant<S>, Error> {
        let unix_epoch = std::time::SystemTime::UNIX_EPOCH;
        let (duration, sign) = match system_time.duration_since(unix_epoch) {
            Ok(duration) => (duration, 1),
            Err(err) => (err.duration(), -1),
        };
        Instant::from_unix_duration_with_scale(duration, sign)
    }
}

#[cfg(feature = "std")]
impl<S: TimeScale> From<Instant<S>> for std::time::SystemTime {
    fn from(time: Instant<S>) -> std::time::SystemTime {
        let unix_epoch = std::time::SystemTime::UNIX_EPOCH;
        let (duration, sign) = time.to_unix_duration();
        // These are guaranteed to succeed because we assume that SystemTime
        // uses at least 64 bits for the time, and our durations are capped via
        // the range on UnixSeconds.
        if sign >= 0 {
            unix_epoch
                .checked_add(duration)
                .expect("duration too big (positive)")
        } else {
            unix_epoch
                .checked_sub(duration)
                .expect("duration too big (negative)")
        }
    }
}

#[cfg(test)]
impl<S: TimeScale + 'static> quickcheck::Arbitrary for Instant<S> {
    fn arbitrary(g: &mut quickcheck::Gen) -> Instant<S> {
        use quickcheck::Arbitrary;

        let seconds: UnixSeconds = Arbitrary::arbitrary(g);
        let mut nanoseconds: FractionalNanosecond = Arbitrary::arbitrary(g);
        // nanoseconds must be zero for the minimum second value,
        // so just clamp it to 0.
        if seconds == UnixSeconds::MIN_REPR {
            nanoseconds = C(0).rinto();
        }
        Instant::from_unix_ranged(seconds, nanoseconds).unwrap_or_default()
    }

    fn shrink(&self) -> alloc::boxed::Box<dyn Iterator<Item = Self>> {
        let (seconds, nanoseconds) = self.to_unix_ranged();
        alloc::boxed::Box::new((seconds, nanoseconds).shrink().filter_map(
            |(seconds, nanoseconds)| {
                if seconds == UnixSeconds::MIN_REPR && nanoseconds > 0 {
                    None
                } else {
                    Instant::from_unix_ranged(seconds, nanoseconds).ok()
                }
            },
        ))
    }
}

pub trait TimeScale: private::TimeScaleInternal {}
impl<S: private::TimeScaleInternal> TimeScale for S {}

#[derive(Clone, Copy, Debug, Default)]
pub struct Unix;

#[derive(Clone, Copy, Debug, Default)]
pub struct Tai;

pub(crate) mod private {
    use core::{
        fmt::Debug,
        ops::{Add, Div, Mul, Rem, Sub},
    };

    use crate::{
        error::Error,
        util::{
            rangeint::{ri64, RFrom, RInto, RangedDebug, TryRFrom},
            t::{
                FractionalNanosecond, NoUnits, NoUnits128, SpanSeconds,
                SubsecNanosecond, TaiNanoseconds, TaiSeconds, UnixNanoseconds,
                UnixSeconds,
            },
        },
    };

    pub(crate) trait TimeScaleInternal: Clone + Copy + Debug {
        type Seconds: Seconds;
        type Nanoseconds: Nanoseconds;

        fn name() -> &'static str;

        fn from_unix_timestamp(
            unix_second: UnixSeconds,
            is_leap_second: bool,
        ) -> Result<Self::Seconds, Error>;

        fn to_unix_timestamp(
            scale_second: Self::Seconds,
        ) -> (UnixSeconds, bool);

        fn is_leap_second(scale_second: Self::Seconds) -> bool;
    }

    pub(crate) trait Seconds:
        Copy
        + Clone
        + Debug
        + Eq
        + PartialEq
        + PartialOrd
        + Ord
        + Add
        + Sub
        + Mul
        + Div
        + Rem
    {
        fn new(what: &'static str, val: i64) -> Result<Self, Error>;

        fn from_no_units(n: NoUnits) -> Self;

        #[allow(non_snake_case)]
        fn N<const VAL: i64>() -> Self;

        fn min_repr() -> i64;

        fn from_span_seconds(val: SpanSeconds) -> Self;

        fn try_from_span_seconds(val: SpanSeconds) -> Result<Self, Error>;

        fn to_span_seconds(self) -> SpanSeconds;

        fn get(self) -> i64;

        fn to_no_units(self) -> NoUnits;
    }

    pub(crate) trait Nanoseconds:
        Copy
        + Clone
        + Debug
        + Eq
        + PartialEq
        + PartialOrd
        + Ord
        + Add
        + Sub
        + Mul
        + Div
        + Rem
    {
        fn new(what: &'static str, val: i128) -> Result<Self, Error>;

        fn get(self) -> i128;

        fn from_no_units(n: NoUnits128) -> Self;

        fn to_no_units(self) -> NoUnits128;
    }

    impl TimeScaleInternal for super::Unix {
        type Seconds = UnixSeconds;
        type Nanoseconds = UnixNanoseconds;

        fn name() -> &'static str {
            "UNIX"
        }

        fn from_unix_timestamp(
            unix_second: UnixSeconds,
            _is_leap_second: bool,
        ) -> Result<UnixSeconds, Error> {
            Ok(unix_second)
        }

        fn to_unix_timestamp(unix_second: UnixSeconds) -> (UnixSeconds, bool) {
            (unix_second, false)
        }

        fn is_leap_second(_unix_second: UnixSeconds) -> bool {
            false
        }
    }

    impl TimeScaleInternal for super::Tai {
        type Seconds = TaiSeconds;
        type Nanoseconds = TaiNanoseconds;

        fn name() -> &'static str {
            "TAI"
        }

        fn from_unix_timestamp(
            unix_second: UnixSeconds,
            is_leap_second: bool,
        ) -> Result<TaiSeconds, Error> {
            let tai_second =
                crate::tz::db().unix_to_tai_timestamp(unix_second)?;
            if is_leap_second {
                tai_second.try_checked_sub("tai seconds", TaiSeconds::N::<1>())
            } else {
                Ok(tai_second)
            }
        }

        fn to_unix_timestamp(tai_second: TaiSeconds) -> (UnixSeconds, bool) {
            crate::tz::db().tai_to_unix_timestamp(tai_second)
        }

        fn is_leap_second(tai_second: TaiSeconds) -> bool {
            Self::to_unix_timestamp(tai_second).1
        }
    }

    impl Seconds for UnixSeconds {
        fn new(what: &'static str, val: i64) -> Result<Self, Error> {
            UnixSeconds::try_new(what, val)
        }

        fn from_no_units(n: NoUnits) -> Self {
            UnixSeconds::rfrom(n)
        }

        #[allow(non_snake_case)]
        fn N<const VAL: i64>() -> Self {
            UnixSeconds::N::<VAL>()
        }

        fn min_repr() -> i64 {
            UnixSeconds::MIN_REPR
        }

        fn from_span_seconds(val: SpanSeconds) -> Self {
            val.rinto()
        }

        fn try_from_span_seconds(val: SpanSeconds) -> Result<Self, Error> {
            UnixSeconds::try_rfrom("instant-seconds", val)
        }

        fn to_span_seconds(self) -> SpanSeconds {
            self.rinto()
        }

        fn get(self) -> i64 {
            UnixSeconds::get(self)
        }

        fn to_no_units(self) -> NoUnits {
            UnixSeconds::without_bounds(self)
        }
    }

    impl Nanoseconds for UnixNanoseconds {
        fn new(what: &'static str, val: i128) -> Result<Self, Error> {
            UnixNanoseconds::try_new128(what, val)
        }

        fn get(self) -> i128 {
            UnixNanoseconds::get(self)
        }

        fn from_no_units(n: NoUnits128) -> Self {
            UnixNanoseconds::rfrom(n)
        }

        fn to_no_units(self) -> NoUnits128 {
            UnixNanoseconds::without_bounds(self)
        }
    }

    impl Seconds for TaiSeconds {
        fn new(what: &'static str, val: i64) -> Result<Self, Error> {
            TaiSeconds::try_new(what, val)
        }

        fn from_no_units(n: NoUnits) -> Self {
            TaiSeconds::rfrom(n)
        }

        #[allow(non_snake_case)]
        fn N<const VAL: i64>() -> Self {
            TaiSeconds::N::<VAL>()
        }

        fn min_repr() -> i64 {
            TaiSeconds::MIN_REPR
        }

        fn from_span_seconds(val: SpanSeconds) -> Self {
            val.rinto()
        }

        fn try_from_span_seconds(val: SpanSeconds) -> Result<Self, Error> {
            TaiSeconds::try_rfrom("instant-seconds", val)
        }

        fn to_span_seconds(self) -> SpanSeconds {
            self.rinto()
        }

        fn get(self) -> i64 {
            TaiSeconds::get(self)
        }

        fn to_no_units(self) -> NoUnits {
            TaiSeconds::without_bounds(self)
        }
    }

    impl Nanoseconds for TaiNanoseconds {
        fn new(what: &'static str, val: i128) -> Result<Self, Error> {
            TaiNanoseconds::try_new128(what, val)
        }

        fn get(self) -> i128 {
            TaiNanoseconds::get(self)
        }

        fn from_no_units(n: NoUnits128) -> Self {
            TaiNanoseconds::rfrom(n)
        }

        fn to_no_units(self) -> NoUnits128 {
            TaiNanoseconds::without_bounds(self)
        }
    }
}

pub(crate) fn datetime_zulu_to_time_duration(
    dt: civil::DateTime,
) -> TimeDuration {
    let (date, time) = (dt.date(), dt.time());
    let day = date.to_unix_epoch_days().without_bounds();
    let mut civil_day_nanosecond = time.to_civil_nanosecond().without_bounds();
    // This makes it so, e.g., 23:59:60 and 00:00:00 correspond to the same
    // Unix timestamp. We need to add 1 second because converting a civil time
    // to a number of nanoseconds ignores the leap second by "rewinding" the
    // 23:59:60 time to 23:59:59.
    //
    // We could also remove this addition, and that would cause 23:59:60 to
    // be equivalent to the Unix time for 23:59:59 instead. I chose this
    // approach because it seems to match what POSIX-like systems actually
    // implement: https://en.wikipedia.org/wiki/Unix_time#Leap_seconds
    //
    // This also seems to line up with the Unix timestamps derived
    // from NTP timestamps in NIST's `leap-seconds.list`. For example,
    // 2015-06-30T23:59:60 is the leap second, and this addition causes its
    // Unix time to be 1435708800. That in turn also corresponds to the Unix
    // timestamp recorded for that leap second in our leap second data table.
    if time.is_leap_second() {
        civil_day_nanosecond += C(1_000_000_000);
    }
    let second = civil_day_nanosecond.div_floor(t::NANOS_PER_SECOND);
    let nanosecond = civil_day_nanosecond.rem_floor(t::NANOS_PER_SECOND);
    let [delta_day, delta_second, delta_nanosecond] = NoUnits::vary_many(
        [day, second, nanosecond],
        |[day, second, nanosecond]| {
            if day >= 0 || nanosecond == 0 {
                [C(0), C(0), C(0)]
            } else {
                [
                    C(1),
                    -(t::SECONDS_PER_CIVIL_DAY - C(1)),
                    (-t::NANOS_PER_SECOND).rinto(),
                ]
            }
        },
    );

    let day = day + delta_day;
    let second = day * t::SECONDS_PER_CIVIL_DAY + second + delta_second;
    let nanosecond = nanosecond + delta_nanosecond;
    TimeDuration::new(second, nanosecond)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mktime(seconds: i64, nanos: i32) -> Instant {
        Instant::from_unix(seconds, nanos).unwrap()
    }

    fn mkdt(
        year: i16,
        month: i8,
        day: i8,
        hour: i8,
        minute: i8,
        second: i8,
        nano: i32,
    ) -> civil::DateTime {
        let date = civil::Date::new(year, month, day).unwrap();
        let time = civil::Time::new(hour, minute, second)
            .unwrap()
            .with_subsec_nanosecond(nano)
            .unwrap();
        civil::DateTime::from_parts(date, time)
    }

    #[test]
    fn to_datetime_specific_examples() {
        let tests = [
            // ((UnixSeconds::MIN_REPR, 0), (-9999, 1, 2, 0, 59, 59, 0)),
            (
                (UnixSeconds::MIN_REPR + 1, -999_999_999),
                (-9999, 1, 2, 1, 59, 59, 1),
            ),
            ((-1, 1), (1969, 12, 31, 23, 59, 59, 1)),
            // ((UnixSeconds::MIN_REPR, 0), (-9999, 1, 1, 0, 0, 0, 0)),
            // ((UnixSeconds::MAX_REPR - 1, 0), (9999, 12, 31, 23, 59, 58, 0)),
            // (
            // (UnixSeconds::MAX_REPR - 1, 999_999_999),
            // (9999, 12, 31, 23, 59, 58, 999_999_999),
            // ),
            // ((UnixSeconds::MAX_REPR, 0), (9999, 12, 31, 23, 59, 59, 0)),
            // (
            // (UnixSeconds::MAX_REPR, 999_999_999),
            // (9999, 12, 31, 23, 59, 59, 999_999_999),
            // ),
            // ((-2, -1), (1969, 12, 31, 23, 59, 57, 999_999_999)),
            // ((-86398, -1), (1969, 12, 31, 0, 0, 1, 999_999_999)),
            // ((-86399, -1), (1969, 12, 31, 0, 0, 0, 999_999_999)),
            // ((-86400, -1), (1969, 12, 30, 23, 59, 59, 999_999_999)),
        ];
        for (t, dt) in tests {
            let instant = mktime(t.0, t.1);
            let datetime = mkdt(dt.0, dt.1, dt.2, dt.3, dt.4, dt.5, dt.6);
            assert_eq!(instant.to_datetime(), datetime, "instant: {t:?}");
            assert_eq!(
                instant,
                datetime.to_zulu().unwrap(),
                "datetime: {datetime:?}"
            );
        }
    }

    #[test]
    fn to_datetime_every_second_in_some_days() {
        let days = [
            i64::from(UnixEpochDays::MIN_REPR),
            -1000,
            -5,
            23,
            2000,
            i64::from(UnixEpochDays::MAX_REPR),
        ];
        let nanos = [0, 1, 5, 999_999_999];
        for day in days {
            let midpoint = day * 86_400;
            let start = midpoint - 86_400;
            let end = midpoint + 86_400;
            for second in start..=end {
                if !UnixSeconds::contains(second) {
                    continue;
                }
                for nano in nanos {
                    if second == UnixSeconds::MIN_REPR && nano != 0 {
                        continue;
                    }
                    let t = Instant::from_unix(second, nano).unwrap();
                    let Ok(got) = t.to_datetime().to_zulu() else { continue };
                    assert_eq!(t, got);
                }
            }
        }
    }

    #[test]
    fn invalid_time() {
        assert!(Instant::from_unix(UnixSeconds::MIN_REPR, -1).is_err());
        assert!(Instant::from_unix(UnixSeconds::MIN_REPR, 1).is_err());
        assert!(
            Instant::from_unix(UnixSeconds::MIN_REPR, -999_999_999).is_err()
        );
        assert!(
            Instant::from_unix(UnixSeconds::MIN_REPR, 999_999_999).is_err()
        );
    }

    #[test]
    fn instant_size() {
        #[cfg(debug_assertions)]
        {
            assert_eq!(40, core::mem::size_of::<Instant>());
        }
        #[cfg(not(debug_assertions))]
        {
            assert_eq!(16, core::mem::size_of::<Instant>());
        }
    }

    #[test]
    fn nanosecond_roundtrip_boundaries() {
        let inst = Instant::MIN;
        let nanos = inst.as_nanosecond_ranged();
        assert_eq!(0, nanos % t::NANOS_PER_SECOND);
        let got = Instant::from_nanosecond_ranged(nanos);
        assert_eq!(inst, got);

        let inst = Instant::MAX;
        let nanos = inst.as_nanosecond_ranged();
        assert_eq!(
            FractionalNanosecond::MAX_SELF,
            nanos % t::NANOS_PER_SECOND
        );
        let got = Instant::from_nanosecond_ranged(nanos);
        assert_eq!(inst, got);
    }

    quickcheck::quickcheck! {
        fn prop_unix_seconds_roundtrip(t: Instant) -> quickcheck::TestResult {
            let dt = t.to_datetime();
            let Ok(got) = dt.to_zulu() else {
                return quickcheck::TestResult::discard();
            };
            quickcheck::TestResult::from_bool(t == got)
        }

        fn prop_nanos_roundtrip_unix_ranged(t: Instant) -> bool {
            let nanos = t.as_nanosecond_ranged();
            let got = Instant::from_nanosecond_ranged(nanos);
            t == got
        }

        fn prop_nanos_roundtrip_tai_ranged(t: Instant<Tai>) -> bool {
            let nanos = t.as_nanosecond_ranged();
            let got = Instant::from_nanosecond_ranged(nanos);
            t == got
        }

        fn prop_nanos_roundtrip_unix(t: Instant) -> bool {
            let nanos = t.as_nanosecond();
            let got = Instant::from_nanosecond(nanos).unwrap();
            t == got
        }

        fn prop_nanos_roundtrip_tai(t: Instant<Tai>) -> bool {
            let nanos = t.as_nanosecond();
            let got = Instant::from_nanosecond(nanos).unwrap();
            t == got
        }
    }
}
