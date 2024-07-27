use crate::{
    civil::{Date, DateTime},
    error::{err, Error},
    fmt::{
        self,
        temporal::{DEFAULT_DATETIME_PARSER, DEFAULT_DATETIME_PRINTER},
    },
    util::{
        rangeint::{RFrom, RInto},
        round::increment,
        t::{
            self, CivilDayNanosecond, Hour, Microsecond, Millisecond, Minute,
            Nanosecond, Second, SubsecNanosecond, C,
        },
    },
    RoundMode, Span, SpanRound, Unit, Zoned,
};

/// A representation of civil "wall clock" time.
///
/// Conceptually, a `Time` value corresponds to the typical hours and minutes
/// that you might see on a clock. This type also contains the second and
/// fractional subsecond (to nanosecond precision) associated with a time.
///
/// # Civil time
///
/// A `Time` value behaves as if it corresponds precisely to a single
/// nanosecond within a day, where all days have `86,400` seconds. That is,
/// any given `Time` value corresponds to a nanosecond in the inclusive range
/// `[0, 86399999999999]`, where `0` corresponds to `00:00:00.000000000`
/// ([`Time::MIN`]) and `86399999999999` corresponds to `23:59:59.999999999`
/// ([`Time::MAX`]). Moreover, in civil time, all hours have the same number of
/// minutes, all minutes have the same number of seconds and all seconds have
/// the same number of nanoseconds.
///
/// # Parsing and printing
///
/// The `Time` type provides convenient trait implementations of
/// [`std::str::FromStr`] and [`std::fmt::Display`]:
///
/// ```
/// use jiff::civil::Time;
///
/// let t: Time = "15:22:45".parse()?;
/// assert_eq!(t.to_string(), "15:22:45");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// A civil `Time` can also be parsed from something that _contains_ a
/// time, but with perhaps other data (such as an offset or time zone):
///
/// ```
/// use jiff::civil::Time;
///
/// let t: Time = "2024-06-19T15:22:45-04[America/New_York]".parse()?;
/// assert_eq!(t.to_string(), "15:22:45");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// For more information on the specific format supported, see the
/// [`fmt::temporal`](crate::fmt::temporal) module documentation.
///
/// # Default value
///
/// For convenience, this type implements the `Default` trait. Its default
/// value is midnight. i.e., `00:00:00.000000000`.
///
/// # Leap seconds
///
/// Jiff does not support leap seconds. Jiff behaves as if they don't exist.
/// The only exception is that if one parses a time with a second component
/// of `60`, then it is automatically constrained to `59`:
///
/// ```
/// use jiff::civil::Time;
///
/// let t: Time = "23:59:60".parse()?;
/// assert_eq!(t, Time::constant(23, 59, 59, 0));
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Comparisons
///
/// The `Time` type provides both `Eq` and `Ord` trait implementations to
/// facilitate easy comparisons. When a time `t1` occurs before a time `t2`,
/// then `t1 < t2`. For example:
///
/// ```
/// use jiff::civil::Time;
///
/// let t1 = Time::constant(7, 30, 1, 0);
/// let t2 = Time::constant(8, 10, 0, 0);
/// assert!(t1 < t2);
/// ```
///
/// As mentioned above, `Time` values are not associated with timezones, and
/// thus transitions such as DST are not taken into account when comparing
/// `Time` values.
///
/// # Arithmetic
///
/// This type provides routines for adding and subtracting spans of time, as
/// well as computing the span of time between two `Time` values.
///
/// For adding or subtracting spans of time, one can use any of the following
/// routines:
///
/// * [`Time::wrapping_add`] or [`Time::wrapping_sub`] for wrapping arithmetic.
/// * [`Time::checked_add`] or [`Time::checked_sub`] for checked arithmetic.
/// * [`Time::saturating_add`] or [`Time::saturating_sub`] for saturating
/// arithmetic.
///
/// Additionally, wrapping arithmetic is available via the `Add` and `Sub`
/// trait implementations:
///
/// ```
/// use jiff::{civil::Time, ToSpan};
///
/// let time = Time::constant(20, 10, 1, 0);
/// let span = 1.hours().minutes(49).seconds(59);
/// assert_eq!(time + span, Time::constant(22, 0, 0, 0));
///
/// // Overflow will result in wrap-around unless using checked
/// // arithmetic explicitly.
/// let time = Time::constant(23, 59, 59, 999_999_999);
/// assert_eq!(Time::constant(0, 0, 0, 0), time + 1.nanoseconds());
/// ```
///
/// Wrapping arithmetic is used by default because it corresponds to how clocks
/// showing the time of day behave in practice.
///
/// One can compute the span of time between two times using either
/// [`Time::until`] or [`Time::since`]. It's also possible to subtract two
/// `Time` values directly via a `Sub` trait implementation:
///
/// ```
/// use jiff::{civil::Time, ToSpan};
///
/// let time1 = Time::constant(22, 0, 0, 0);
/// let time2 = Time::constant(20, 10, 1, 0);
/// assert_eq!(time1 - time2, 1.hours().minutes(49).seconds(59));
/// ```
///
/// The `until` and `since` APIs are polymorphic and allow re-balancing and
/// rounding the span returned. For example, the default largest unit is hours
/// (as exemplified above), but we can ask for smaller units:
///
/// ```
/// use jiff::{civil::Time, ToSpan, Unit};
///
/// let time1 = Time::constant(23, 30, 0, 0);
/// let time2 = Time::constant(7, 0, 0, 0);
/// assert_eq!(
///     time1.since((Unit::Minute, time2))?,
///     990.minutes(),
/// );
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// Or even round the span returned:
///
/// ```
/// use jiff::{civil::{Time, TimeDifference}, RoundMode, ToSpan, Unit};
///
/// let time1 = Time::constant(23, 30, 0, 0);
/// let time2 = Time::constant(23, 35, 59, 0);
/// assert_eq!(
///     time1.until(
///         TimeDifference::new(time2).smallest(Unit::Minute),
///     )?,
///     5.minutes(),
/// );
/// // `TimeDifference` uses truncation as a rounding mode by default,
/// // but you can set the rounding mode to break ties away from zero:
/// assert_eq!(
///     time1.until(
///         TimeDifference::new(time2)
///             .smallest(Unit::Minute)
///             .mode(RoundMode::HalfExpand),
///     )?,
///     // Rounds up to 6 minutes.
///     6.minutes(),
/// );
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Rounding
///
/// A `Time` can be rounded based on a [`TimeRound`] configuration of smallest
/// units, rounding increment and rounding mode. Here's an example showing how
/// to round to the nearest third hour:
///
/// ```
/// use jiff::{civil::{Time, TimeRound}, Unit};
///
/// let t = Time::constant(16, 27, 29, 999_999_999);
/// assert_eq!(
///     t.round(TimeRound::new().smallest(Unit::Hour).increment(3))?,
///     Time::constant(15, 0, 0, 0),
/// );
/// // Or alternatively, make use of the `From<(Unit, i64)> for TimeRound`
/// // trait implementation:
/// assert_eq!(t.round((Unit::Hour, 3))?, Time::constant(15, 0, 0, 0));
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// See [`Time::round`] for more details.
#[derive(Clone, Copy, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct Time {
    hour: Hour,
    minute: Minute,
    second: Second,
    subsec_nanosecond: SubsecNanosecond,
}

impl Time {
    /// The minimum representable time value.
    ///
    /// This corresponds to `00:00:00.000000000`.
    pub const MIN: Time = Time::midnight();

    /// The maximum representable time value.
    ///
    /// This corresponds to `23:59:59.999999999`.
    pub const MAX: Time = Time::constant(23, 59, 59, 999_999_999);

    /// Creates a new `Time` value from its component hour, minute, second and
    /// fractional subsecond (up to nanosecond precision) values.
    ///
    /// To set the component values of a time after creating it, use
    /// [`TimeWith`] via [`Time::with`] to build a new [`Time`] from the fields
    /// of an existing time.
    ///
    /// # Errors
    ///
    /// This returns an error unless *all* of the following conditions are
    /// true:
    ///
    /// * `0 <= hour <= 23`
    /// * `0 <= minute <= 59`
    /// * `0 <= second <= 59`
    /// * `0 <= subsec_nanosecond <= 999,999,999`
    ///
    /// # Example
    ///
    /// This shows an example of a valid time:
    ///
    /// ```
    /// use jiff::civil::Time;
    ///
    /// let t = Time::new(21, 30, 5, 123_456_789).unwrap();
    /// assert_eq!(t.hour(), 21);
    /// assert_eq!(t.minute(), 30);
    /// assert_eq!(t.second(), 5);
    /// assert_eq!(t.millisecond(), 123);
    /// assert_eq!(t.microsecond(), 456);
    /// assert_eq!(t.nanosecond(), 789);
    /// ```
    ///
    /// This shows an example of an invalid time:
    ///
    /// ```
    /// use jiff::civil::Time;
    ///
    /// assert!(Time::new(21, 30, 60, 0).is_err());
    /// ```
    #[inline]
    pub fn new(
        hour: i8,
        minute: i8,
        second: i8,
        subsec_nanosecond: i32,
    ) -> Result<Time, Error> {
        let hour = Hour::try_new("hour", hour)?;
        let minute = Minute::try_new("minute", minute)?;
        let second = Second::try_new("second", second)?;
        let subsec_nanosecond =
            SubsecNanosecond::try_new("subsec_nanosecond", subsec_nanosecond)?;
        Ok(Time::new_ranged(hour, minute, second, subsec_nanosecond))
    }

    /// Creates a new `Time` value in a `const` context.
    ///
    /// # Panics
    ///
    /// This panics if the given values do not correspond to a valid `Time`.
    /// All of the following conditions must be true:
    ///
    /// * `0 <= hour <= 23`
    /// * `0 <= minute <= 59`
    /// * `0 <= second <= 59`
    /// * `0 <= subsec_nanosecond <= 999,999,999`
    ///
    /// Similarly, when used in a const context, invalid parameters will
    /// prevent your Rust program from compiling.
    ///
    /// # Example
    ///
    /// This shows an example of a valid time in a `const` context:
    ///
    /// ```
    /// use jiff::civil::Time;
    ///
    /// const BEDTIME: Time = Time::constant(21, 30, 5, 123_456_789);
    /// assert_eq!(BEDTIME.hour(), 21);
    /// assert_eq!(BEDTIME.minute(), 30);
    /// assert_eq!(BEDTIME.second(), 5);
    /// assert_eq!(BEDTIME.millisecond(), 123);
    /// assert_eq!(BEDTIME.microsecond(), 456);
    /// assert_eq!(BEDTIME.nanosecond(), 789);
    /// assert_eq!(BEDTIME.subsec_nanosecond(), 123_456_789);
    /// ```
    #[inline]
    pub const fn constant(
        hour: i8,
        minute: i8,
        second: i8,
        subsec_nanosecond: i32,
    ) -> Time {
        if !Hour::contains(hour) {
            panic!("invalid hour");
        }
        if !Minute::contains(minute) {
            panic!("invalid minute");
        }
        if !Second::contains(second) {
            panic!("invalid second");
        }
        if !SubsecNanosecond::contains(subsec_nanosecond) {
            panic!("invalid nanosecond");
        }
        let hour = Hour::new_unchecked(hour);
        let minute = Minute::new_unchecked(minute);
        let second = Second::new_unchecked(second);
        let subsec_nanosecond =
            SubsecNanosecond::new_unchecked(subsec_nanosecond);
        Time { hour, minute, second, subsec_nanosecond }
    }

    /// Returns the first moment of time in a day.
    ///
    /// Specifically, this has the `hour`, `minute`, `second`, `millisecond`,
    /// `microsecond` and `nanosecond` fields all set to `0`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::Time;
    ///
    /// let t = Time::midnight();
    /// assert_eq!(t.hour(), 0);
    /// assert_eq!(t.minute(), 0);
    /// assert_eq!(t.second(), 0);
    /// assert_eq!(t.millisecond(), 0);
    /// assert_eq!(t.microsecond(), 0);
    /// assert_eq!(t.nanosecond(), 0);
    /// ```
    #[inline]
    pub const fn midnight() -> Time {
        Time::constant(0, 0, 0, 0)
    }

    /// Create a builder for constructing a `Time` from the fields of this
    /// time.
    ///
    /// See the methods on [`TimeWith`] for the different ways one can set the
    /// fields of a new `Time`.
    ///
    /// # Example
    ///
    /// Unlike [`Date`], a [`Time`] is valid for all possible valid values
    /// of its fields. That is, there is no way for two valid field values
    /// to combine into an invalid `Time`. So, for `Time`, this builder does
    /// have as much of a benefit versus an API design with methods like
    /// `Time::with_hour` and `Time::with_minute`. Nevertheless, this builder
    /// permits settings multiple fields at the same time and performing only
    /// one validity check. Moreover, this provides a consistent API with other
    /// date and time types in this crate.
    ///
    /// ```
    /// use jiff::civil::time;
    ///
    /// let t1 = time(0, 0, 24, 0);
    /// let t2 = t1.with().hour(15).minute(30).millisecond(10).build()?;
    /// assert_eq!(t2, time(15, 30, 24, 10_000_000));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn with(self) -> TimeWith {
        TimeWith::new(self)
    }

    /// Returns the "hour" component of this time.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::Time;
    ///
    /// let t = Time::constant(13, 35, 56, 123_456_789);
    /// assert_eq!(t.hour(), 13);
    /// ```
    #[inline]
    pub fn hour(self) -> i8 {
        self.hour_ranged().get()
    }

    /// Returns the "minute" component of this time.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::Time;
    ///
    /// let t = Time::constant(13, 35, 56, 123_456_789);
    /// assert_eq!(t.minute(), 35);
    /// ```
    #[inline]
    pub fn minute(self) -> i8 {
        self.minute_ranged().get()
    }

    /// Returns the "second" component of this time.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::Time;
    ///
    /// let t = Time::constant(13, 35, 56, 123_456_789);
    /// assert_eq!(t.second(), 56);
    /// ```
    #[inline]
    pub fn second(self) -> i8 {
        self.second_ranged().get()
    }

    /// Returns the "millisecond" component of this time.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::Time;
    ///
    /// let t = Time::constant(13, 35, 56, 123_456_789);
    /// assert_eq!(t.millisecond(), 123);
    /// ```
    #[inline]
    pub fn millisecond(self) -> i16 {
        self.millisecond_ranged().get()
    }

    /// Returns the "microsecond" component of this time.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::Time;
    ///
    /// let t = Time::constant(13, 35, 56, 123_456_789);
    /// assert_eq!(t.microsecond(), 456);
    /// ```
    #[inline]
    pub fn microsecond(self) -> i16 {
        self.microsecond_ranged().get()
    }

    /// Returns the "nanosecond" component of this time.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::Time;
    ///
    /// let t = Time::constant(13, 35, 56, 123_456_789);
    /// assert_eq!(t.nanosecond(), 789);
    /// ```
    #[inline]
    pub fn nanosecond(self) -> i16 {
        self.nanosecond_ranged().get()
    }

    /// Returns the fractional nanosecond for this `Time` value.
    ///
    /// If you want to set this value on `Time`, then use
    /// [`TimeWith::subsec_nanosecond`] via [`Time::with`].
    ///
    /// # Example
    ///
    /// This shows the relationship between constructing a `Time` value
    /// with routines like `with().millisecond()` and accessing the entire
    /// fractional part as a nanosecond:
    ///
    /// ```
    /// use jiff::civil::time;
    ///
    /// let t = time(15, 21, 35, 0).with().millisecond(987).build()?;
    /// assert_eq!(t.subsec_nanosecond(), 987_000_000);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: nanoseconds from a timestamp
    ///
    /// This shows how the fractional nanosecond part of a `Time` value
    /// manifests from a specific timestamp.
    ///
    /// ```
    /// use jiff::{civil, Timestamp};
    ///
    /// // 1,234 nanoseconds after the Unix epoch.
    /// let zdt = Timestamp::new(0, 1_234)?.intz("UTC")?;
    /// let time = zdt.datetime().time();
    /// assert_eq!(time.subsec_nanosecond(), 1_234);
    ///
    /// // 1,234 nanoseconds before the Unix epoch.
    /// let zdt = Timestamp::new(0, -1_234)?.intz("UTC")?;
    /// let time = zdt.datetime().time();
    /// // The nanosecond is equal to `1_000_000_000 - 1_234`.
    /// assert_eq!(time.subsec_nanosecond(), 999998766);
    /// // Looking at the other components of the time value might help.
    /// assert_eq!(time.hour(), 23);
    /// assert_eq!(time.minute(), 59);
    /// assert_eq!(time.second(), 59);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn subsec_nanosecond(self) -> i32 {
        self.subsec_nanosecond_ranged().get()
    }

    /// Given a [`Date`], this constructs a [`DateTime`] value with its time
    /// component equal to this time.
    ///
    /// This is a convenience function for [`DateTime::from_parts`].
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::{DateTime, date, time};
    ///
    /// let d = date(2010, 3, 14);
    /// let t = time(2, 30, 0, 0);
    /// assert_eq!(DateTime::from_parts(d, t), t.to_datetime(d));
    /// ```
    #[inline]
    pub const fn to_datetime(self, date: Date) -> DateTime {
        DateTime::from_parts(date, self)
    }

    /// A convenience function for constructing a [`DateTime`] from this time
    /// on the date given by its components.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::time;
    ///
    /// assert_eq!(
    ///     time(2, 30, 0, 0).on(2010, 3, 14).to_string(),
    ///     "2010-03-14T02:30:00",
    /// );
    /// ```
    ///
    /// One can also flip the order by making use of [`Date::at`]:
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// assert_eq!(
    ///     date(2010, 3, 14).at(2, 30, 0, 0).to_string(),
    ///     "2010-03-14T02:30:00",
    /// );
    /// ```
    #[inline]
    pub const fn on(self, year: i16, month: i8, day: i8) -> DateTime {
        DateTime::from_parts(Date::constant(year, month, day), self)
    }

    /// Add the given span to this time and wrap around on overflow.
    ///
    /// # Properties
    ///
    /// Given times `t1` and `t2`, and a span `s`, with `t2 = t1 + s`, it
    /// follows then that `t1 = t2 - s` for all values of `t1` and `s` that sum
    /// to `t2`.
    ///
    /// In short, subtracting the given span from the sum returned by this
    /// function is guaranteed to result in precisely the original time.
    ///
    /// # Example: available via addition operator
    ///
    /// This routine can be used via the `+` operator.
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// let t = Time::constant(20, 10, 1, 0);
    /// assert_eq!(
    ///     t + 1.hours().minutes(49).seconds(59),
    ///     Time::constant(22, 0, 0, 0),
    /// );
    /// ```
    ///
    /// # Example: add nanoseconds to a `Time`
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// let t = Time::constant(22, 35, 1, 0);
    /// assert_eq!(
    ///     Time::constant(22, 35, 3, 500_000_000),
    ///     t.wrapping_add(2_500_000_000i64.nanoseconds()),
    /// );
    /// ```
    ///
    /// # Example: add span with multiple units
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// let t = Time::constant(20, 10, 1, 0);
    /// assert_eq!(
    ///     Time::constant(22, 0, 0, 0),
    ///     t.wrapping_add(1.hours().minutes(49).seconds(59)),
    /// );
    /// ```
    ///
    /// # Example: adding an empty span is a no-op
    ///
    /// ```
    /// use jiff::{civil::Time, Span};
    ///
    /// let t = Time::constant(20, 10, 1, 0);
    /// assert_eq!(t, t.wrapping_add(Span::new()));
    /// ```
    ///
    /// # Example: addition wraps on overflow
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// let t = Time::constant(23, 59, 59, 999_999_999);
    /// assert_eq!(Time::constant(0, 0, 0, 0), t.wrapping_add(1.nanoseconds()));
    /// ```
    ///
    /// Similarly, if there are any non-zero units greater than hours in the
    /// given span, then they also result in wrapping behavior (i.e., they are
    /// ignored):
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// // doesn't matter what our time value is in this example
    /// let t = Time::constant(0, 0, 0, 0);
    /// assert_eq!(t, t.wrapping_add(1.days()));
    /// ```
    #[inline]
    pub fn wrapping_add(self, span: Span) -> Time {
        let mut sum = self.to_nanosecond().without_bounds();
        sum = sum.wrapping_add(
            span.get_hours_ranged()
                .without_bounds()
                .wrapping_mul(t::NANOS_PER_HOUR),
        );
        sum = sum.wrapping_add(
            span.get_minutes_ranged()
                .without_bounds()
                .wrapping_mul(t::NANOS_PER_MINUTE),
        );
        sum = sum.wrapping_add(
            span.get_seconds_ranged()
                .without_bounds()
                .wrapping_mul(t::NANOS_PER_SECOND),
        );
        sum = sum.wrapping_add(
            span.get_milliseconds_ranged()
                .without_bounds()
                .wrapping_mul(t::NANOS_PER_MILLI),
        );
        sum = sum.wrapping_add(
            span.get_microseconds_ranged()
                .without_bounds()
                .wrapping_mul(t::NANOS_PER_MICRO),
        );
        sum = sum.wrapping_add(span.get_nanoseconds_ranged().without_bounds());
        let civil_day_nanosecond = sum % t::NANOS_PER_CIVIL_DAY;
        Time::from_nanosecond(civil_day_nanosecond)
    }

    /// Subtract the given span from this time and wrap around on overflow.
    ///
    /// # Properties
    ///
    /// Given times `t1` and `t2`, and a span `s`, with `t2 = t1 - s`, it
    /// follows then that `t1 = t2 + s` for all values of `t1` and `s` whose
    /// difference is `t2`.
    ///
    /// In short, adding the given span from the difference returned by this
    /// function is guaranteed to result in precisely the original time.
    ///
    /// # Example: available via subtraction operator
    ///
    /// This routine can be used via the `-` operator.
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// let t = Time::constant(22, 0, 0, 0);
    /// assert_eq!(
    ///     t - 1.hours().minutes(49).seconds(59),
    ///     Time::constant(20, 10, 1, 0),
    /// );
    /// ```
    ///
    /// # Example: subtract nanoseconds from a `Time`
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// let t = Time::constant(22, 35, 1, 0);
    /// assert_eq!(
    ///     Time::constant(22, 34, 58, 500_000_000),
    ///     t.wrapping_sub(2_500_000_000i64.nanoseconds()),
    /// );
    /// ```
    ///
    /// # Example: subtract span with multiple units
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// let t = Time::constant(22, 0, 0, 0);
    /// assert_eq!(
    ///     Time::constant(20, 10, 1, 0),
    ///     t.wrapping_sub(1.hours().minutes(49).seconds(59)),
    /// );
    /// ```
    ///
    /// # Example: addition wraps on overflow
    ///
    /// ```
    /// use jiff::{civil::Time, Span};
    ///
    /// let t = Time::constant(20, 10, 1, 0);
    /// assert_eq!(t, t.wrapping_sub(Span::new()));
    /// ```
    ///
    /// # Example: subtraction wraps on overflow
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// let t = Time::constant(0, 0, 0, 0);
    /// assert_eq!(
    ///     Time::constant(23, 59, 59, 999_999_999),
    ///     t.wrapping_sub(1.nanoseconds()),
    /// );
    /// ```
    ///
    /// Similarly, if there are any non-zero units greater than hours in the
    /// given span, then they also result in wrapping behavior (i.e., they are
    /// ignored):
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// // doesn't matter what our time value is in this example
    /// let t = Time::constant(23, 59, 59, 999_999_999);
    /// assert_eq!(t, t.wrapping_sub(1.days()));
    /// ```
    #[inline]
    pub fn wrapping_sub(self, span: Span) -> Time {
        self.wrapping_add(span.negate())
    }

    /// Add the given span to this time and return an error if the result would
    /// otherwise overflow.
    ///
    /// # Properties
    ///
    /// Given a time `t1` and a span `s`, and assuming `t2 = t1 + s` exists, it
    /// follows then that `t1 = t2 - s` for all values of `t1` and `s` that sum
    /// to a valid `t2`.
    ///
    /// In short, subtracting the given span from the sum returned by this
    /// function is guaranteed to result in precisely the original time.
    ///
    /// # Errors
    ///
    /// If the sum would overflow the minimum or maximum timestamp values, then
    /// an error is returned.
    ///
    /// If the given span has any non-zero units greater than hours, then an
    /// error is returned.
    ///
    /// # Example: add nanoseconds to a `Time`
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// let t = Time::constant(22, 35, 1, 0);
    /// assert_eq!(
    ///     Time::constant(22, 35, 3, 500_000_000),
    ///     t.checked_add(2_500_000_000i64.nanoseconds())?,
    /// );
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: add span with multiple units
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// let t = Time::constant(20, 10, 1, 0);
    /// assert_eq!(
    ///     Time::constant(22, 0, 0, 0),
    ///     t.checked_add(1.hours().minutes(49).seconds(59))?,
    /// );
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: adding an empty span is a no-op
    ///
    /// ```
    /// use jiff::{civil::Time, Span};
    ///
    /// let t = Time::constant(20, 10, 1, 0);
    /// assert_eq!(t, t.checked_add(Span::new())?);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: error on overflow
    ///
    /// ```
    /// use jiff::{civil::time, ToSpan};
    ///
    /// // okay
    /// let t = time(23, 59, 59, 999_999_998);
    /// assert_eq!(
    ///     t.with().nanosecond(999).build()?,
    ///     t.checked_add(1.nanoseconds())?,
    /// );
    ///
    /// // not okay
    /// let t = time(23, 59, 59, 999_999_999);
    /// assert!(t.checked_add(1.nanoseconds()).is_err());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// Similarly, if there are any non-zero units greater than hours in the
    /// given span, then they also result in overflow (and thus an error):
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// // doesn't matter what our time value is in this example
    /// let t = Time::constant(0, 0, 0, 0);
    /// assert!(t.checked_add(1.days()).is_err());
    /// ```
    #[inline]
    pub fn checked_add(self, span: Span) -> Result<Time, Error> {
        let (time, span) = self.overflowing_add(span)?;
        if let Some(err) = span.smallest_non_time_non_zero_unit_error() {
            return Err(err);
        }
        Ok(time)
    }

    /// Subtract the given span from this time and return an error if the
    /// result would otherwise overflow.
    ///
    /// # Properties
    ///
    /// Given a time `t1` and a span `s`, and assuming `t2 = t1 - s` exists, it
    /// follows then that `t1 = t2 + s` for all values of `t1` and `s` whose
    /// difference is a valid `t2`.
    ///
    /// In short, adding the given span from the difference returned by this
    /// function is guaranteed to result in precisely the original time.
    ///
    /// # Errors
    ///
    /// This returns an error in two cases:
    ///
    /// 1. When the given span's interval overflows the maximum allowed
    /// duration.
    /// 2. When subtracting the span to a time value would exceed the minimum
    /// allowed value (`00:00:00.000000000`). This also automatically happens
    /// whenever the given span has any non-zero values for units bigger than
    /// hours.
    ///
    /// # Example: subtract nanoseconds to a `Time`
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// let t = Time::constant(22, 35, 1, 0);
    /// assert_eq!(
    ///     Time::constant(22, 34, 58, 500_000_000),
    ///     t.checked_sub(2_500_000_000i64.nanoseconds())?,
    /// );
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: subtract span with multiple units
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// let t = Time::constant(22, 0, 0, 0);
    /// assert_eq!(
    ///     Time::constant(20, 10, 1, 0),
    ///     t.checked_sub(1.hours().minutes(49).seconds(59))?,
    /// );
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: subtracting an empty span is a no-op
    ///
    /// ```
    /// use jiff::{civil::Time, Span};
    ///
    /// let t = Time::constant(20, 10, 1, 0);
    /// assert_eq!(t, t.checked_sub(Span::new())?);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: error on overflow
    ///
    /// ```
    /// use jiff::{civil::time, ToSpan};
    ///
    /// // okay
    /// let t = time(0, 0, 0, 1);
    /// assert_eq!(
    ///     t.with().nanosecond(0).build()?,
    ///     t.checked_sub(1.nanoseconds())?,
    /// );
    ///
    /// // not okay
    /// let t = time(0, 0, 0, 0);
    /// assert!(t.checked_sub(1.nanoseconds()).is_err());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// Similarly, if there are any non-zero units greater than hours in the
    /// given span, then they also result in overflow (and thus an error):
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// // doesn't matter what our time value is in this example
    /// let t = Time::constant(23, 59, 59, 999_999_999);
    /// assert!(t.checked_sub(1.days()).is_err());
    /// ```
    #[inline]
    pub fn checked_sub(self, span: Span) -> Result<Time, Error> {
        self.checked_add(span.negate())
    }

    /// Add the given span to this time and saturate if the addition would
    /// otherwise overflow.
    ///
    /// # Example: add nanoseconds to a `Time`
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// let t = Time::constant(22, 35, 1, 0);
    /// assert_eq!(
    ///     Time::constant(22, 35, 3, 500_000_000),
    ///     t.saturating_add(2_500_000_000i64.nanoseconds()),
    /// );
    /// ```
    ///
    /// # Example: add span with multiple units
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// let t = Time::constant(20, 10, 1, 0);
    /// assert_eq!(
    ///     Time::constant(22, 0, 0, 0),
    ///     t.saturating_add(1.hours().minutes(49).seconds(59)),
    /// );
    /// ```
    ///
    /// # Example: adding an empty span is a no-op
    ///
    /// ```
    /// use jiff::{civil::Time, Span};
    ///
    /// let t = Time::constant(20, 10, 1, 0);
    /// assert_eq!(t, t.saturating_add(Span::new()));
    /// ```
    ///
    /// # Example: saturate on overflow
    ///
    /// ```
    /// use jiff::{civil::{Time, time}, ToSpan};
    ///
    /// // no saturation
    /// let t = time(23, 59, 59, 999_999_998);
    /// assert_eq!(
    ///     t.with().nanosecond(999).build()?,
    ///     t.saturating_add(1.nanoseconds()),
    /// );
    ///
    /// // saturates
    /// let t = time(23, 59, 59, 999_999_999);
    /// assert_eq!(Time::MAX, t.saturating_add(1.nanoseconds()));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// Similarly, if there are any non-zero units greater than hours in the
    /// given span, then they also result in overflow (and thus saturation):
    ///
    /// ```
    /// use jiff::{civil::{Time, time}, ToSpan};
    ///
    /// // doesn't matter what our time value is in this example
    /// let t = time(0, 0, 0, 0);
    /// assert_eq!(Time::MAX, t.saturating_add(1.days()));
    /// ```
    #[inline]
    pub fn saturating_add(self, span: Span) -> Time {
        self.checked_add(span).unwrap_or_else(|_| {
            if span.is_negative() {
                Time::MIN
            } else {
                Time::MAX
            }
        })
    }

    /// Subtract the given span from this time and saturate if the subtraction
    /// would otherwise overflow.
    ///
    /// # Example: subtract nanoseconds to a `Time`
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// let t = Time::constant(22, 35, 1, 0);
    /// assert_eq!(
    ///     Time::constant(22, 34, 58, 500_000_000),
    ///     t.saturating_sub(2_500_000_000i64.nanoseconds()),
    /// );
    /// ```
    ///
    /// # Example: subtract span with multiple units
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// let t = Time::constant(22, 0, 0, 0);
    /// assert_eq!(
    ///     Time::constant(20, 10, 1, 0),
    ///     t.saturating_sub(1.hours().minutes(49).seconds(59)),
    /// );
    /// ```
    ///
    /// # Example: subtracting an empty span is a no-op
    ///
    /// ```
    /// use jiff::{civil::Time, Span};
    ///
    /// let t = Time::constant(20, 10, 1, 0);
    /// assert_eq!(t, t.saturating_sub(Span::new()));
    /// ```
    ///
    /// # Example: saturate on overflow
    ///
    /// ```
    /// use jiff::{civil::{Time, time}, ToSpan};
    ///
    /// // no saturation
    /// let t = time(0, 0, 0, 1);
    /// assert_eq!(
    ///     t.with().nanosecond(0).build()?,
    ///     t.saturating_sub(1.nanoseconds()),
    /// );
    ///
    /// // saturates
    /// let t = time(0, 0, 0, 0);
    /// assert_eq!(Time::MIN, t.saturating_sub(1.nanoseconds()));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// Similarly, if there are any non-zero units greater than hours in the
    /// given span, then they also result in overflow (and thus saturation):
    ///
    /// ```
    /// use jiff::{civil::{Time, time}, ToSpan};
    ///
    /// // doesn't matter what our time value is in this example
    /// let t = time(23, 59, 59, 999_999_999);
    /// assert_eq!(Time::MIN, t.saturating_sub(1.days()));
    /// ```
    #[inline]
    pub fn saturating_sub(self, span: Span) -> Time {
        self.saturating_add(span.negate())
    }

    /// Adds the given span to the this time value, and returns the resulting
    /// time with any overflowing amount in the span returned.
    ///
    /// This isn't part of the public API because it seems a little odd, and
    /// I'm unsure of its use case. Overall this routine is a bit specialized
    /// and I'm not sure how generally useful it is. But it is used in crucial
    /// points in other parts of this crate.
    ///
    /// If you want this public, please file an issue and discuss your use
    /// case: https://github.com/BurntSushi/jiff/issues/new
    #[inline]
    pub(crate) fn overflowing_add(
        self,
        span: Span,
    ) -> Result<(Time, Span), Error> {
        if let Some(err) = span.smallest_non_time_non_zero_unit_error() {
            return Err(err);
        }
        let span_nanos = span.to_invariant_nanoseconds();
        let time_nanos = self.to_nanosecond();
        let sum = span_nanos + time_nanos;
        let days = t::SpanDays::try_new(
            "overflowing-days",
            sum.div_floor(t::NANOS_PER_CIVIL_DAY),
        )?;
        let time_nanos = sum.rem_floor(t::NANOS_PER_CIVIL_DAY);
        let time = Time::from_nanosecond(time_nanos);
        Ok((time, Span::new().days_ranged(days)))
    }

    /// Returns a span representing the elapsed time from this time since
    /// the given `other` time.
    ///
    /// When `other` is later than this time, the span returned will be
    /// negative.
    ///
    /// Depending on the input provided, the span returned is rounded. It may
    /// also be balanced down to smaller units than the default. By default,
    /// the span returned is balanced such that the biggest possible unit is
    /// hours.
    ///
    /// This operation is configured by providing a [`TimeDifference`]
    /// value. Since this routine accepts anything that implements
    /// `Into<TimeDifference>`, once can pass a `Time` directly. One
    /// can also pass a `(Unit, Time)`, where `Unit` is treated as
    /// [`TimeDifference::largest`].
    ///
    /// # Properties
    ///
    /// As long as no rounding is requested, it is guaranteed that adding the
    /// span returned to the `other` time will always equal this time.
    ///
    /// # Errors
    ///
    /// An error can occur if `TimeDifference` is misconfigured. For example,
    /// if the smallest unit provided is bigger than the largest unit. Or if
    /// a unit greater than `Unit::Hour` is provided.
    ///
    /// It is guaranteed that if one provides a time with the default
    /// [`TimeDifference`] configuration, then this routine will never fail.
    ///
    /// # Examples
    ///
    /// ```
    /// # // See: https://github.com/rust-lang/rust/pull/121364
    /// # #![allow(unknown_lints, ambiguous_negative_literals)]
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// let t1 = Time::constant(22, 35, 1, 0);
    /// let t2 = Time::constant(22, 35, 3, 500_000_000);
    /// assert_eq!(t2.since(t1)?, 2.seconds().milliseconds(500));
    /// // Flipping the dates is fine, but you'll get a negative span.
    /// assert_eq!(t1.since(t2)?, -2.seconds().milliseconds(500));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: available via subtraction operator
    ///
    /// This routine can be used via the `-` operator. Since the default
    /// configuration is used and because a `Span` can represent the difference
    /// between any two possible times, it will never panic.
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// let earlier = Time::constant(1, 0, 0, 0);
    /// let later = Time::constant(22, 30, 0, 0);
    /// assert_eq!(later - earlier, 21.hours().minutes(30));
    /// ```
    ///
    /// # Example: using smaller units
    ///
    /// This example shows how to contract the span returned to smaller units.
    /// This makes use of a `From<(Unit, Time)> for TimeDifference`
    /// trait implementation.
    ///
    /// ```
    /// use jiff::{civil::Time, Unit, ToSpan};
    ///
    /// let t1 = Time::constant(3, 24, 30, 3500);
    /// let t2 = Time::constant(15, 30, 0, 0);
    ///
    /// // The default limits spans to using "hours" as the biggest unit.
    /// let span = t2.since(t1)?;
    /// assert_eq!(span.to_string(), "PT12h5m29.9999965s");
    ///
    /// // But we can ask for smaller units, like capping the biggest unit
    /// // to minutes instead of hours.
    /// let span = t2.since((Unit::Minute, t1))?;
    /// assert_eq!(span.to_string(), "PT725m29.9999965s");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn since<A: Into<TimeDifference>>(
        self,
        other: A,
    ) -> Result<Span, Error> {
        let args: TimeDifference = other.into();
        let span = -args.until_with_largest_unit(self)?;
        if args.rounding_may_change_span() {
            span.round(args.round)
        } else {
            Ok(span)
        }
    }

    /// Returns a span representing the elapsed time from this time until
    /// the given `other` time.
    ///
    /// When `other` is earlier than this time, the span returned will be
    /// negative.
    ///
    /// Depending on the input provided, the span returned is rounded. It may
    /// also be balanced down to smaller units than the default. By default,
    /// the span returned is balanced such that the biggest possible unit is
    /// hours.
    ///
    /// This operation is configured by providing a [`TimeDifference`]
    /// value. Since this routine accepts anything that implements
    /// `Into<TimeDifference>`, once can pass a `Time` directly. One
    /// can also pass a `(Unit, Time)`, where `Unit` is treated as
    /// [`TimeDifference::largest`].
    ///
    /// # Properties
    ///
    /// As long as no rounding is requested, it is guaranteed that adding the
    /// span returned to the `other` time will always equal this time.
    ///
    /// # Examples
    ///
    /// ```
    /// # // See: https://github.com/rust-lang/rust/pull/121364
    /// # #![allow(unknown_lints, ambiguous_negative_literals)]
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// let t1 = Time::constant(22, 35, 1, 0);
    /// let t2 = Time::constant(22, 35, 3, 500_000_000);
    /// assert_eq!(t1.until(t2)?, 2.seconds().milliseconds(500));
    /// // Flipping the dates is fine, but you'll get a negative span.
    /// assert_eq!(t2.until(t1)?, -2.seconds().milliseconds(500));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: using smaller units
    ///
    /// This example shows how to contract the span returned to smaller units.
    /// This makes use of a `From<(Unit, Time)> for TimeDifference`
    /// trait implementation.
    ///
    /// ```
    /// use jiff::{civil::Time, Unit, ToSpan};
    ///
    /// let t1 = Time::constant(3, 24, 30, 3500);
    /// let t2 = Time::constant(15, 30, 0, 0);
    ///
    /// // The default limits spans to using "hours" as the biggest unit.
    /// let span = t1.until(t2)?;
    /// assert_eq!(span.to_string(), "PT12h5m29.9999965s");
    ///
    /// // But we can ask for smaller units, like capping the biggest unit
    /// // to minutes instead of hours.
    /// let span = t1.until((Unit::Minute, t2))?;
    /// assert_eq!(span.to_string(), "PT725m29.9999965s");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn until<A: Into<TimeDifference>>(
        self,
        other: A,
    ) -> Result<Span, Error> {
        let args: TimeDifference = other.into();
        let span = args.until_with_largest_unit(self)?;
        if args.rounding_may_change_span() {
            span.round(args.round)
        } else {
            Ok(span)
        }
    }

    /// Rounds this time according to the [`TimeRound`] configuration given.
    ///
    /// The principal option is [`TimeRound::smallest`], which allows one
    /// to configure the smallest units in the returned time. Rounding
    /// is what determines whether that unit should keep its current value
    /// or whether it should be incremented. Moreover, the amount it should
    /// be incremented can be configured via [`TimeRound::increment`].
    /// Finally, the rounding strategy itself can be configured via
    /// [`TimeRound::mode`].
    ///
    /// Note that this routine is generic and accepts anything that
    /// implements `Into<TimeRound>`. Some notable implementations are:
    ///
    /// * `From<Unit> for Round`, which will automatically create a
    /// `TimeRound::new().smallest(unit)` from the unit provided.
    /// * `From<(Unit, i64)> for Round`, which will automatically create a
    /// `TimeRound::new().smallest(unit).increment(number)` from the unit
    /// and increment provided.
    ///
    /// # Errors
    ///
    /// This returns an error if the smallest unit configured on the given
    /// [`TimeRound`] is bigger than hours.
    ///
    /// The rounding increment must divide evenly into the next highest unit
    /// after the smallest unit configured (and must not be equivalent to it).
    /// For example, if the smallest unit is [`Unit::Nanosecond`], then *some*
    /// of the valid values for the rounding increment are `1`, `2`, `4`, `5`,
    /// `100` and `500`. Namely, any integer that divides evenly into `1,000`
    /// nanoseconds since there are `1,000` nanoseconds in the next highest
    /// unit (microseconds).
    ///
    /// This can never fail because of overflow for any input. The only
    /// possible errors are "configuration" errors.
    ///
    /// # Example
    ///
    /// This is a basic example that demonstrates rounding a datetime to the
    /// nearest second. This also demonstrates calling this method with the
    /// smallest unit directly, instead of constructing a `TimeRound` manually.
    ///
    /// ```
    /// use jiff::{civil::Time, Unit};
    ///
    /// let t = Time::constant(15, 45, 10, 123_456_789);
    /// assert_eq!(
    ///     t.round(Unit::Second)?,
    ///     Time::constant(15, 45, 10, 0),
    /// );
    /// let t = Time::constant(15, 45, 10, 500_000_001);
    /// assert_eq!(
    ///     t.round(Unit::Second)?,
    ///     Time::constant(15, 45, 11, 0),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: changing the rounding mode
    ///
    /// The default rounding mode is [`RoundMode::HalfExpand`], which
    /// breaks ties by rounding away from zero. But other modes like
    /// [`RoundMode::Trunc`] can be used too:
    ///
    /// ```
    /// use jiff::{civil::{Time, TimeRound}, RoundMode, Unit};
    ///
    /// let t = Time::constant(15, 45, 10, 999_999_999);
    /// assert_eq!(
    ///     t.round(Unit::Second)?,
    ///     Time::constant(15, 45, 11, 0),
    /// );
    /// // The default will round up to the next second for any fraction
    /// // greater than or equal to 0.5. But truncation will always round
    /// // toward zero.
    /// assert_eq!(
    ///     t.round(
    ///         TimeRound::new().smallest(Unit::Second).mode(RoundMode::Trunc),
    ///     )?,
    ///     Time::constant(15, 45, 10, 0),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: rounding to the nearest 5 minute increment
    ///
    /// ```
    /// use jiff::{civil::Time, Unit};
    ///
    /// // rounds down
    /// let t = Time::constant(15, 27, 29, 999_999_999);
    /// assert_eq!(t.round((Unit::Minute, 5))?, Time::constant(15, 25, 0, 0));
    /// // rounds up
    /// let t = Time::constant(15, 27, 30, 0);
    /// assert_eq!(t.round((Unit::Minute, 5))?, Time::constant(15, 30, 0, 0));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: rounding wraps around on overflow
    ///
    /// This example demonstrates that it's possible for this operation to
    /// overflow, and as a result, have the time wrap around.
    ///
    /// ```
    /// use jiff::{civil::Time, Unit};
    ///
    /// let t = Time::MAX;
    /// assert_eq!(t.round(Unit::Hour)?, Time::MIN);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn round(self, options: impl Into<TimeRound>) -> Result<Time, Error> {
        let options: TimeRound = options.into();
        options.round(self)
    }

    /// Return an iterator of periodic times determined by the given span.
    ///
    /// The given span may be negative, in which case, the iterator will move
    /// backwards through time. The iterator won't stop until either the span
    /// itself overflows, or it would otherwise exceed the minimum or maximum
    /// `Time` value.
    ///
    /// # Example: visiting every third hour
    ///
    /// This shows how to visit each third hour of a 24 hour time interval:
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// let start = Time::MIN;
    /// let mut every_third_hour = vec![];
    /// for time in start.series(3.hours()) {
    ///     every_third_hour.push(time);
    /// }
    /// assert_eq!(every_third_hour, vec![
    ///     Time::constant(0, 0, 0, 0),
    ///     Time::constant(3, 0, 0, 0),
    ///     Time::constant(6, 0, 0, 0),
    ///     Time::constant(9, 0, 0, 0),
    ///     Time::constant(12, 0, 0, 0),
    ///     Time::constant(15, 0, 0, 0),
    ///     Time::constant(18, 0, 0, 0),
    ///     Time::constant(21, 0, 0, 0),
    /// ]);
    /// ```
    ///
    /// Or go backwards every 6.5 hours:
    ///
    /// ```
    /// # // See: https://github.com/rust-lang/rust/pull/121364
    /// # #![allow(unknown_lints, ambiguous_negative_literals)]
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// let start = Time::constant(23, 0, 0, 0);
    /// let times: Vec<Time> = start.series(-6.hours().minutes(30)).collect();
    /// assert_eq!(times, vec![
    ///     Time::constant(23, 0, 0, 0),
    ///     Time::constant(16, 30, 0, 0),
    ///     Time::constant(10, 0, 0, 0),
    ///     Time::constant(3, 30, 0, 0),
    /// ]);
    /// ```
    #[inline]
    pub fn series(self, period: Span) -> TimeSeries {
        TimeSeries { start: self, period, step: 0 }
    }
}

/// Parsing and formatting using a "printf" style of API.
impl Time {
    /// Parses a civil time in `input` matching the given `format`.
    ///
    /// The format string uses a "printf" style of API where conversion
    /// specifiers can be used as place holders to match components of
    /// a datetime. For details on the specifiers supported, see the
    /// [`fmt::strtime`] module documentation.
    ///
    /// # Errors
    ///
    /// This returns an error when parsing failed. This might happen because
    /// the format string itself was invalid, or because the input didn't match
    /// the format string.
    ///
    /// This also returns an error if there wasn't sufficient information to
    /// construct a civil time. For example, if an offset wasn't parsed.
    ///
    /// # Example
    ///
    /// This example shows how to parse a civil time:
    ///
    /// ```
    /// use jiff::civil::Time;
    ///
    /// // Parse with a 12-hour clock.
    /// let time = Time::strptime("%I:%M%P", "4:30pm")?;
    /// assert_eq!(time.to_string(), "16:30:00");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn strptime(
        format: impl AsRef<[u8]>,
        input: impl AsRef<[u8]>,
    ) -> Result<Time, Error> {
        fmt::strtime::parse(format, input).and_then(|tm| tm.to_time())
    }

    /// Formats this civil time according to the given `format`.
    ///
    /// The format string uses a "printf" style of API where conversion
    /// specifiers can be used as place holders to format components of
    /// a datetime. For details on the specifiers supported, see the
    /// [`fmt::strtime`] module documentation.
    ///
    /// # Errors and panics
    ///
    /// While this routine itself does not error or panic, using the value
    /// returned may result in a panic if formatting fails. See the
    /// documentation on [`fmt::strtime::Display`] for more information.
    ///
    /// To format in a way that surfaces errors without panicking, use either
    /// [`fmt::strtime::format`] or [`fmt::strtime::BrokenDownTime::format`].
    ///
    /// # Example
    ///
    /// This example shows how to format a civil time in a 12 hour clock with
    /// no padding for the hour:
    ///
    /// ```
    /// use jiff::civil::time;
    ///
    /// let t = time(16, 30, 59, 0);
    /// let string = t.strftime("%-I:%M%P").to_string();
    /// assert_eq!(string, "4:30pm");
    /// ```
    ///
    /// Note that one can round a `Time` before formatting. For example, to
    /// round to the nearest minute:
    ///
    /// ```
    /// use jiff::{civil::time, Unit};
    ///
    /// let t = time(16, 30, 59, 0);
    /// let string = t.round(Unit::Minute)?.strftime("%-I:%M%P").to_string();
    /// assert_eq!(string, "4:31pm");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn strftime<'f, F: 'f + ?Sized + AsRef<[u8]>>(
        &self,
        format: &'f F,
    ) -> fmt::strtime::Display<'f> {
        fmt::strtime::Display { fmt: format.as_ref(), tm: (*self).into() }
    }
}

/// Crate internal APIs.
///
/// Many of these are mirrors of the public API, but on ranged types. These
/// are often much more convenient to use in composition with other parts of
/// the crate that also use ranged integer types. And this often permits the
/// routines to be infallible and (possibly) zero-cost.
impl Time {
    #[inline]
    pub(crate) fn new_ranged(
        hour: impl RInto<Hour>,
        minute: impl RInto<Minute>,
        second: impl RInto<Second>,
        subsec_nanosecond: impl RInto<SubsecNanosecond>,
    ) -> Time {
        Time {
            hour: hour.rinto(),
            minute: minute.rinto(),
            second: second.rinto(),
            subsec_nanosecond: subsec_nanosecond.rinto(),
        }
    }

    /// Set the fractional parts of this time to the given units via ranged
    /// types.
    #[inline]
    fn with_subsec_parts_ranged(
        self,
        millisecond: impl RInto<Millisecond>,
        microsecond: impl RInto<Microsecond>,
        nanosecond: impl RInto<Nanosecond>,
    ) -> Time {
        let millisecond = SubsecNanosecond::rfrom(millisecond.rinto());
        let microsecond = SubsecNanosecond::rfrom(microsecond.rinto());
        let nanosecond = SubsecNanosecond::rfrom(nanosecond.rinto());
        let mut subsec_nanosecond =
            millisecond * t::MICROS_PER_MILLI * t::NANOS_PER_MICRO;
        subsec_nanosecond += microsecond * t::NANOS_PER_MICRO;
        subsec_nanosecond += nanosecond;
        Time { subsec_nanosecond: subsec_nanosecond.rinto(), ..self }
    }

    #[inline]
    pub(crate) fn hour_ranged(self) -> Hour {
        self.hour
    }

    #[inline]
    pub(crate) fn minute_ranged(self) -> Minute {
        self.minute
    }

    #[inline]
    pub(crate) fn second_ranged(self) -> Second {
        self.second
    }

    #[inline]
    pub(crate) fn millisecond_ranged(self) -> Millisecond {
        let micros = self.subsec_nanosecond_ranged() / t::NANOS_PER_MICRO;
        let millis = micros / t::MICROS_PER_MILLI;
        millis.rinto()
    }

    #[inline]
    pub(crate) fn microsecond_ranged(self) -> Microsecond {
        let micros = self.subsec_nanosecond_ranged() / t::NANOS_PER_MICRO;
        let only_micros = micros % t::MICROS_PER_MILLI;
        only_micros.rinto()
    }

    #[inline]
    pub(crate) fn nanosecond_ranged(self) -> Nanosecond {
        let only_nanos = self.subsec_nanosecond_ranged() % t::NANOS_PER_MICRO;
        only_nanos.rinto()
    }

    #[inline]
    pub(crate) fn subsec_nanosecond_ranged(self) -> SubsecNanosecond {
        self.subsec_nanosecond
    }

    #[inline]
    pub(crate) fn until_nanoseconds(self, other: Time) -> t::SpanNanoseconds {
        let t1 = t::SpanNanoseconds::rfrom(self.to_nanosecond());
        let t2 = t::SpanNanoseconds::rfrom(other.to_nanosecond());
        t2 - t1
    }

    /// Converts this time value to the number of nanoseconds that has elapsed
    /// since `00:00:00.000000000`.
    ///
    /// The maximum possible value that can be returned represents the time
    /// `23:59:59.999999999`.
    #[inline]
    pub(crate) fn to_nanosecond(&self) -> CivilDayNanosecond {
        let mut civil_day_nanosecond =
            CivilDayNanosecond::rfrom(self.hour_ranged()) * t::NANOS_PER_HOUR;
        civil_day_nanosecond +=
            CivilDayNanosecond::rfrom(self.minute_ranged())
                * t::NANOS_PER_MINUTE;
        // Note that we clamp the leap second here! That's because we
        // effectively pretend they don't exist when treating `Time` values
        // as equal divisions in a single day.
        civil_day_nanosecond +=
            CivilDayNanosecond::rfrom(self.second_ranged())
                * t::NANOS_PER_SECOND;
        civil_day_nanosecond +=
            CivilDayNanosecond::rfrom(self.subsec_nanosecond_ranged());
        civil_day_nanosecond
    }

    /// Converts the given nanosecond to a time value. The nanosecond should
    /// correspond to the number of nanoseconds that have elapsed since
    /// `00:00:00.000000000`.
    #[inline]
    pub(crate) fn from_nanosecond(
        nanosecond: impl RInto<CivilDayNanosecond>,
    ) -> Time {
        let nanosecond = nanosecond.rinto();
        let hour = nanosecond / t::NANOS_PER_HOUR;
        let minute = (nanosecond % t::NANOS_PER_HOUR) / t::NANOS_PER_MINUTE;
        let second = (nanosecond % t::NANOS_PER_MINUTE) / t::NANOS_PER_SECOND;
        let subsec_nanosecond = nanosecond % t::NANOS_PER_SECOND;
        Time::new_ranged(hour, minute, second, subsec_nanosecond)
    }
}

impl Default for Time {
    #[inline]
    fn default() -> Time {
        Time::midnight()
    }
}

impl core::fmt::Debug for Time {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        core::fmt::Display::fmt(self, f)
    }
}

impl core::fmt::Display for Time {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        use crate::fmt::StdFmtWrite;

        DEFAULT_DATETIME_PRINTER
            .print_time(self, StdFmtWrite(f))
            .map_err(|_| core::fmt::Error)
    }
}

impl core::str::FromStr for Time {
    type Err = Error;

    #[inline]
    fn from_str(string: &str) -> Result<Time, Error> {
        DEFAULT_DATETIME_PARSER.parse_time(string)
    }
}

/// Adds a span of time. This uses wrapping arithmetic.
///
/// For checked arithmetic, see [`Time::checked_add`].
impl core::ops::Add<Span> for Time {
    type Output = Time;

    #[inline]
    fn add(self, rhs: Span) -> Time {
        self.wrapping_add(rhs)
    }
}

/// Adds a span of time in place. This uses wrapping arithmetic.
///
/// For checked arithmetic, see [`Time::checked_add`].
impl core::ops::AddAssign<Span> for Time {
    #[inline]
    fn add_assign(&mut self, rhs: Span) {
        *self = *self + rhs;
    }
}

/// Subtracts a span of time. This uses wrapping arithmetic.
///
/// For checked arithmetic, see [`Time::checked_sub`].
impl core::ops::Sub<Span> for Time {
    type Output = Time;

    #[inline]
    fn sub(self, rhs: Span) -> Time {
        self.wrapping_sub(rhs)
    }
}

/// Subtracts a span of time in place. This uses wrapping arithmetic.
///
/// For checked arithmetic, see [`Time::checked_sub`].
impl core::ops::SubAssign<Span> for Time {
    #[inline]
    fn sub_assign(&mut self, rhs: Span) {
        *self = *self - rhs;
    }
}

/// Computes the span of time between two times.
///
/// This will return a negative span when the time being subtracted is greater.
///
/// Since this uses the default configuration for calculating a span between
/// two times (no rounding and largest units is hours), this will never panic
/// or fail in any way.
///
/// To configure the largest unit or enable rounding, use [`Time::since`].
impl core::ops::Sub for Time {
    type Output = Span;

    #[inline]
    fn sub(self, rhs: Time) -> Span {
        self.since(rhs).expect("since never fails when given Time")
    }
}

impl From<DateTime> for Time {
    #[inline]
    fn from(dt: DateTime) -> Time {
        dt.time()
    }
}

impl From<Zoned> for Time {
    #[inline]
    fn from(zdt: Zoned) -> Time {
        zdt.datetime().time()
    }
}

impl<'a> From<&'a Zoned> for Time {
    #[inline]
    fn from(zdt: &'a Zoned) -> Time {
        zdt.datetime().time()
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for Time {
    #[inline]
    fn serialize<S: serde::Serializer>(
        &self,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        serializer.collect_str(self)
    }
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for Time {
    #[inline]
    fn deserialize<D: serde::Deserializer<'de>>(
        deserializer: D,
    ) -> Result<Time, D::Error> {
        use serde::de;

        struct TimeVisitor;

        impl<'de> de::Visitor<'de> for TimeVisitor {
            type Value = Time;

            fn expecting(
                &self,
                f: &mut core::fmt::Formatter,
            ) -> core::fmt::Result {
                f.write_str("a time string")
            }

            #[inline]
            fn visit_bytes<E: de::Error>(
                self,
                value: &[u8],
            ) -> Result<Time, E> {
                DEFAULT_DATETIME_PARSER
                    .parse_time(value)
                    .map_err(de::Error::custom)
            }

            #[inline]
            fn visit_str<E: de::Error>(self, value: &str) -> Result<Time, E> {
                self.visit_bytes(value.as_bytes())
            }
        }

        deserializer.deserialize_bytes(TimeVisitor)
    }
}

#[cfg(test)]
impl quickcheck::Arbitrary for Time {
    fn arbitrary(g: &mut quickcheck::Gen) -> Time {
        let hour = Hour::arbitrary(g);
        let minute = Minute::arbitrary(g);
        let second = Second::arbitrary(g);
        let subsec_nanosecond = SubsecNanosecond::arbitrary(g);
        Time::new_ranged(hour, minute, second, subsec_nanosecond)
    }

    fn shrink(&self) -> alloc::boxed::Box<dyn Iterator<Item = Time>> {
        alloc::boxed::Box::new(
            (
                self.hour_ranged(),
                self.minute_ranged(),
                self.second_ranged(),
                self.subsec_nanosecond_ranged(),
            )
                .shrink()
                .map(
                    |(hour, minute, second, subsec_nanosecond)| {
                        Time::new_ranged(
                            hour,
                            minute,
                            second,
                            subsec_nanosecond,
                        )
                    },
                ),
        )
    }
}

/// An iterator over periodic times, created by [`Time::series`].
///
/// It is exhausted when the next value would exceed a [`Span`] or [`Time`]
/// value.
#[derive(Clone, Debug)]
pub struct TimeSeries {
    start: Time,
    period: Span,
    step: i64,
}

impl Iterator for TimeSeries {
    type Item = Time;

    #[inline]
    fn next(&mut self) -> Option<Time> {
        let span = self.period.checked_mul(self.step).ok()?;
        self.step = self.step.checked_add(1)?;
        let time = self.start.checked_add(span).ok()?;
        Some(time)
    }
}

/// Options for [`Time::since`] and [`Time::until`].
///
/// This type provides a way to configure the calculation of spans between two
/// [`Time`] values. In particular, both `Time::since` and `Time::until` accept
/// anything that implements `Into<TimeDifference>`. There are a few key trait
/// implementations that make this convenient:
///
/// * `From<Time> for TimeDifference` will construct a configuration consisting
/// of just the time. So for example, `time1.until(time2)` will return the span
/// from `time1` to `time2`.
/// * `From<DateTime> for TimeDifference` will construct a configuration
/// consisting of just the time from the given datetime. So for example,
/// `time.since(datetime)` returns the span from `datetime.time()` to `time`.
/// * `From<(Unit, Time)>` is a convenient way to specify the largest units
/// that should be present on the span returned. By default, the largest units
/// are hours. Using this trait implementation is equivalent to
/// `TimeDifference::new(time).largest(unit)`.
/// * `From<(Unit, DateTime)>` is like the one above, but with the time from
/// the given datetime.
///
/// One can also provide a `TimeDifference` value directly. Doing so
/// is necessary to use the rounding features of calculating a span. For
/// example, setting the smallest unit (defaults to [`Unit::Nanosecond`]), the
/// rounding mode (defaults to [`RoundMode::Trunc`]) and the rounding increment
/// (defaults to `1`). The defaults are selected such that no rounding occurs.
///
/// Rounding a span as part of calculating it is provided as a convenience.
/// Callers may choose to round the span as a distinct step via
/// [`Span::round`].
///
/// # Example
///
/// This example shows how to round a span between two datetimes to the nearest
/// half-hour, with ties breaking away from zero.
///
/// ```
/// use jiff::{civil::{Time, TimeDifference}, RoundMode, ToSpan, Unit};
///
/// let t1 = "08:14:00.123456789".parse::<Time>()?;
/// let t2 = "15:00".parse::<Time>()?;
/// let span = t1.until(
///     TimeDifference::new(t2)
///         .smallest(Unit::Minute)
///         .mode(RoundMode::HalfExpand)
///         .increment(30),
/// )?;
/// assert_eq!(span, 7.hours());
///
/// // One less minute, and because of the HalfExpand mode, the span would
/// // get rounded down.
/// let t2 = "14:59".parse::<Time>()?;
/// let span = t1.until(
///     TimeDifference::new(t2)
///         .smallest(Unit::Minute)
///         .mode(RoundMode::HalfExpand)
///         .increment(30),
/// )?;
/// assert_eq!(span, 6.hours().minutes(30));
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Clone, Copy, Debug)]
pub struct TimeDifference {
    time: Time,
    round: SpanRound<'static>,
}

impl TimeDifference {
    /// Create a new default configuration for computing the span between
    /// the given time and some other time (specified as the receiver in
    /// [`Time::since`] or [`Time::until`]).
    #[inline]
    pub fn new(time: Time) -> TimeDifference {
        // We use truncation rounding by default since it seems that's
        // what is generally expected when computing the difference between
        // datetimes.
        //
        // See: https://github.com/tc39/proposal-temporal/issues/1122
        let round = SpanRound::new().mode(RoundMode::Trunc);
        TimeDifference { time, round }
    }

    /// Set the smallest units allowed in the span returned.
    ///
    /// # Errors
    ///
    /// The smallest units must be no greater than the largest units. If this
    /// is violated, then computing a span with this configuration will result
    /// in an error.
    ///
    /// # Example
    ///
    /// This shows how to round a span between two times to units no less than
    /// seconds.
    ///
    /// ```
    /// use jiff::{civil::{Time, TimeDifference}, RoundMode, ToSpan, Unit};
    ///
    /// let t1 = "08:14:02.5001".parse::<Time>()?;
    /// let t2 = "08:30:03.0001".parse::<Time>()?;
    /// let span = t1.until(
    ///     TimeDifference::new(t2)
    ///         .smallest(Unit::Second)
    ///         .mode(RoundMode::HalfExpand),
    /// )?;
    /// assert_eq!(span, 16.minutes().seconds(1));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn smallest(self, unit: Unit) -> TimeDifference {
        TimeDifference { round: self.round.smallest(unit), ..self }
    }

    /// Set the largest units allowed in the span returned.
    ///
    /// When a largest unit is not specified, computing a span between times
    /// behaves as if it were set to [`Unit::Hour`].
    ///
    /// # Errors
    ///
    /// The largest units, when set, must be at least as big as the smallest
    /// units (which defaults to [`Unit::Nanosecond`]). If this is violated,
    /// then computing a span with this configuration will result in an error.
    ///
    /// # Example
    ///
    /// This shows how to round a span between two times to units no
    /// bigger than seconds.
    ///
    /// ```
    /// use jiff::{civil::{Time, TimeDifference}, ToSpan, Unit};
    ///
    /// let t1 = "08:14".parse::<Time>()?;
    /// let t2 = "08:30".parse::<Time>()?;
    /// let span = t1.until(TimeDifference::new(t2).largest(Unit::Second))?;
    /// assert_eq!(span, 960.seconds());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn largest(self, unit: Unit) -> TimeDifference {
        TimeDifference { round: self.round.largest(unit), ..self }
    }

    /// Set the rounding mode.
    ///
    /// This defaults to [`RoundMode::Trunc`] since it's plausible that
    /// rounding "up" in the context of computing the span between two times
    /// could be surprising in a number of cases. The [`RoundMode::HalfExpand`]
    /// mode corresponds to typical rounding you might have learned about in
    /// school. But a variety of other rounding modes exist.
    ///
    /// # Example
    ///
    /// This shows how to always round "up" towards positive infinity.
    ///
    /// ```
    /// use jiff::{civil::{Time, TimeDifference}, RoundMode, ToSpan, Unit};
    ///
    /// let t1 = "08:10".parse::<Time>()?;
    /// let t2 = "08:11".parse::<Time>()?;
    /// let span = t1.until(
    ///     TimeDifference::new(t2)
    ///         .smallest(Unit::Hour)
    ///         .mode(RoundMode::Ceil),
    /// )?;
    /// // Only one minute elapsed, but we asked to always round up!
    /// assert_eq!(span, 1.hour());
    ///
    /// // Since `Ceil` always rounds toward positive infinity, the behavior
    /// // flips for a negative span.
    /// let span = t1.since(
    ///     TimeDifference::new(t2)
    ///         .smallest(Unit::Hour)
    ///         .mode(RoundMode::Ceil),
    /// )?;
    /// assert_eq!(span, 0.hour());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn mode(self, mode: RoundMode) -> TimeDifference {
        TimeDifference { round: self.round.mode(mode), ..self }
    }

    /// Set the rounding increment for the smallest unit.
    ///
    /// The default value is `1`. Other values permit rounding the smallest
    /// unit to the nearest integer increment specified. For example, if the
    /// smallest unit is set to [`Unit::Minute`], then a rounding increment of
    /// `30` would result in rounding in increments of a half hour. That is,
    /// the only minute value that could result would be `0` or `30`.
    ///
    /// # Errors
    ///
    /// The rounding increment must divide evenly into the next highest unit
    /// after the smallest unit configured (and must not be equivalent to it).
    /// For example, if the smallest unit is [`Unit::Nanosecond`], then *some*
    /// of the valid values for the rounding increment are `1`, `2`, `4`, `5`,
    /// `100` and `500`. Namely, any integer that divides evenly into `1,000`
    /// nanoseconds since there are `1,000` nanoseconds in the next highest
    /// unit (microseconds).
    ///
    /// The error will occur when computing the span, and not when setting
    /// the increment here.
    ///
    /// # Example
    ///
    /// This shows how to round the span between two times to the nearest 5
    /// minute increment.
    ///
    /// ```
    /// use jiff::{civil::{Time, TimeDifference}, RoundMode, ToSpan, Unit};
    ///
    /// let t1 = "08:19".parse::<Time>()?;
    /// let t2 = "12:52".parse::<Time>()?;
    /// let span = t1.until(
    ///     TimeDifference::new(t2)
    ///         .smallest(Unit::Minute)
    ///         .increment(5)
    ///         .mode(RoundMode::HalfExpand),
    /// )?;
    /// assert_eq!(span, 4.hour().minutes(35));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn increment(self, increment: i64) -> TimeDifference {
        TimeDifference { round: self.round.increment(increment), ..self }
    }

    /// Returns true if and only if this configuration could change the span
    /// via rounding.
    #[inline]
    fn rounding_may_change_span(&self) -> bool {
        self.round.rounding_may_change_span_ignore_largest()
    }

    /// Returns the span of time from `t1` to the time in this configuration.
    /// The biggest units allowed are determined by the `smallest` and
    /// `largest` settings, but defaults to `Unit::Hour`.
    #[inline]
    fn until_with_largest_unit(&self, t1: Time) -> Result<Span, Error> {
        let t2 = self.time;
        if t1 == t2 {
            return Ok(Span::new());
        }
        let largest = self.round.get_largest().unwrap_or(Unit::Hour);
        if largest > Unit::Hour {
            return Err(err!(
                "rounding the span between two times must use hours \
                 or smaller for its units, but found {units}",
                units = largest.plural(),
            ));
        }
        let start = t1.to_nanosecond();
        let end = t2.to_nanosecond();
        let span = Span::from_invariant_nanoseconds(largest, end - start)
            .expect("difference in civil times is always in bounds");
        Ok(span)
    }
}

impl From<Time> for TimeDifference {
    #[inline]
    fn from(time: Time) -> TimeDifference {
        TimeDifference::new(time)
    }
}

impl From<DateTime> for TimeDifference {
    #[inline]
    fn from(dt: DateTime) -> TimeDifference {
        TimeDifference::from(Time::from(dt))
    }
}

impl From<Zoned> for TimeDifference {
    #[inline]
    fn from(zdt: Zoned) -> TimeDifference {
        TimeDifference::from(Time::from(zdt))
    }
}

impl<'a> From<&'a Zoned> for TimeDifference {
    #[inline]
    fn from(zdt: &'a Zoned) -> TimeDifference {
        TimeDifference::from(zdt.datetime())
    }
}

impl From<(Unit, Time)> for TimeDifference {
    #[inline]
    fn from((largest, time): (Unit, Time)) -> TimeDifference {
        TimeDifference::from(time).largest(largest)
    }
}

impl From<(Unit, DateTime)> for TimeDifference {
    #[inline]
    fn from((largest, dt): (Unit, DateTime)) -> TimeDifference {
        TimeDifference::from((largest, Time::from(dt)))
    }
}

impl From<(Unit, Zoned)> for TimeDifference {
    #[inline]
    fn from((largest, zdt): (Unit, Zoned)) -> TimeDifference {
        TimeDifference::from((largest, Time::from(zdt)))
    }
}

impl<'a> From<(Unit, &'a Zoned)> for TimeDifference {
    #[inline]
    fn from((largest, zdt): (Unit, &'a Zoned)) -> TimeDifference {
        TimeDifference::from((largest, zdt.datetime()))
    }
}

/// Options for [`Time::round`].
///
/// This type provides a way to configure the rounding of a civil time.
/// In particular, `Time::round` accepts anything that implements the
/// `Into<TimeRound>` trait. There are some trait implementations that
/// therefore make calling `Time::round` in some common cases more ergonomic:
///
/// * `From<Unit> for TimeRound` will construct a rounding configuration that
/// rounds to the unit given. Specifically, `TimeRound::new().smallest(unit)`.
/// * `From<(Unit, i64)> for TimeRound` is like the one above, but also
/// specifies the rounding increment for [`TimeRound::increment`].
///
/// Note that in the default configuration, no rounding occurs.
///
/// # Example
///
/// This example shows how to round a time to the nearest second:
///
/// ```
/// use jiff::{civil::Time, Unit};
///
/// let t: Time = "16:24:59.5".parse()?;
/// assert_eq!(
///     t.round(Unit::Second)?,
///     // The second rounds up and causes minutes to increase.
///     Time::constant(16, 25, 0, 0),
/// );
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// The above makes use of the fact that `Unit` implements
/// `Into<TimeRound>`. If you want to change the rounding mode to, say,
/// truncation, then you'll need to construct a `TimeRound` explicitly
/// since there are no convenience `Into` trait implementations for
/// [`RoundMode`].
///
/// ```
/// use jiff::{civil::{Time, TimeRound}, RoundMode, Unit};
///
/// let t: Time = "2024-06-20 16:24:59.5".parse()?;
/// assert_eq!(
///     t.round(
///         TimeRound::new().smallest(Unit::Second).mode(RoundMode::Trunc),
///     )?,
///     // The second just gets truncated as if it wasn't there.
///     Time::constant(16, 24, 59, 0),
/// );
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Clone, Copy, Debug)]
pub struct TimeRound {
    smallest: Unit,
    mode: RoundMode,
    increment: i64,
}

impl TimeRound {
    /// Create a new default configuration for rounding a [`Time`].
    #[inline]
    pub fn new() -> TimeRound {
        TimeRound {
            smallest: Unit::Nanosecond,
            mode: RoundMode::HalfExpand,
            increment: 1,
        }
    }

    /// Set the smallest units allowed in the time returned after rounding.
    ///
    /// Any units below the smallest configured unit will be used, along with
    /// the rounding increment and rounding mode, to determine the value of the
    /// smallest unit. For example, when rounding `03:25:30` to the
    /// nearest minute, the `30` second unit will result in rounding the minute
    /// unit of `25` up to `26` and zeroing out everything below minutes.
    ///
    /// This defaults to [`Unit::Nanosecond`].
    ///
    /// # Errors
    ///
    /// The smallest units must be no greater than [`Unit::Hour`].
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::{civil::{Time, TimeRound}, Unit};
    ///
    /// let t = Time::constant(3, 25, 30, 0);
    /// assert_eq!(
    ///     t.round(TimeRound::new().smallest(Unit::Minute))?,
    ///     Time::constant(3, 26, 0, 0),
    /// );
    /// // Or, utilize the `From<Unit> for TimeRound` impl:
    /// assert_eq!(t.round(Unit::Minute)?, Time::constant(3, 26, 0, 0));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn smallest(self, unit: Unit) -> TimeRound {
        TimeRound { smallest: unit, ..self }
    }

    /// Set the rounding mode.
    ///
    /// This defaults to [`RoundMode::HalfExpand`], which rounds away from
    /// zero. It matches the kind of rounding you might have been taught in
    /// school.
    ///
    /// # Example
    ///
    /// This shows how to always round times up towards positive infinity.
    ///
    /// ```
    /// use jiff::{civil::{Time, TimeRound}, RoundMode, Unit};
    ///
    /// let t: Time = "03:25:01".parse()?;
    /// assert_eq!(
    ///     t.round(
    ///         TimeRound::new()
    ///             .smallest(Unit::Minute)
    ///             .mode(RoundMode::Ceil),
    ///     )?,
    ///     Time::constant(3, 26, 0, 0),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn mode(self, mode: RoundMode) -> TimeRound {
        TimeRound { mode, ..self }
    }

    /// Set the rounding increment for the smallest unit.
    ///
    /// The default value is `1`. Other values permit rounding the smallest
    /// unit to the nearest integer increment specified. For example, if the
    /// smallest unit is set to [`Unit::Minute`], then a rounding increment of
    /// `30` would result in rounding in increments of a half hour. That is,
    /// the only minute value that could result would be `0` or `30`.
    ///
    /// # Errors
    ///
    /// The rounding increment must divide evenly into the
    /// next highest unit above the smallest unit set. The rounding increment
    /// must also not be equal to the next highest unit. For example, if the
    /// smallest unit is [`Unit::Nanosecond`], then *some* of the valid values
    /// for the rounding increment are `1`, `2`, `4`, `5`, `100` and `500`.
    /// Namely, any integer that divides evenly into `1,000` nanoseconds since
    /// there are `1,000` nanoseconds in the next highest unit (microseconds).
    ///
    /// # Example
    ///
    /// This example shows how to round a time to the nearest 10 minute
    /// increment.
    ///
    /// ```
    /// use jiff::{civil::{Time, TimeRound}, RoundMode, Unit};
    ///
    /// let t: Time = "03:24:59".parse()?;
    /// assert_eq!(t.round((Unit::Minute, 10))?, Time::constant(3, 20, 0, 0));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn increment(self, increment: i64) -> TimeRound {
        TimeRound { increment, ..self }
    }

    /// Does the actual rounding.
    pub(crate) fn round(&self, t: Time) -> Result<Time, Error> {
        let increment = increment::for_time(self.smallest, self.increment)?;
        let nanos = t.to_nanosecond();
        let rounded = self.mode.round_by_unit_in_nanoseconds(
            nanos,
            self.smallest,
            increment,
        );
        let limit =
            t::NoUnits128::rfrom(t::CivilDayNanosecond::MAX_SELF) + C(1);
        Ok(Time::from_nanosecond(rounded % limit))
    }
}

impl Default for TimeRound {
    #[inline]
    fn default() -> TimeRound {
        TimeRound::new()
    }
}

impl From<Unit> for TimeRound {
    #[inline]
    fn from(unit: Unit) -> TimeRound {
        TimeRound::default().smallest(unit)
    }
}

impl From<(Unit, i64)> for TimeRound {
    #[inline]
    fn from((unit, increment): (Unit, i64)) -> TimeRound {
        TimeRound::from(unit).increment(increment)
    }
}

/// A builder for setting the fields on a [`Time`].
///
/// This builder is constructed via [`Time::with`].
///
/// # Example
///
/// Unlike [`Date`], a [`Time`] is valid for all possible valid values of its
/// fields. That is, there is no way for two valid field values to combine
/// into an invalid `Time`. So, for `Time`, this builder does have as much of
/// a benefit versus an API design with methods like `Time::with_hour` and
/// `Time::with_minute`. Nevertheless, this builder permits settings multiple
/// fields at the same time and performing only one validity check. Moreover,
/// this provides a consistent API with other date and time types in this
/// crate.
///
/// ```
/// use jiff::civil::time;
///
/// let t1 = time(0, 0, 24, 0);
/// let t2 = t1.with().hour(15).minute(30).millisecond(10).build()?;
/// assert_eq!(t2, time(15, 30, 24, 10_000_000));
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Clone, Copy, Debug)]
pub struct TimeWith {
    original: Time,
    hour: Option<i8>,
    minute: Option<i8>,
    second: Option<i8>,
    millisecond: Option<i16>,
    microsecond: Option<i16>,
    nanosecond: Option<i16>,
    subsec_nanosecond: Option<i32>,
}

impl TimeWith {
    #[inline]
    fn new(original: Time) -> TimeWith {
        TimeWith {
            original,
            hour: None,
            minute: None,
            second: None,
            millisecond: None,
            microsecond: None,
            nanosecond: None,
            subsec_nanosecond: None,
        }
    }

    /// Create a new `Time` from the fields set on this configuration.
    ///
    /// An error occurs when the fields combine to an invalid time. This only
    /// occurs when at least one field has an invalid value, or if at least
    /// one of `millisecond`, `microsecond` or `nanosecond` is set _and_
    /// `subsec_nanosecond` is set. Otherwise, if all fields are valid, then
    /// the entire `Time` is guaranteed to be valid.
    ///
    /// For any fields not set on this configuration, the values are taken from
    /// the [`Time`] that originally created this configuration. When no values
    /// are set, this routine is guaranteed to succeed and will always return
    /// the original time without modification.
    ///
    /// # Example
    ///
    /// This creates a time but with its fractional nanosecond component
    /// stripped:
    ///
    /// ```
    /// use jiff::civil::time;
    ///
    /// let t = time(14, 27, 30, 123_456_789);
    /// assert_eq!(t.with().subsec_nanosecond(0).build()?, time(14, 27, 30, 0));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: error for invalid time
    ///
    /// ```
    /// use jiff::civil::time;
    ///
    /// let t = time(14, 27, 30, 0);
    /// assert!(t.with().hour(24).build().is_err());
    /// ```
    ///
    /// # Example: error for ambiguous sub-second value
    ///
    /// ```
    /// use jiff::civil::time;
    ///
    /// let t = time(14, 27, 30, 123_456_789);
    /// // Setting both the individual sub-second fields and the entire
    /// // fractional component could lead to a misleading configuration. So
    /// // if it's done, it results in an error in all cases. Callers must
    /// // choose one or the other.
    /// assert!(t.with().microsecond(1).subsec_nanosecond(0).build().is_err());
    /// ```
    #[inline]
    pub fn build(self) -> Result<Time, Error> {
        let hour = match self.hour {
            None => self.original.hour_ranged(),
            Some(hour) => Hour::try_new("hour", hour)?,
        };
        let minute = match self.minute {
            None => self.original.minute_ranged(),
            Some(minute) => Minute::try_new("minute", minute)?,
        };
        let second = match self.second {
            None => self.original.second_ranged(),
            Some(second) => Second::try_new("second", second)?,
        };
        let millisecond = match self.millisecond {
            None => self.original.millisecond_ranged(),
            Some(millisecond) => {
                Millisecond::try_new("millisecond", millisecond)?
            }
        };
        let microsecond = match self.microsecond {
            None => self.original.microsecond_ranged(),
            Some(microsecond) => {
                Microsecond::try_new("microsecond", microsecond)?
            }
        };
        let nanosecond = match self.nanosecond {
            None => self.original.nanosecond_ranged(),
            Some(nanosecond) => Nanosecond::try_new("nanosecond", nanosecond)?,
        };
        let subsec_nanosecond = match self.subsec_nanosecond {
            None => self.original.subsec_nanosecond_ranged(),
            Some(subsec_nanosecond) => {
                if self.millisecond.is_some() {
                    return Err(err!(
                        "cannot set both TimeWith::millisecond \
                         and TimeWith::subsec_nanosecond",
                    ));
                }
                if self.microsecond.is_some() {
                    return Err(err!(
                        "cannot set both TimeWith::microsecond \
                         and TimeWith::subsec_nanosecond",
                    ));
                }
                if self.nanosecond.is_some() {
                    return Err(err!(
                        "cannot set both TimeWith::nanosecond \
                         and TimeWith::subsec_nanosecond",
                    ));
                }
                SubsecNanosecond::try_new(
                    "subsec_nanosecond",
                    subsec_nanosecond,
                )?
            }
        };
        if self.subsec_nanosecond.is_some() {
            Ok(Time::new_ranged(hour, minute, second, subsec_nanosecond))
        } else {
            Ok(Time::new_ranged(hour, minute, second, C(0))
                .with_subsec_parts_ranged(
                    millisecond,
                    microsecond,
                    nanosecond,
                ))
        }
    }

    /// Set the hour field on a [`Time`].
    ///
    /// One can access this value via [`Time::hour`].
    ///
    /// This overrides any previous hour settings.
    ///
    /// # Errors
    ///
    /// This returns an error when [`TimeWith::build`] is called if the given
    /// hour is outside the range `0..=23`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::time;
    ///
    /// let t1 = time(15, 21, 59, 0);
    /// assert_eq!(t1.hour(), 15);
    /// let t2 = t1.with().hour(3).build()?;
    /// assert_eq!(t2.hour(), 3);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn hour(self, hour: i8) -> TimeWith {
        TimeWith { hour: Some(hour), ..self }
    }

    /// Set the minute field on a [`Time`].
    ///
    /// One can access this value via [`Time::minute`].
    ///
    /// This overrides any previous minute settings.
    ///
    /// # Errors
    ///
    /// This returns an error when [`TimeWith::build`] is called if the given
    /// minute is outside the range `0..=59`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::time;
    ///
    /// let t1 = time(15, 21, 59, 0);
    /// assert_eq!(t1.minute(), 21);
    /// let t2 = t1.with().minute(3).build()?;
    /// assert_eq!(t2.minute(), 3);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn minute(self, minute: i8) -> TimeWith {
        TimeWith { minute: Some(minute), ..self }
    }

    /// Set the second field on a [`Time`].
    ///
    /// One can access this value via [`Time::second`].
    ///
    /// This overrides any previous second settings.
    ///
    /// # Errors
    ///
    /// This returns an error when [`TimeWith::build`] is called if the given
    /// second is outside the range `0..=59`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::time;
    ///
    /// let t1 = time(15, 21, 59, 0);
    /// assert_eq!(t1.second(), 59);
    /// let t2 = t1.with().second(3).build()?;
    /// assert_eq!(t2.second(), 3);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn second(self, second: i8) -> TimeWith {
        TimeWith { second: Some(second), ..self }
    }

    /// Set the millisecond field on a [`Time`].
    ///
    /// One can access this value via [`Time::millisecond`].
    ///
    /// This overrides any previous millisecond settings.
    ///
    /// # Errors
    ///
    /// This returns an error when [`TimeWith::build`] is called if the given
    /// millisecond is outside the range `0..=999`, or if both this and
    /// [`TimeWith::subsec_nanosecond`] are set.
    ///
    /// # Example
    ///
    /// This shows the relationship between [`Time::millisecond`] and
    /// [`Time::subsec_nanosecond`]:
    ///
    /// ```
    /// use jiff::civil::time;
    ///
    /// let t = time(15, 21, 35, 0).with().millisecond(123).build()?;
    /// assert_eq!(t.subsec_nanosecond(), 123_000_000);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn millisecond(self, millisecond: i16) -> TimeWith {
        TimeWith { millisecond: Some(millisecond), ..self }
    }

    /// Set the microsecond field on a [`Time`].
    ///
    /// One can access this value via [`Time::microsecond`].
    ///
    /// This overrides any previous microsecond settings.
    ///
    /// # Errors
    ///
    /// This returns an error when [`TimeWith::build`] is called if the given
    /// microsecond is outside the range `0..=999`, or if both this and
    /// [`TimeWith::subsec_nanosecond`] are set.
    ///
    /// # Example
    ///
    /// This shows the relationship between [`Time::microsecond`] and
    /// [`Time::subsec_nanosecond`]:
    ///
    /// ```
    /// use jiff::civil::time;
    ///
    /// let t = time(15, 21, 35, 0).with().microsecond(123).build()?;
    /// assert_eq!(t.subsec_nanosecond(), 123_000);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn microsecond(self, microsecond: i16) -> TimeWith {
        TimeWith { microsecond: Some(microsecond), ..self }
    }

    /// Set the nanosecond field on a [`Time`].
    ///
    /// One can access this value via [`Time::nanosecond`].
    ///
    /// This overrides any previous nanosecond settings.
    ///
    /// # Errors
    ///
    /// This returns an error when [`TimeWith::build`] is called if the given
    /// nanosecond is outside the range `0..=999`, or if both this and
    /// [`TimeWith::subsec_nanosecond`] are set.
    ///
    /// # Example
    ///
    /// This shows the relationship between [`Time::nanosecond`] and
    /// [`Time::subsec_nanosecond`]:
    ///
    /// ```
    /// use jiff::civil::time;
    ///
    /// let t = time(15, 21, 35, 0).with().nanosecond(123).build()?;
    /// assert_eq!(t.subsec_nanosecond(), 123);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn nanosecond(self, nanosecond: i16) -> TimeWith {
        TimeWith { nanosecond: Some(nanosecond), ..self }
    }

    /// Set the subsecond nanosecond field on a [`Time`].
    ///
    /// If you want to access this value on `Time`, then use
    /// [`Time::subsec_nanosecond`].
    ///
    /// This overrides any previous subsecond nanosecond settings.
    ///
    /// # Errors
    ///
    /// This returns an error when [`TimeWith::build`] is called if the given
    /// subsecond nanosecond is outside the range `0..=999,999,999`, or if both
    /// this and one of [`TimeWith::millisecond`], [`TimeWith::microsecond`] or
    /// [`TimeWith::nanosecond`] are set.
    ///
    /// # Example
    ///
    /// This shows the relationship between constructing a `Time` value with
    /// subsecond nanoseconds and its individual subsecond fields:
    ///
    /// ```
    /// use jiff::civil::time;
    ///
    /// let t1 = time(15, 21, 35, 0);
    /// let t2 = t1.with().subsec_nanosecond(123_456_789).build()?;
    /// assert_eq!(t2.millisecond(), 123);
    /// assert_eq!(t2.microsecond(), 456);
    /// assert_eq!(t2.nanosecond(), 789);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn subsec_nanosecond(self, subsec_nanosecond: i32) -> TimeWith {
        TimeWith { subsec_nanosecond: Some(subsec_nanosecond), ..self }
    }
}

#[cfg(test)]
mod tests {
    use crate::ToSpan;

    use super::*;

    #[test]
    fn min() {
        let t = Time::MIN;
        assert_eq!(t.hour(), 0);
        assert_eq!(t.minute(), 0);
        assert_eq!(t.second(), 0);
        assert_eq!(t.subsec_nanosecond(), 0);
    }

    #[test]
    fn max() {
        let t = Time::MAX;
        assert_eq!(t.hour(), 23);
        assert_eq!(t.minute(), 59);
        assert_eq!(t.second(), 59);
        assert_eq!(t.subsec_nanosecond(), 999_999_999);
    }

    #[test]
    fn invalid() {
        assert!(Time::new(24, 0, 0, 0).is_err());
        assert!(Time::new(23, 60, 0, 0).is_err());
        assert!(Time::new(23, 59, 60, 0).is_err());
        assert!(Time::new(23, 59, 61, 0).is_err());
        assert!(Time::new(-1, 0, 0, 0).is_err());
        assert!(Time::new(0, -1, 0, 0).is_err());
        assert!(Time::new(0, 0, -1, 0).is_err());

        assert!(Time::new(0, 0, 0, 1_000_000_000).is_err());
        assert!(Time::new(0, 0, 0, -1).is_err());
        assert!(Time::new(23, 59, 59, 1_000_000_000).is_err());
        assert!(Time::new(23, 59, 59, -1).is_err());
    }

    #[test]
    fn rounding_cross_midnight() {
        let t1 = Time::constant(23, 59, 59, 999_999_999);

        let t2 = t1.round(Unit::Nanosecond).unwrap();
        assert_eq!(t2, t1);

        let t2 = t1.round(Unit::Millisecond).unwrap();
        assert_eq!(t2, Time::constant(0, 0, 0, 0));

        let t2 = t1.round(Unit::Microsecond).unwrap();
        assert_eq!(t2, Time::constant(0, 0, 0, 0));

        let t2 = t1.round(Unit::Millisecond).unwrap();
        assert_eq!(t2, Time::constant(0, 0, 0, 0));

        let t2 = t1.round(Unit::Second).unwrap();
        assert_eq!(t2, Time::constant(0, 0, 0, 0));

        let t2 = t1.round(Unit::Minute).unwrap();
        assert_eq!(t2, Time::constant(0, 0, 0, 0));

        let t2 = t1.round(Unit::Hour).unwrap();
        assert_eq!(t2, Time::constant(0, 0, 0, 0));

        let t1 = Time::constant(22, 15, 0, 0);
        assert_eq!(
            Time::constant(22, 30, 0, 0),
            t1.round(TimeRound::new().smallest(Unit::Minute).increment(30))
                .unwrap()
        );
    }

    quickcheck::quickcheck! {
        fn prop_ordering_same_as_civil_nanosecond(
            civil_nanosecond1: CivilDayNanosecond,
            civil_nanosecond2: CivilDayNanosecond
        ) -> bool {
            let t1 = Time::from_nanosecond(civil_nanosecond1);
            let t2 = Time::from_nanosecond(civil_nanosecond2);
            t1.cmp(&t2) == civil_nanosecond1.cmp(&civil_nanosecond2)
        }

        fn prop_checked_add_then_sub(
            time: Time,
            nano_span: CivilDayNanosecond
        ) -> quickcheck::TestResult {
            let span = Span::new().nanoseconds(nano_span.get());
            let Ok(sum) = time.checked_add(span) else {
                return quickcheck::TestResult::discard()
            };
            let diff = sum.checked_sub(span).unwrap();
            quickcheck::TestResult::from_bool(time == diff)
        }

        fn prop_wrapping_add_then_sub(
            time: Time,
            nano_span: CivilDayNanosecond
        ) -> bool {
            let span = Span::new().nanoseconds(nano_span.get());
            let sum = time.wrapping_add(span);
            let diff = sum.wrapping_sub(span);
            time == diff
        }

        fn prop_checked_add_equals_wrapping_add(
            time: Time,
            nano_span: CivilDayNanosecond
        ) -> quickcheck::TestResult {
            let span = Span::new().nanoseconds(nano_span.get());
            let Ok(sum_checked) = time.checked_add(span) else {
                return quickcheck::TestResult::discard()
            };
            let sum_wrapped = time.wrapping_add(span);
            quickcheck::TestResult::from_bool(sum_checked == sum_wrapped)
        }

        fn prop_checked_sub_equals_wrapping_sub(
            time: Time,
            nano_span: CivilDayNanosecond
        ) -> quickcheck::TestResult {
            let span = Span::new().nanoseconds(nano_span.get());
            let Ok(diff_checked) = time.checked_sub(span) else {
                return quickcheck::TestResult::discard()
            };
            let diff_wrapped = time.wrapping_sub(span);
            quickcheck::TestResult::from_bool(diff_checked == diff_wrapped)
        }

        fn prop_until_then_add(t1: Time, t2: Time) -> bool {
            let span = t1.until(t2).unwrap();
            t1.checked_add(span).unwrap() == t2
        }

        fn prop_until_then_sub(t1: Time, t2: Time) -> bool {
            let span = t1.until(t2).unwrap();
            t2.checked_sub(span).unwrap() == t1
        }

        fn prop_since_then_add(t1: Time, t2: Time) -> bool {
            let span = t1.since(t2).unwrap();
            t2.checked_add(span).unwrap() == t1
        }

        fn prop_since_then_sub(t1: Time, t2: Time) -> bool {
            let span = t1.since(t2).unwrap();
            t1.checked_sub(span).unwrap() == t2
        }

        fn prop_until_is_since_negated(t1: Time, t2: Time) -> bool {
            t1.until(t2).unwrap().get_nanoseconds()
                == t1.since(t2).unwrap().negate().get_nanoseconds()
        }
    }

    #[test]
    fn overflowing_add() {
        let t1 = Time::constant(23, 30, 0, 0);
        let (t2, span) = t1.overflowing_add(5.hours()).unwrap();
        assert_eq!(t2, Time::constant(4, 30, 0, 0));
        assert_eq!(span, 1.days());
    }

    #[test]
    fn overflowing_add_overflows() {
        let t1 = Time::constant(23, 30, 0, 0);
        let span = Span::new()
            .hours(t::SpanHours::MAX_REPR)
            .minutes(t::SpanMinutes::MAX_REPR)
            .seconds(t::SpanSeconds::MAX_REPR)
            .milliseconds(t::SpanMilliseconds::MAX_REPR)
            .microseconds(t::SpanMicroseconds::MAX_REPR)
            .nanoseconds(t::SpanNanoseconds::MAX_REPR);
        assert!(t1.overflowing_add(span).is_err());
    }

    #[test]
    fn time_size() {
        #[cfg(debug_assertions)]
        {
            assert_eq!(24, core::mem::size_of::<Time>());
        }
        #[cfg(not(debug_assertions))]
        {
            assert_eq!(8, core::mem::size_of::<Time>());
        }
    }
}
