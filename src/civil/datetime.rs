use crate::{
    civil::{datetime, Date, DateWith, Era, Time, TimeWith, Weekday},
    error::{err, Error, ErrorContext},
    fmt::{
        self,
        temporal::{DEFAULT_DATETIME_PARSER, DEFAULT_DATETIME_PRINTER},
    },
    tz::TimeZone,
    util::{
        rangeint::{RFrom, RInto},
        round::increment,
        t::{self, C},
    },
    zoned::Zoned,
    RoundMode, Span, SpanRound, Unit,
};

/// A representation of a civil datetime in the Gregorian calendar.
///
/// A `DateTime` value corresponds to a pair of a [`Date`] and a [`Time`].
/// That is, a datetime contains a year, month, day, hour, minute, second and
/// the fractional number of nanoseconds.
///
/// A `DateTime` value is guaranteed to contain a valid date and time. For
/// example, neither `2023-02-29T00:00:00` nor `2015-06-30T23:59:60` are
/// valid `DateTime` values.
///
/// # Civil datetimes
///
/// A `DateTime` value behaves without regard to daylight saving time or time
/// zones in general. When doing arithmetic on datetimes with spans defined in
/// units of time (such as with [`DateTime::checked_add`]), days are considered
/// to always be precisely `86,400` seconds long.
///
/// # Parsing and printing
///
/// The `DateTime` type provides convenient trait implementations of
/// [`std::str::FromStr`] and [`std::fmt::Display`]:
///
/// ```
/// use jiff::civil::DateTime;
///
/// let dt: DateTime = "2024-06-19 15:22:45".parse()?;
/// assert_eq!(dt.to_string(), "2024-06-19T15:22:45");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// A civil `DateTime` can also be parsed from something that _contains_ a
/// datetime, but with perhaps other data (such as an offset or time zone):
///
/// ```
/// use jiff::civil::DateTime;
///
/// let dt: DateTime = "2024-06-19T15:22:45-04[America/New_York]".parse()?;
/// assert_eq!(dt.to_string(), "2024-06-19T15:22:45");
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
/// value corresponds to `0000-01-01T00:00:00.000000000`. That is, it is
/// the datetime corresponding to `DateTime::from_parts(Date::default(),
/// Time::default())`. One can also access this value via the `DateTime::ZERO`
/// constant.
///
/// # Leap seconds
///
/// Jiff does not support leap seconds. Jiff behaves as if they don't exist.
/// The only exception is that if one parses a datetime with a second component
/// of `60`, then it is automatically constrained to `59`:
///
/// ```
/// use jiff::civil::{DateTime, date};
///
/// let dt: DateTime = "2016-12-31 23:59:60".parse()?;
/// assert_eq!(dt, date(2016, 12, 31).at(23, 59, 59, 0));
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Comparisons
///
/// The `DateTime` type provides both `Eq` and `Ord` trait implementations to
/// facilitate easy comparisons. When a datetime `dt1` occurs before a datetime
/// `dt2`, then `dt1 < dt2`. For example:
///
/// ```
/// use jiff::civil::date;
///
/// let dt1 = date(2024, 3, 11).at(1, 25, 15, 0);
/// let dt2 = date(2025, 1, 31).at(0, 30, 0, 0);
/// assert!(dt1 < dt2);
/// ```
///
/// # Arithmetic
///
/// This type provides routines for adding and subtracting spans of time, as
/// well as computing the span of time between two `DateTime` values.
///
/// For adding or subtracting spans of time, one can use any of the following
/// routines:
///
/// * [`DateTime::checked_add`] or [`DateTime::checked_sub`] for checked
/// arithmetic.
/// * [`DateTime::saturating_add`] or [`DateTime::saturating_sub`] for
/// saturating arithmetic.
///
/// Additionally, checked arithmetic is available via the `Add` and `Sub`
/// trait implementations. When the result overflows, a panic occurs.
///
/// ```
/// use jiff::{civil::date, ToSpan};
///
/// let start = date(2024, 2, 25).at(15, 45, 0, 0);
/// let one_week_later = start + 1.weeks();
/// assert_eq!(one_week_later, date(2024, 3, 3).at(15, 45, 0, 0));
/// ```
///
/// One can compute the span of time between two datetimes using either
/// [`DateTime::until`] or [`DateTime::since`]. It's also possible to subtract
/// two `DateTime` values directly via a `Sub` trait implementation:
///
/// ```
/// use jiff::{civil::date, ToSpan};
///
/// let datetime1 = date(2024, 5, 3).at(23, 30, 0, 0);
/// let datetime2 = date(2024, 2, 25).at(7, 0, 0, 0);
/// assert_eq!(datetime1 - datetime2, 68.days().hours(16).minutes(30));
/// ```
///
/// The `until` and `since` APIs are polymorphic and allow re-balancing and
/// rounding the span returned. For example, the default largest unit is days
/// (as exemplified above), but we can ask for bigger units:
///
/// ```
/// use jiff::{civil::date, ToSpan, Unit};
///
/// let datetime1 = date(2024, 5, 3).at(23, 30, 0, 0);
/// let datetime2 = date(2024, 2, 25).at(7, 0, 0, 0);
/// assert_eq!(
///     datetime1.since((Unit::Year, datetime2))?,
///     2.months().days(7).hours(16).minutes(30),
/// );
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// Or even round the span returned:
///
/// ```
/// use jiff::{civil::{DateTimeDifference, date}, RoundMode, ToSpan, Unit};
///
/// let datetime1 = date(2024, 5, 3).at(23, 30, 0, 0);
/// let datetime2 = date(2024, 2, 25).at(7, 0, 0, 0);
/// assert_eq!(
///     datetime1.since(
///         DateTimeDifference::new(datetime2)
///             .smallest(Unit::Day)
///             .largest(Unit::Year),
///     )?,
///     2.months().days(7),
/// );
/// // `DateTimeDifference` uses truncation as a rounding mode by default,
/// // but you can set the rounding mode to break ties away from zero:
/// assert_eq!(
///     datetime1.since(
///         DateTimeDifference::new(datetime2)
///             .smallest(Unit::Day)
///             .largest(Unit::Year)
///             .mode(RoundMode::HalfExpand),
///     )?,
///     // Rounds up to 8 days.
///     2.months().days(8),
/// );
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Rounding
///
/// A `DateTime` can be rounded based on a [`DateTimeRound`] configuration of
/// smallest units, rounding increment and rounding mode. Here's an example
/// showing how to round to the nearest third hour:
///
/// ```
/// use jiff::{civil::{DateTimeRound, date}, Unit};
///
/// let dt = date(2024, 6, 19).at(16, 27, 29, 999_999_999);
/// assert_eq!(
///     dt.round(DateTimeRound::new().smallest(Unit::Hour).increment(3))?,
///     date(2024, 6, 19).at(15, 0, 0, 0),
/// );
/// // Or alternatively, make use of the `From<(Unit, i64)> for DateTimeRound`
/// // trait implementation:
/// assert_eq!(
///     dt.round((Unit::Hour, 3))?,
///     date(2024, 6, 19).at(15, 0, 0, 0),
/// );
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// See [`DateTime::round`] for more details.
#[derive(Clone, Copy, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct DateTime {
    date: Date,
    time: Time,
}

impl DateTime {
    /// The minimum representable Gregorian datetime.
    ///
    /// The minimum is chosen such that any [`Timestamp`](crate::Timestamp)
    /// combined with any valid time zone offset can be infallibly converted to
    /// this type.
    pub const MIN: DateTime = datetime(-9999, 1, 1, 0, 0, 0, 0);

    /// The maximum representable Gregorian datetime.
    ///
    /// The maximum is chosen such that any [`Timestamp`](crate::Timestamp)
    /// combined with any valid time zone offset can be infallibly converted to
    /// this type.
    pub const MAX: DateTime = datetime(9999, 12, 31, 23, 59, 59, 999_999_999);

    /// The first day of the zeroth year.
    ///
    /// This is guaranteed to be equivalent to `DateTime::default()`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::DateTime;
    ///
    /// assert_eq!(DateTime::ZERO, DateTime::default());
    /// ```
    pub const ZERO: DateTime = DateTime::from_parts(Date::ZERO, Time::MIN);

    /// Creates a new `DateTime` value from its component year, month, day,
    /// hour, minute, second and fractional subsecond (up to nanosecond
    /// precision) values.
    ///
    /// To create a new datetime from another with a particular component, use
    /// the methods on [`DateTimeWith`] via [`DateTime::with`].
    ///
    /// # Errors
    ///
    /// This returns an error when the given components do not correspond to a
    /// valid datetime. Namely, all of the following must be true:
    ///
    /// * The year must be in the range `-9999..=9999`.
    /// * The month must be in the range `1..=12`.
    /// * The day must be at least `1` and must be at most the number of days
    /// in the corresponding month. So for example, `2024-02-29` is valid but
    /// `2023-02-29` is not.
    /// * `0 <= hour <= 23`
    /// * `0 <= minute <= 59`
    /// * `0 <= second <= 59`
    /// * `0 <= subsec_nanosecond <= 999,999,999`
    ///
    /// # Example
    ///
    /// This shows an example of a valid datetime:
    ///
    /// ```
    /// use jiff::civil::DateTime;
    ///
    /// let d = DateTime::new(2024, 2, 29, 21, 30, 5, 123_456_789).unwrap();
    /// assert_eq!(d.year(), 2024);
    /// assert_eq!(d.month(), 2);
    /// assert_eq!(d.day(), 29);
    /// assert_eq!(d.hour(), 21);
    /// assert_eq!(d.minute(), 30);
    /// assert_eq!(d.second(), 5);
    /// assert_eq!(d.millisecond(), 123);
    /// assert_eq!(d.microsecond(), 456);
    /// assert_eq!(d.nanosecond(), 789);
    /// ```
    ///
    /// This shows some examples of invalid datetimes:
    ///
    /// ```
    /// use jiff::civil::DateTime;
    ///
    /// assert!(DateTime::new(2023, 2, 29, 21, 30, 5, 0).is_err());
    /// assert!(DateTime::new(2015, 6, 30, 23, 59, 60, 0).is_err());
    /// assert!(DateTime::new(2024, 6, 20, 19, 58, 0, 1_000_000_000).is_err());
    /// ```
    #[inline]
    pub fn new(
        year: i16,
        month: i8,
        day: i8,
        hour: i8,
        minute: i8,
        second: i8,
        subsec_nanosecond: i32,
    ) -> Result<DateTime, Error> {
        let date = Date::new(year, month, day)?;
        let time = Time::new(hour, minute, second, subsec_nanosecond)?;
        Ok(DateTime { date, time })
    }

    /// Creates a new `DateTime` value in a `const` context.
    ///
    /// Note that an alternative syntax that is terser and perhaps easier to
    /// read for the same operation is to combine
    /// [`civil::date`](crate::civil::date()) with [`Date::at`].
    ///
    /// # Panics
    ///
    /// This routine panics when [`DateTime::new`] would return an error. That
    /// is, when the given components do not correspond to a valid datetime.
    /// Namely, all of the following must be true:
    ///
    /// * The year must be in the range `-9999..=9999`.
    /// * The month must be in the range `1..=12`.
    /// * The day must be at least `1` and must be at most the number of days
    /// in the corresponding month. So for example, `2024-02-29` is valid but
    /// `2023-02-29` is not.
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
    /// ```
    /// use jiff::civil::DateTime;
    ///
    /// let dt = DateTime::constant(2024, 2, 29, 21, 30, 5, 123_456_789);
    /// assert_eq!(dt.year(), 2024);
    /// assert_eq!(dt.month(), 2);
    /// assert_eq!(dt.day(), 29);
    /// assert_eq!(dt.hour(), 21);
    /// assert_eq!(dt.minute(), 30);
    /// assert_eq!(dt.second(), 5);
    /// assert_eq!(dt.millisecond(), 123);
    /// assert_eq!(dt.microsecond(), 456);
    /// assert_eq!(dt.nanosecond(), 789);
    /// ```
    ///
    /// Or alternatively:
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt = date(2024, 2, 29).at(21, 30, 5, 123_456_789);
    /// assert_eq!(dt.year(), 2024);
    /// assert_eq!(dt.month(), 2);
    /// assert_eq!(dt.day(), 29);
    /// assert_eq!(dt.hour(), 21);
    /// assert_eq!(dt.minute(), 30);
    /// assert_eq!(dt.second(), 5);
    /// assert_eq!(dt.millisecond(), 123);
    /// assert_eq!(dt.microsecond(), 456);
    /// assert_eq!(dt.nanosecond(), 789);
    /// ```
    #[inline]
    pub const fn constant(
        year: i16,
        month: i8,
        day: i8,
        hour: i8,
        minute: i8,
        second: i8,
        subsec_nanosecond: i32,
    ) -> DateTime {
        let date = Date::constant(year, month, day);
        let time = Time::constant(hour, minute, second, subsec_nanosecond);
        DateTime { date, time }
    }

    /// Creates a `DateTime` from its constituent parts.
    ///
    /// Any combination of a valid `Date` and a valid `Time` results in a valid
    /// `DateTime`.
    ///
    /// # Example
    ///
    /// This example shows how to build a datetime from its parts:
    ///
    /// ```
    /// use jiff::civil::{DateTime, date, time};
    ///
    /// let dt = DateTime::from_parts(date(2024, 6, 6), time(6, 0, 0, 0));
    /// assert_eq!(dt, date(2024, 6, 6).at(6, 0, 0, 0));
    /// ```
    #[inline]
    pub const fn from_parts(date: Date, time: Time) -> DateTime {
        DateTime { date, time }
    }

    /// Create a builder for constructing a new `DateTime` from the fields of
    /// this datetime.
    ///
    /// See the methods on [`DateTimeWith`] for the different ways one can set
    /// the fields of a new `DateTime`.
    ///
    /// # Example
    ///
    /// The builder ensures one can chain together the individual components of
    /// a datetime without it failing at an intermediate step. For example, if
    /// you had a date of `2024-10-31T00:00:00` and wanted to change both the
    /// day and the month, and each setting was validated independent of the
    /// other, you would need to be careful to set the day first and then the
    /// month. In some cases, you would need to set the month first and then
    /// the day!
    ///
    /// But with the builder, you can set values in any order:
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt1 = date(2024, 10, 31).at(0, 0, 0, 0);
    /// let dt2 = dt1.with().month(11).day(30).build()?;
    /// assert_eq!(dt2, date(2024, 11, 30).at(0, 0, 0, 0));
    ///
    /// let dt1 = date(2024, 4, 30).at(0, 0, 0, 0);
    /// let dt2 = dt1.with().day(31).month(7).build()?;
    /// assert_eq!(dt2, date(2024, 7, 31).at(0, 0, 0, 0));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn with(self) -> DateTimeWith {
        DateTimeWith::new(self)
    }

    /// Returns the year for this datetime.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt1 = date(2024, 3, 9).at(7, 30, 0, 0);
    /// assert_eq!(dt1.year(), 2024);
    ///
    /// let dt2 = date(-2024, 3, 9).at(7, 30, 0, 0);
    /// assert_eq!(dt2.year(), -2024);
    ///
    /// let dt3 = date(0, 3, 9).at(7, 30, 0, 0);
    /// assert_eq!(dt3.year(), 0);
    /// ```
    #[inline]
    pub fn year(self) -> i16 {
        self.date().year()
    }

    /// Returns the year and its era.
    ///
    /// This crate specifically allows years to be negative or `0`, where as
    /// years written for the Gregorian calendar are always positive and
    /// greater than `0`. In the Gregorian calendar, the era labels `BCE` and
    /// `CE` are used to disambiguate between years less than or equal to `0`
    /// and years greater than `0`, respectively.
    ///
    /// The crate is designed this way so that years in the latest era (that
    /// is, `CE`) are aligned with years in this crate.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::{Era, date};
    ///
    /// let dt = date(2024, 10, 3).at(7, 30, 0, 0);
    /// assert_eq!(dt.era_year(), (2024, Era::CE));
    ///
    /// let dt = date(1, 10, 3).at(7, 30, 0, 0);
    /// assert_eq!(dt.era_year(), (1, Era::CE));
    ///
    /// let dt = date(0, 10, 3).at(7, 30, 0, 0);
    /// assert_eq!(dt.era_year(), (1, Era::BCE));
    ///
    /// let dt = date(-1, 10, 3).at(7, 30, 0, 0);
    /// assert_eq!(dt.era_year(), (2, Era::BCE));
    ///
    /// let dt = date(-10, 10, 3).at(7, 30, 0, 0);
    /// assert_eq!(dt.era_year(), (11, Era::BCE));
    ///
    /// let dt = date(-9_999, 10, 3).at(7, 30, 0, 0);
    /// assert_eq!(dt.era_year(), (10_000, Era::BCE));
    /// ```
    #[inline]
    pub fn era_year(self) -> (i16, Era) {
        self.date().era_year()
    }

    /// Returns the month for this datetime.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt1 = date(2024, 3, 9).at(7, 30, 0, 0);
    /// assert_eq!(dt1.month(), 3);
    /// ```
    #[inline]
    pub fn month(self) -> i8 {
        self.date().month()
    }

    /// Returns the day for this datetime.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt1 = date(2024, 2, 29).at(7, 30, 0, 0);
    /// assert_eq!(dt1.day(), 29);
    /// ```
    #[inline]
    pub fn day(self) -> i8 {
        self.date().day()
    }

    /// Returns the "hour" component of this datetime.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt = date(2000, 1, 2).at(3, 4, 5, 123_456_789);
    /// assert_eq!(dt.hour(), 3);
    /// ```
    #[inline]
    pub fn hour(self) -> i8 {
        self.time().hour()
    }

    /// Returns the "minute" component of this datetime.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt = date(2000, 1, 2).at(3, 4, 5, 123_456_789);
    /// assert_eq!(dt.minute(), 4);
    /// ```
    #[inline]
    pub fn minute(self) -> i8 {
        self.time().minute()
    }

    /// Returns the "second" component of this datetime.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt = date(2000, 1, 2).at(3, 4, 5, 123_456_789);
    /// assert_eq!(dt.second(), 5);
    /// ```
    #[inline]
    pub fn second(self) -> i8 {
        self.time().second()
    }

    /// Returns the "millisecond" component of this datetime.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt = date(2000, 1, 2).at(3, 4, 5, 123_456_789);
    /// assert_eq!(dt.millisecond(), 123);
    /// ```
    #[inline]
    pub fn millisecond(self) -> i16 {
        self.time().millisecond()
    }

    /// Returns the "microsecond" component of this datetime.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt = date(2000, 1, 2).at(3, 4, 5, 123_456_789);
    /// assert_eq!(dt.microsecond(), 456);
    /// ```
    #[inline]
    pub fn microsecond(self) -> i16 {
        self.time().microsecond()
    }

    /// Returns the "nanosecond" component of this datetime.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt = date(2000, 1, 2).at(3, 4, 5, 123_456_789);
    /// assert_eq!(dt.nanosecond(), 789);
    /// ```
    #[inline]
    pub fn nanosecond(self) -> i16 {
        self.time().nanosecond()
    }

    /// Returns the fractional nanosecond for this `DateTime` value.
    ///
    /// If you want to set this value on `DateTime`, then use
    /// [`DateTimeWith::subsec_nanosecond`] via [`DateTime::with`].
    ///
    /// # Example
    ///
    /// This shows the relationship between constructing a `DateTime` value
    /// with routines like `with().millisecond()` and accessing the entire
    /// fractional part as a nanosecond:
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt1 = date(2000, 1, 2).at(3, 4, 5, 123_456_789);
    /// assert_eq!(dt1.subsec_nanosecond(), 123_456_789);
    /// let dt2 = dt1.with().millisecond(333).build()?;
    /// assert_eq!(dt2.subsec_nanosecond(), 333_456_789);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: nanoseconds from a timestamp
    ///
    /// This shows how the fractional nanosecond part of a `DateTime` value
    /// manifests from a specific timestamp.
    ///
    /// ```
    /// use jiff::{civil, Timestamp};
    ///
    /// // 1,234 nanoseconds after the Unix epoch.
    /// let zdt = Timestamp::new(0, 1_234)?.intz("UTC")?;
    /// let dt = zdt.datetime();
    /// assert_eq!(dt.subsec_nanosecond(), 1_234);
    ///
    /// // 1,234 nanoseconds before the Unix epoch.
    /// let zdt = Timestamp::new(0, -1_234)?.intz("UTC")?;
    /// let dt = zdt.datetime();
    /// // The nanosecond is equal to `1_000_000_000 - 1_234`.
    /// assert_eq!(dt.subsec_nanosecond(), 999998766);
    /// // Looking at the other components of the time value might help.
    /// assert_eq!(dt.hour(), 23);
    /// assert_eq!(dt.minute(), 59);
    /// assert_eq!(dt.second(), 59);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn subsec_nanosecond(self) -> i32 {
        self.time().subsec_nanosecond()
    }

    /// Returns the weekday corresponding to this datetime.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::{Weekday, date};
    ///
    /// // The Unix epoch was on a Thursday.
    /// let dt = date(1970, 1, 1).at(7, 30, 0, 0);
    /// assert_eq!(dt.weekday(), Weekday::Thursday);
    /// // One can also get the weekday as an offset in a variety of schemes.
    /// assert_eq!(dt.weekday().to_monday_zero_offset(), 3);
    /// assert_eq!(dt.weekday().to_monday_one_offset(), 4);
    /// assert_eq!(dt.weekday().to_sunday_zero_offset(), 4);
    /// assert_eq!(dt.weekday().to_sunday_one_offset(), 5);
    /// ```
    #[inline]
    pub fn weekday(self) -> Weekday {
        self.date().weekday()
    }

    /// Returns the ordinal day of the year that this datetime resides in.
    ///
    /// For leap years, this always returns a value in the range `1..=366`.
    /// Otherwise, the value is in the range `1..=365`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt = date(2006, 8, 24).at(7, 30, 0, 0);
    /// assert_eq!(dt.day_of_year(), 236);
    ///
    /// let dt = date(2023, 12, 31).at(7, 30, 0, 0);
    /// assert_eq!(dt.day_of_year(), 365);
    ///
    /// let dt = date(2024, 12, 31).at(7, 30, 0, 0);
    /// assert_eq!(dt.day_of_year(), 366);
    /// ```
    #[inline]
    pub fn day_of_year(self) -> i16 {
        self.date().day_of_year()
    }

    /// Returns the ordinal day of the year that this datetime resides in, but
    /// ignores leap years.
    ///
    /// That is, the range of possible values returned by this routine is
    /// `1..=365`, even if this date resides in a leap year. If this date is
    /// February 29, then this routine returns `None`.
    ///
    /// The value `365` always corresponds to the last day in the year,
    /// December 31, even for leap years.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt = date(2006, 8, 24).at(7, 30, 0, 0);
    /// assert_eq!(dt.day_of_year_no_leap(), Some(236));
    ///
    /// let dt = date(2023, 12, 31).at(7, 30, 0, 0);
    /// assert_eq!(dt.day_of_year_no_leap(), Some(365));
    ///
    /// let dt = date(2024, 12, 31).at(7, 30, 0, 0);
    /// assert_eq!(dt.day_of_year_no_leap(), Some(365));
    ///
    /// let dt = date(2024, 2, 29).at(7, 30, 0, 0);
    /// assert_eq!(dt.day_of_year_no_leap(), None);
    /// ```
    #[inline]
    pub fn day_of_year_no_leap(self) -> Option<i16> {
        self.date().day_of_year_no_leap()
    }

    /// Returns the beginning of the day that this datetime resides in.
    ///
    /// That is, the datetime returned always keeps the same date, but its
    /// time is always `00:00:00` (midnight).
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt = date(2024, 7, 3).at(7, 30, 10, 123_456_789);
    /// assert_eq!(dt.start_of_day(), date(2024, 7, 3).at(0, 0, 0, 0));
    /// ```
    #[inline]
    pub fn start_of_day(&self) -> DateTime {
        DateTime::from_parts(self.date(), Time::MIN)
    }

    /// Returns the end of the day that this datetime resides in.
    ///
    /// That is, the datetime returned always keeps the same date, but its
    /// time is always `23:59:59.999999999`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt = date(2024, 7, 3).at(7, 30, 10, 123_456_789);
    /// assert_eq!(
    ///     dt.end_of_day(),
    ///     date(2024, 7, 3).at(23, 59, 59, 999_999_999),
    /// );
    /// ```
    #[inline]
    pub fn end_of_day(&self) -> DateTime {
        DateTime::from_parts(self.date(), Time::MAX)
    }

    /// Returns the first date of the month that this datetime resides in.
    ///
    /// The time in the datetime returned remains unchanged.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt = date(2024, 2, 29).at(7, 30, 0, 0);
    /// assert_eq!(dt.first_of_month(), date(2024, 2, 1).at(7, 30, 0, 0));
    /// ```
    #[inline]
    pub fn first_of_month(self) -> DateTime {
        DateTime::from_parts(self.date().first_of_month(), self.time())
    }

    /// Returns the last date of the month that this datetime resides in.
    ///
    /// The time in the datetime returned remains unchanged.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt = date(2024, 2, 5).at(7, 30, 0, 0);
    /// assert_eq!(dt.last_of_month(), date(2024, 2, 29).at(7, 30, 0, 0));
    /// ```
    #[inline]
    pub fn last_of_month(self) -> DateTime {
        DateTime::from_parts(self.date().last_of_month(), self.time())
    }

    /// Returns the total number of days in the the month in which this
    /// datetime resides.
    ///
    /// This is guaranteed to always return one of the following values,
    /// depending on the year and the month: 28, 29, 30 or 31.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt = date(2024, 2, 10).at(7, 30, 0, 0);
    /// assert_eq!(dt.days_in_month(), 29);
    ///
    /// let dt = date(2023, 2, 10).at(7, 30, 0, 0);
    /// assert_eq!(dt.days_in_month(), 28);
    ///
    /// let dt = date(2024, 8, 15).at(7, 30, 0, 0);
    /// assert_eq!(dt.days_in_month(), 31);
    /// ```
    #[inline]
    pub fn days_in_month(self) -> i8 {
        self.date().days_in_month()
    }

    /// Returns the first date of the year that this datetime resides in.
    ///
    /// The time in the datetime returned remains unchanged.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt = date(2024, 2, 29).at(7, 30, 0, 0);
    /// assert_eq!(dt.first_of_year(), date(2024, 1, 1).at(7, 30, 0, 0));
    /// ```
    #[inline]
    pub fn first_of_year(self) -> DateTime {
        DateTime::from_parts(self.date().first_of_year(), self.time())
    }

    /// Returns the last date of the year that this datetime resides in.
    ///
    /// The time in the datetime returned remains unchanged.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt = date(2024, 2, 5).at(7, 30, 0, 0);
    /// assert_eq!(dt.last_of_year(), date(2024, 12, 31).at(7, 30, 0, 0));
    /// ```
    #[inline]
    pub fn last_of_year(self) -> DateTime {
        DateTime::from_parts(self.date().last_of_year(), self.time())
    }

    /// Returns the total number of days in the the year in which this datetime
    /// resides.
    ///
    /// This is guaranteed to always return either `365` or `366`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt = date(2024, 7, 10).at(7, 30, 0, 0);
    /// assert_eq!(dt.days_in_year(), 366);
    ///
    /// let dt = date(2023, 7, 10).at(7, 30, 0, 0);
    /// assert_eq!(dt.days_in_year(), 365);
    /// ```
    #[inline]
    pub fn days_in_year(self) -> i16 {
        self.date().days_in_year()
    }

    /// Returns true if and only if the year in which this datetime resides is
    /// a leap year.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// assert!(date(2024, 1, 1).at(7, 30, 0, 0).in_leap_year());
    /// assert!(!date(2023, 12, 31).at(7, 30, 0, 0).in_leap_year());
    /// ```
    #[inline]
    pub fn in_leap_year(self) -> bool {
        self.date().in_leap_year()
    }

    /// Returns the datetime with a date immediately following this one.
    ///
    /// The time in the datetime returned remains unchanged.
    ///
    /// # Errors
    ///
    /// This returns an error when this datetime's date is the maximum value.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::{DateTime, date};
    ///
    /// let dt = date(2024, 2, 28).at(7, 30, 0, 0);
    /// assert_eq!(dt.tomorrow()?, date(2024, 2, 29).at(7, 30, 0, 0));
    ///
    /// // The max doesn't have a tomorrow.
    /// assert!(DateTime::MAX.tomorrow().is_err());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn tomorrow(self) -> Result<DateTime, Error> {
        Ok(DateTime::from_parts(self.date().tomorrow()?, self.time()))
    }

    /// Returns the datetime with a date immediately preceding this one.
    ///
    /// The time in the datetime returned remains unchanged.
    ///
    /// # Errors
    ///
    /// This returns an error when this datetime's date is the minimum value.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::{DateTime, date};
    ///
    /// let dt = date(2024, 3, 1).at(7, 30, 0, 0);
    /// assert_eq!(dt.yesterday()?, date(2024, 2, 29).at(7, 30, 0, 0));
    ///
    /// // The min doesn't have a yesterday.
    /// assert!(DateTime::MIN.yesterday().is_err());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn yesterday(self) -> Result<DateTime, Error> {
        Ok(DateTime::from_parts(self.date().yesterday()?, self.time()))
    }

    /// Returns the "nth" weekday from the beginning or end of the month in
    /// which this datetime resides.
    ///
    /// The `nth` parameter can be positive or negative. A positive value
    /// computes the "nth" weekday from the beginning of the month. A negative
    /// value computes the "nth" weekday from the end of the month. So for
    /// example, use `-1` to "find the last weekday" in this date's month.
    ///
    /// The time in the datetime returned remains unchanged.
    ///
    /// # Errors
    ///
    /// This returns an error when `nth` is `0`, or if it is `5` or `-5` and
    /// there is no 5th weekday from the beginning or end of the month.
    ///
    /// # Example
    ///
    /// This shows how to get the nth weekday in a month, starting from the
    /// beginning of the month:
    ///
    /// ```
    /// use jiff::civil::{Weekday, date};
    ///
    /// let dt = date(2017, 3, 1).at(7, 30, 0, 0);
    /// let second_friday = dt.nth_weekday_of_month(2, Weekday::Friday)?;
    /// assert_eq!(second_friday, date(2017, 3, 10).at(7, 30, 0, 0));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// This shows how to do the reverse of the above. That is, the nth _last_
    /// weekday in a month:
    ///
    /// ```
    /// use jiff::civil::{Weekday, date};
    ///
    /// let dt = date(2024, 3, 1).at(7, 30, 0, 0);
    /// let last_thursday = dt.nth_weekday_of_month(-1, Weekday::Thursday)?;
    /// assert_eq!(last_thursday, date(2024, 3, 28).at(7, 30, 0, 0));
    /// let second_last_thursday = dt.nth_weekday_of_month(
    ///     -2,
    ///     Weekday::Thursday,
    /// )?;
    /// assert_eq!(second_last_thursday, date(2024, 3, 21).at(7, 30, 0, 0));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// This routine can return an error if there isn't an `nth` weekday
    /// for this month. For example, March 2024 only has 4 Mondays:
    ///
    /// ```
    /// use jiff::civil::{Weekday, date};
    ///
    /// let dt = date(2024, 3, 25).at(7, 30, 0, 0);
    /// let fourth_monday = dt.nth_weekday_of_month(4, Weekday::Monday)?;
    /// assert_eq!(fourth_monday, date(2024, 3, 25).at(7, 30, 0, 0));
    /// // There is no 5th Monday.
    /// assert!(dt.nth_weekday_of_month(5, Weekday::Monday).is_err());
    /// // Same goes for counting backwards.
    /// assert!(dt.nth_weekday_of_month(-5, Weekday::Monday).is_err());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn nth_weekday_of_month(
        self,
        nth: i8,
        weekday: Weekday,
    ) -> Result<DateTime, Error> {
        let date = self.date().nth_weekday_of_month(nth, weekday)?;
        Ok(DateTime::from_parts(date, self.time()))
    }

    /// Returns the "nth" weekday from this datetime, not including itself.
    ///
    /// The `nth` parameter can be positive or negative. A positive value
    /// computes the "nth" weekday starting at the day after this date and
    /// going forwards in time. A negative value computes the "nth" weekday
    /// starting at the day before this date and going backwards in time.
    ///
    /// For example, if this datetime's weekday is a Sunday and the first
    /// Sunday is asked for (that is, `dt.nth_weekday(1, Weekday::Sunday)`),
    /// then the result is a week from this datetime corresponding to the
    /// following Sunday.
    ///
    /// The time in the datetime returned remains unchanged.
    ///
    /// # Errors
    ///
    /// This returns an error when `nth` is `0`, or if it would otherwise
    /// result in a date that overflows the minimum/maximum values of
    /// `DateTime`.
    ///
    /// # Example
    ///
    /// This example shows how to find the "nth" weekday going forwards in
    /// time:
    ///
    /// ```
    /// use jiff::civil::{Weekday, date};
    ///
    /// // Use a Sunday in March as our start date.
    /// let dt = date(2024, 3, 10).at(7, 30, 0, 0);
    /// assert_eq!(dt.weekday(), Weekday::Sunday);
    ///
    /// // The first next Monday is tomorrow!
    /// let next_monday = dt.nth_weekday(1, Weekday::Monday)?;
    /// assert_eq!(next_monday, date(2024, 3, 11).at(7, 30, 0, 0));
    ///
    /// // But the next Sunday is a week away, because this doesn't
    /// // include the current weekday.
    /// let next_sunday = dt.nth_weekday(1, Weekday::Sunday)?;
    /// assert_eq!(next_sunday, date(2024, 3, 17).at(7, 30, 0, 0));
    ///
    /// // "not this Thursday, but next Thursday"
    /// let next_next_thursday = dt.nth_weekday(2, Weekday::Thursday)?;
    /// assert_eq!(next_next_thursday, date(2024, 3, 21).at(7, 30, 0, 0));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// This example shows how to find the "nth" weekday going backwards in
    /// time:
    ///
    /// ```
    /// use jiff::civil::{Weekday, date};
    ///
    /// // Use a Sunday in March as our start date.
    /// let dt = date(2024, 3, 10).at(7, 30, 0, 0);
    /// assert_eq!(dt.weekday(), Weekday::Sunday);
    ///
    /// // "last Saturday" was yesterday!
    /// let last_saturday = dt.nth_weekday(-1, Weekday::Saturday)?;
    /// assert_eq!(last_saturday, date(2024, 3, 9).at(7, 30, 0, 0));
    ///
    /// // "last Sunday" was a week ago.
    /// let last_sunday = dt.nth_weekday(-1, Weekday::Sunday)?;
    /// assert_eq!(last_sunday, date(2024, 3, 3).at(7, 30, 0, 0));
    ///
    /// // "not last Thursday, but the one before"
    /// let prev_prev_thursday = dt.nth_weekday(-2, Weekday::Thursday)?;
    /// assert_eq!(prev_prev_thursday, date(2024, 2, 29).at(7, 30, 0, 0));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// This example shows that overflow results in an error in either
    /// direction:
    ///
    /// ```
    /// use jiff::civil::{DateTime, Weekday};
    ///
    /// let dt = DateTime::MAX;
    /// assert_eq!(dt.weekday(), Weekday::Friday);
    /// assert!(dt.nth_weekday(1, Weekday::Saturday).is_err());
    ///
    /// let dt = DateTime::MIN;
    /// assert_eq!(dt.weekday(), Weekday::Monday);
    /// assert!(dt.nth_weekday(-1, Weekday::Sunday).is_err());
    /// ```
    ///
    /// # Example: the start of Israeli summer time
    ///
    /// Israeli law says (at present, as of 2024-03-11) that DST or
    /// "summer time" starts on the Friday before the last Sunday in
    /// March. We can find that date using both `nth_weekday` and
    /// [`DateTime::nth_weekday_of_month`]:
    ///
    /// ```
    /// use jiff::civil::{Weekday, date};
    ///
    /// let march = date(2024, 3, 1).at(0, 0, 0, 0);
    /// let last_sunday = march.nth_weekday_of_month(-1, Weekday::Sunday)?;
    /// let dst_starts_on = last_sunday.nth_weekday(-1, Weekday::Friday)?;
    /// assert_eq!(dst_starts_on, date(2024, 3, 29).at(0, 0, 0, 0));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: getting the start of the week
    ///
    /// Given a date, one can use `nth_weekday` to determine the start of the
    /// week in which the date resides in. This might vary based on whether
    /// the weeks start on Sunday or Monday. This example shows how to handle
    /// both.
    ///
    /// ```
    /// use jiff::civil::{Weekday, date};
    ///
    /// let dt = date(2024, 3, 15).at(7, 30, 0, 0);
    /// // For weeks starting with Sunday.
    /// let start_of_week = dt.tomorrow()?.nth_weekday(-1, Weekday::Sunday)?;
    /// assert_eq!(start_of_week, date(2024, 3, 10).at(7, 30, 0, 0));
    /// // For weeks starting with Monday.
    /// let start_of_week = dt.tomorrow()?.nth_weekday(-1, Weekday::Monday)?;
    /// assert_eq!(start_of_week, date(2024, 3, 11).at(7, 30, 0, 0));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// In the above example, we first get the date after the current one
    /// because `nth_weekday` does not consider itself when counting. This
    /// works as expected even at the boundaries of a week:
    ///
    /// ```
    /// use jiff::civil::{Time, Weekday, date};
    ///
    /// // The start of the week.
    /// let dt = date(2024, 3, 10).at(0, 0, 0, 0);
    /// let start_of_week = dt.tomorrow()?.nth_weekday(-1, Weekday::Sunday)?;
    /// assert_eq!(start_of_week, date(2024, 3, 10).at(0, 0, 0, 0));
    /// // The end of the week.
    /// let dt = date(2024, 3, 16).at(23, 59, 59, 999_999_999);
    /// let start_of_week = dt
    ///     .tomorrow()?
    ///     .nth_weekday(-1, Weekday::Sunday)?
    ///     .with().time(Time::midnight()).build()?;
    /// assert_eq!(start_of_week, date(2024, 3, 10).at(0, 0, 0, 0));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn nth_weekday(
        self,
        nth: i32,
        weekday: Weekday,
    ) -> Result<DateTime, Error> {
        let date = self.date().nth_weekday(nth, weekday)?;
        Ok(DateTime::from_parts(date, self.time()))
    }

    /// Returns the date component of this datetime.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt = date(2024, 3, 14).at(18, 45, 0, 0);
    /// assert_eq!(dt.date(), date(2024, 3, 14));
    /// ```
    #[inline]
    pub fn date(self) -> Date {
        self.date
    }

    /// Returns the time component of this datetime.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::{date, time};
    ///
    /// let dt = date(2024, 3, 14).at(18, 45, 0, 0);
    /// assert_eq!(dt.time(), time(18, 45, 0, 0));
    /// ```
    #[inline]
    pub fn time(self) -> Time {
        self.time
    }

    /// Converts a civil datetime to a [`Zoned`] datetime by adding the given
    /// time zone.
    ///
    /// The name given is resolved to a [`TimeZone`] by using the default
    /// [`TimeZoneDatabase`](crate::tz::TimeZoneDatabase) created by
    /// [`tz::db`](crate::tz::db). Indeed, this is a convenience function for
    /// [`DateTime::to_zoned`] where the time zone database lookup is done
    /// automatically.
    ///
    /// In some cases, a civil datetime may be ambiguous in a
    /// particular time zone. This routine automatically utilizes the
    /// [`Disambiguation::Compatible`](crate::tz::Disambiguation) strategy
    /// for resolving ambiguities. That is, if a civil datetime occurs in a
    /// backward transition (called a fold), then the earlier time is selected.
    /// Or if a civil datetime occurs in a forward transition (called a gap),
    /// then the later time is selected.
    ///
    /// To convert a datetime to a `Zoned` using a different disambiguation
    /// strategy, use [`TimeZone::to_ambiguous_zoned`].
    ///
    /// # Errors
    ///
    /// This returns an error when the given time zone name could not be found
    /// in the default time zone database.
    ///
    /// This also returns an error if this datetime could not be represented as
    /// an instant. This can occur in some cases near the minimum and maximum
    /// boundaries of a `DateTime`.
    ///
    /// # Example
    ///
    /// This is a simple example of converting a civil datetime (a "wall" or
    /// "local" or "naive" datetime) to a datetime that is aware of its time
    /// zone:
    ///
    /// ```
    /// use jiff::civil::DateTime;
    ///
    /// let dt: DateTime = "2024-06-20 15:06".parse()?;
    /// let zdt = dt.intz("America/New_York")?;
    /// assert_eq!(zdt.to_string(), "2024-06-20T15:06:00-04:00[America/New_York]");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: dealing with ambiguity
    ///
    /// In the `America/New_York` time zone, there was a forward transition
    /// at `2024-03-10 02:00:00` civil time, and a backward transition at
    /// `2024-11-03 01:00:00` civil time. In the former case, a gap was
    /// created such that the 2 o'clock hour never appeared on clocks for folks
    /// in the `America/New_York` time zone. In the latter case, a fold was
    /// created such that the 1 o'clock hour was repeated. Thus, March 10, 2024
    /// in New York was 23 hours long, while November 3, 2024 in New York was
    /// 25 hours long.
    ///
    /// This example shows how datetimes in these gaps and folds are resolved
    /// by default:
    ///
    /// ```
    /// use jiff::civil::DateTime;
    ///
    /// // This is the gap, where by default we select the later time.
    /// let dt: DateTime = "2024-03-10 02:30".parse()?;
    /// let zdt = dt.intz("America/New_York")?;
    /// assert_eq!(zdt.to_string(), "2024-03-10T03:30:00-04:00[America/New_York]");
    ///
    /// // This is the fold, where by default we select the earlier time.
    /// let dt: DateTime = "2024-11-03 01:30".parse()?;
    /// let zdt = dt.intz("America/New_York")?;
    /// // Since this is a fold, the wall clock time is repeated. It might be
    /// // hard to see that this is the earlier time, but notice the offset:
    /// // it is the offset for DST time in New York. The later time, or the
    /// // repetition of the 1 o'clock hour, would occur in standard time,
    /// // which is an offset of -05 for New York.
    /// assert_eq!(zdt.to_string(), "2024-11-03T01:30:00-04:00[America/New_York]");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: errors
    ///
    /// This routine can return an error when the time zone is unrecognized:
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt = date(2024, 6, 20).at(15, 6, 0, 0);
    /// assert!(dt.intz("does not exist").is_err());
    /// ```
    ///
    /// Note that even if a time zone exists in, say, the IANA database, there
    /// may have been a problem reading it from your system's installation of
    /// that database. To see what wrong, enable Jiff's `logging` crate feature
    /// and install a logger. If there was a failure, then a `WARN` level log
    /// message should be emitted.
    ///
    /// This routine can also fail if this datetime cannot be represented
    /// within the allowable timestamp limits:
    ///
    /// ```
    /// use jiff::{civil::DateTime, tz::{Offset, TimeZone}};
    ///
    /// let dt = DateTime::MAX;
    /// // All errors because the combination of the offset and the datetime
    /// // isn't enough to fit into timestamp limits.
    /// assert!(dt.intz("UTC").is_err());
    /// assert!(dt.intz("America/New_York").is_err());
    /// assert!(dt.intz("Australia/Tasmania").is_err());
    /// // In fact, the only valid offset one can use to turn the maximum civil
    /// // datetime into a Zoned value is the maximum offset:
    /// let tz = Offset::from_seconds(93_599).unwrap().to_time_zone();
    /// assert!(dt.to_zoned(tz).is_ok());
    /// // One second less than the maximum offset results in a failure at the
    /// // maximum datetime boundary.
    /// let tz = Offset::from_seconds(93_598).unwrap().to_time_zone();
    /// assert!(dt.to_zoned(tz).is_err());
    /// ```
    ///
    /// This behavior exists because it guarantees that every possible `Zoned`
    /// value can be converted into a civil datetime, but not every possible
    /// combination of civil datetime and offset can be converted into a
    /// `Zoned` value. There isn't a way to make every possible roundtrip
    /// lossless in both directions, so Jiff chooses to ensure that there is
    /// always a way to convert a `Zoned` instant to a human readable wall
    /// clock time.
    #[inline]
    pub fn intz(self, time_zone_name: &str) -> Result<Zoned, Error> {
        let tz = crate::tz::db().get(time_zone_name)?;
        self.to_zoned(tz)
    }

    /// Converts a civil datetime to a [`Zoned`] datetime by adding the given
    /// [`TimeZone`].
    ///
    /// In some cases, a civil datetime may be ambiguous in a
    /// particular time zone. This routine automatically utilizes the
    /// [`Disambiguation::Compatible`](crate::tz::Disambiguation) strategy
    /// for resolving ambiguities. That is, if a civil datetime occurs in a
    /// backward transition (called a fold), then the earlier time is selected.
    /// Or if a civil datetime occurs in a forward transition (called a gap),
    /// then the later time is selected.
    ///
    /// To convert a datetime to a `Zoned` using a different disambiguation
    /// strategy, use [`TimeZone::to_ambiguous_zoned`].
    ///
    /// In the common case of a time zone being represented as a name string,
    /// like `Australia/Tasmania`, consider using [`DateTime::to_zoned`]
    /// instead.
    ///
    /// # Errors
    ///
    /// This returns an error if this datetime could not be represented as an
    /// instant. This can occur in some cases near the minimum and maximum
    /// boundaries of a `DateTime`.
    ///
    /// # Example
    ///
    /// This example shows how to created a zoned value with a fixed time zone
    /// offset:
    ///
    /// ```
    /// use jiff::{civil::date, tz::{self, TimeZone}};
    ///
    /// let tz = TimeZone::fixed(tz::offset(-4));
    /// let zdt = date(2024, 6, 20).at(17, 3, 0, 0).to_zoned(tz)?;
    /// // A time zone annotation is still included in the printable version
    /// // of the Zoned value, but it is fixed to a particular offset.
    /// assert_eq!(zdt.to_string(), "2024-06-20T17:03:00-04:00[-04:00]");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: POSIX time zone strings
    ///
    /// And this example shows how to create a time zone from a POSIX time
    /// zone string that describes the transition to and from daylight saving
    /// time for `America/St_Johns`. In particular, this rule uses non-zero
    /// minutes, which is atypical.
    ///
    /// ```
    /// use jiff::{civil::date, tz::TimeZone};
    ///
    /// let tz = TimeZone::posix("NST3:30NDT,M3.2.0,M11.1.0")?;
    /// let zdt = date(2024, 6, 20).at(17, 3, 0, 0).to_zoned(tz)?;
    /// // There isn't any agreed upon mechanism for transmitting a POSIX time
    /// // zone string within an RFC 9557 TZ annotation, so Jiff just emits the
    /// // offset. In practice, POSIX TZ strings are rarely user facing anyway.
    /// // (They are still in widespread use as an implementation detail of the
    /// // IANA Time Zone Database however.)
    /// assert_eq!(zdt.to_string(), "2024-06-20T17:03:00-02:30[-02:30]");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn to_zoned(self, tz: TimeZone) -> Result<Zoned, Error> {
        tz.into_ambiguous_zoned(self).compatible()
    }

    /// Add the given span of time to this datetime. If the sum would overflow
    /// the minimum or maximum datetime values, then an error is returned.
    ///
    /// # Properties
    ///
    /// This routine is _not_ reversible because some additions may
    /// be ambiguous. For example, adding `1 month` to the datetime
    /// `2024-03-31T00:00:00` will produce `2024-04-30T00:00:00` since April
    /// has only 30 days in a month. Moreover, subtracting `1 month` from
    /// `2024-04-30T00:00:00` will produce `2024-03-30T00:00:00`, which is not
    /// the date we started with.
    ///
    /// If spans of time are limited to units of days (or less), then this
    /// routine _is_ reversible.
    ///
    /// # Errors
    ///
    /// If the span added to this datetime would result in a datetime that
    /// exceeds the range of a `DateTime`, then this will return an error.
    ///
    /// # Example
    ///
    /// This shows a few examples of adding spans of time to various dates.
    /// We make use of the [`ToSpan`](crate::ToSpan) trait for convenient
    /// creation of spans.
    ///
    /// ```
    /// use jiff::{civil::date, ToSpan};
    ///
    /// let dt = date(1995, 12, 7).at(3, 24, 30, 3_500);
    /// let got = dt.checked_add(20.years().months(4).nanoseconds(500))?;
    /// assert_eq!(got, date(2016, 4, 7).at(3, 24, 30, 4_000));
    ///
    /// let dt = date(2019, 1, 31).at(15, 30, 0, 0);
    /// let got = dt.checked_add(1.months())?;
    /// assert_eq!(got, date(2019, 2, 28).at(15, 30, 0, 0));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: available via addition operator
    ///
    /// This routine can be used via the `+` operator. Note though that if it
    /// fails, it will result in a panic.
    ///
    /// ```
    /// use jiff::{civil::date, ToSpan};
    ///
    /// let dt = date(1995, 12, 7).at(3, 24, 30, 3_500);
    /// let got = dt + 20.years().months(4).nanoseconds(500);
    /// assert_eq!(got, date(2016, 4, 7).at(3, 24, 30, 4_000));
    /// ```
    ///
    /// # Example: negative spans are supported
    ///
    /// ```
    /// # // See: https://github.com/rust-lang/rust/pull/121364
    /// # #![allow(unknown_lints, ambiguous_negative_literals)]
    /// use jiff::{civil::date, ToSpan};
    ///
    /// let dt = date(2024, 3, 31).at(19, 5, 59, 999_999_999);
    /// assert_eq!(
    ///     dt.checked_add(-1.months())?,
    ///     date(2024, 2, 29).at(19, 5, 59, 999_999_999),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: error on overflow
    ///
    /// ```
    /// # // See: https://github.com/rust-lang/rust/pull/121364
    /// # #![allow(unknown_lints, ambiguous_negative_literals)]
    /// use jiff::{civil::date, ToSpan};
    ///
    /// let dt = date(2024, 3, 31).at(13, 13, 13, 13);
    /// assert!(dt.checked_add(9000.years()).is_err());
    /// assert!(dt.checked_add(-19000.years()).is_err());
    /// ```
    #[inline]
    pub fn checked_add(self, span: Span) -> Result<DateTime, Error> {
        let (date, time) = (self.date(), self.time());
        let span_date = span.without_lower(Unit::Day);
        let span_time = span.only_lower(Unit::Day);

        let (new_time, leftovers) = time
            .overflowing_add(span_time)
            .with_context(|| err!("failed to add {span_time} to {time}"))?;
        let new_date = date
            .checked_add(span_date)
            .with_context(|| err!("failed to add {span_date} to {date}"))?;
        let new_date = new_date.checked_add(leftovers).with_context(|| {
            err!(
                "failed to add overflowing span, {leftovers}, \
                 from adding {span_time} to {time}, \
                 to {new_date}",
            )
        })?;
        Ok(DateTime::from_parts(new_date, new_time))
    }

    /// Subtract the given span of time from this datetime. If the difference
    /// would overflow the minimum or maximum datetime values, then an error is
    /// returned.
    ///
    /// # Properties
    ///
    /// This routine is _not_ reversible because some additions may
    /// be ambiguous. For example, adding `1 month` to the datetime
    /// `2024-03-31T00:00:00` will produce `2024-04-30T00:00:00` since April
    /// has only 30 days in a month. Moreover, subtracting `1 month` from
    /// `2024-04-30T00:00:00` will produce `2024-03-30T00:00:00`, which is not
    /// the date we started with.
    ///
    /// If spans of time are limited to units of days (or less), then this
    /// routine _is_ reversible.
    ///
    /// # Errors
    ///
    /// If the span subtracted from this datetime would result in a datetime
    /// that exceeds the range of a `DateTime`, then this will return an error.
    ///
    /// # Example
    ///
    /// This shows a few examples of subtracting spans of time to various
    /// dates. We make use of the [`ToSpan`](crate::ToSpan) trait for
    /// convenient creation of spans.
    ///
    /// ```
    /// use jiff::{civil::date, ToSpan};
    ///
    /// let dt = date(1995, 12, 7).at(3, 24, 30, 3_500);
    /// let got = dt.checked_sub(20.years().months(4).nanoseconds(500))?;
    /// assert_eq!(got, date(1975, 8, 7).at(3, 24, 30, 3_000));
    ///
    /// let dt = date(2019, 2, 28).at(15, 30, 0, 0);
    /// let got = dt.checked_sub(1.months())?;
    /// assert_eq!(got, date(2019, 1, 28).at(15, 30, 0, 0));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: available via subtraction operator
    ///
    /// This routine can be used via the `-` operator. Note though that if it
    /// fails, it will result in a panic.
    ///
    /// ```
    /// use jiff::{civil::date, ToSpan};
    ///
    /// let dt = date(1995, 12, 7).at(3, 24, 30, 3_500);
    /// let got = dt - 20.years().months(4).nanoseconds(500);
    /// assert_eq!(got, date(1975, 8, 7).at(3, 24, 30, 3_000));
    /// ```
    ///
    /// # Example: negative spans are supported
    ///
    /// ```
    /// # // See: https://github.com/rust-lang/rust/pull/121364
    /// # #![allow(unknown_lints, ambiguous_negative_literals)]
    /// use jiff::{civil::date, ToSpan};
    ///
    /// let dt = date(2024, 3, 31).at(19, 5, 59, 999_999_999);
    /// assert_eq!(
    ///     dt.checked_sub(-1.months())?,
    ///     date(2024, 4, 30).at(19, 5, 59, 999_999_999),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: error on overflow
    ///
    /// ```
    /// # // See: https://github.com/rust-lang/rust/pull/121364
    /// # #![allow(unknown_lints, ambiguous_negative_literals)]
    /// use jiff::{civil::date, ToSpan};
    ///
    /// let dt = date(2024, 3, 31).at(13, 13, 13, 13);
    /// assert!(dt.checked_sub(19000.years()).is_err());
    /// assert!(dt.checked_sub(-9000.years()).is_err());
    /// ```
    #[inline]
    pub fn checked_sub(self, span: Span) -> Result<DateTime, Error> {
        self.checked_add(-span)
    }

    /// Add the given span of time to this datetime. If the sum would overflow
    /// the minimum or maximum datetime values, then the result saturates.
    ///
    /// # Properties
    ///
    /// This routine is _not_ reversible because some additions may
    /// be ambiguous. For example, adding `1 month` to the datetime
    /// `2024-03-31T00:00:00` will produce `2024-04-30T00:00:00` since April
    /// has only 30 days in a month. Moreover, subtracting `1 month` from
    /// `2024-04-30T00:00:00` will produce `2024-03-30T00:00:00`, which is not
    /// the date we started with.
    ///
    /// If spans of time are limited to units of days (or less), and no
    /// saturation occurs, then this routine _is_ reversible.
    ///
    /// # Example
    ///
    /// This shows a few examples of adding spans of time to various dates.
    /// We make use of the [`ToSpan`](crate::ToSpan) trait for convenient
    /// creation of spans.
    ///
    /// ```
    /// use jiff::{civil::date, ToSpan};
    ///
    /// let dt = date(1995, 12, 7).at(3, 24, 30, 3_500);
    /// let got = dt.saturating_add(20.years().months(4).nanoseconds(500));
    /// assert_eq!(got, date(2016, 4, 7).at(3, 24, 30, 4_000));
    ///
    /// let dt = date(2019, 1, 31).at(15, 30, 0, 0);
    /// let got = dt.saturating_add(1.months());
    /// assert_eq!(got, date(2019, 2, 28).at(15, 30, 0, 0));
    /// ```
    ///
    /// # Example: negative spans are supported
    ///
    /// ```
    /// # // See: https://github.com/rust-lang/rust/pull/121364
    /// # #![allow(unknown_lints, ambiguous_negative_literals)]
    /// use jiff::{civil::date, ToSpan};
    ///
    /// let dt = date(2024, 3, 31).at(19, 5, 59, 999_999_999);
    /// assert_eq!(
    ///     dt.saturating_add(-1.months()),
    ///     date(2024, 2, 29).at(19, 5, 59, 999_999_999),
    /// );
    /// ```
    ///
    /// # Example: saturation on overflow
    ///
    /// ```
    /// # // See: https://github.com/rust-lang/rust/pull/121364
    /// # #![allow(unknown_lints, ambiguous_negative_literals)]
    /// use jiff::{civil::{DateTime, date}, ToSpan};
    ///
    /// let dt = date(2024, 3, 31).at(13, 13, 13, 13);
    /// assert_eq!(DateTime::MAX, dt.saturating_add(9000.years()));
    /// assert_eq!(DateTime::MIN, dt.saturating_add(-19000.years()));
    /// ```
    #[inline]
    pub fn saturating_add(self, span: Span) -> DateTime {
        self.checked_add(span).unwrap_or_else(|_| {
            if span.is_negative() {
                DateTime::MIN
            } else {
                DateTime::MAX
            }
        })
    }

    /// Subtract the given span of time from this datetime. If the difference
    /// would overflow the minimum or maximum datetime values, then the result
    /// saturates.
    ///
    /// # Properties
    ///
    /// This routine is _not_ reversible because some additions may
    /// be ambiguous. For example, adding `1 month` to the datetime
    /// `2024-03-31T00:00:00` will produce `2024-04-30T00:00:00` since April
    /// has only 30 days in a month. Moreover, subtracting `1 month` from
    /// `2024-04-30T00:00:00` will produce `2024-03-30T00:00:00`, which is not
    /// the date we started with.
    ///
    /// If spans of time are limited to units of days (or less), and no
    /// saturation occurs, then this routine _is_ reversible.
    ///
    /// # Example
    ///
    /// This shows a few examples of subtracting spans of time to various
    /// dates. We make use of the [`ToSpan`](crate::ToSpan) trait for
    /// convenient creation of spans.
    ///
    /// ```
    /// use jiff::{civil::date, ToSpan};
    ///
    /// let dt = date(1995, 12, 7).at(3, 24, 30, 3_500);
    /// let got = dt.saturating_sub(20.years().months(4).nanoseconds(500));
    /// assert_eq!(got, date(1975, 8, 7).at(3, 24, 30, 3_000));
    ///
    /// let dt = date(2019, 2, 28).at(15, 30, 0, 0);
    /// let got = dt.saturating_sub(1.months());
    /// assert_eq!(got, date(2019, 1, 28).at(15, 30, 0, 0));
    /// ```
    ///
    /// # Example: negative spans are supported
    ///
    /// ```
    /// # // See: https://github.com/rust-lang/rust/pull/121364
    /// # #![allow(unknown_lints, ambiguous_negative_literals)]
    /// use jiff::{civil::date, ToSpan};
    ///
    /// let dt = date(2024, 3, 31).at(19, 5, 59, 999_999_999);
    /// assert_eq!(
    ///     dt.saturating_sub(-1.months()),
    ///     date(2024, 4, 30).at(19, 5, 59, 999_999_999),
    /// );
    /// ```
    ///
    /// # Example: saturation on overflow
    ///
    /// ```
    /// # // See: https://github.com/rust-lang/rust/pull/121364
    /// # #![allow(unknown_lints, ambiguous_negative_literals)]
    /// use jiff::{civil::{DateTime, date}, ToSpan};
    ///
    /// let dt = date(2024, 3, 31).at(13, 13, 13, 13);
    /// assert_eq!(DateTime::MIN, dt.saturating_sub(19000.years()));
    /// assert_eq!(DateTime::MAX, dt.saturating_sub(-9000.years()));
    /// ```
    #[inline]
    pub fn saturating_sub(self, span: Span) -> DateTime {
        self.saturating_add(-span)
    }

    /// Returns a span representing the elapsed time from this datetime since
    /// the given `other` datetime.
    ///
    /// When `other` occurs after this datetime, then the span returned will
    /// be negative.
    ///
    /// Depending on the input provided, the span returned is rounded. It may
    /// also be balanced up to bigger units than the default. By default, the
    /// span returned is balanced such that the biggest possible unit is days.
    ///
    /// This operation is configured by providing a [`DateTimeDifference`]
    /// value. Since this routine accepts anything that implements
    /// `Into<DateTimeDifference>`, once can pass a `DateTime` directly.
    /// One can also pass a `(Unit, DateTime)`, where `Unit` is treated as
    /// [`DateTimeDifference::largest`].
    ///
    /// # Properties
    ///
    /// It is guaranteed that if the returned span is added to `other`, and if
    /// no rounding is requested, and if the largest unit requested is at most
    /// `Unit::Day`, then the original datetime will be returned.
    ///
    /// This routine is equivalent to `self.until(other).map(|span| -span)`
    /// if no rounding options are set. If rounding options are set, then
    /// it's equivalent to
    /// `self.until(other_without_rounding_options).map(|span| -span)`,
    /// followed by a call to [`Span::round`] with the appropriate rounding
    /// options set. This is because the negation of a span can result in
    /// different rounding results depending on the rounding mode.
    ///
    /// # Errors
    ///
    /// An error can occur in some cases when the requested configuration
    /// would result in a span that is beyond allowable limits. For example,
    /// the nanosecond component of a span cannot represent the span of
    /// time between the minimum and maximum datetime supported by Jiff.
    /// Therefore, if one requests a span with its largest unit set to
    /// [`Unit::Nanosecond`], then it's possible for this routine to fail.
    ///
    /// An error can also occur if `DateTimeDifference` is misconfigured. For
    /// example, if the smallest unit provided is bigger than the largest unit.
    ///
    /// It is guaranteed that if one provides a datetime with the default
    /// [`DateTimeDifference`] configuration, then this routine will never
    /// fail.
    ///
    /// # Example
    ///
    /// ```
    /// # // See: https://github.com/rust-lang/rust/pull/121364
    /// # #![allow(unknown_lints, ambiguous_negative_literals)]
    /// use jiff::{civil::date, ToSpan};
    ///
    /// let earlier = date(2006, 8, 24).at(22, 30, 0, 0);
    /// let later = date(2019, 1, 31).at(21, 0, 0, 0);
    /// assert_eq!(later.since(earlier)?, 4542.days().hours(22).minutes(30));
    ///
    /// // Flipping the dates is fine, but you'll get a negative span.
    /// assert_eq!(earlier.since(later)?, -4542.days().hours(22).minutes(30));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: available via subtraction operator
    ///
    /// This routine can be used via the `-` operator. Since the default
    /// configuration is used and because a `Span` can represent the difference
    /// between any two possible datetimes, it will never panic.
    ///
    /// ```
    /// use jiff::{civil::date, ToSpan};
    ///
    /// let earlier = date(2006, 8, 24).at(22, 30, 0, 0);
    /// let later = date(2019, 1, 31).at(21, 0, 0, 0);
    /// assert_eq!(later - earlier, 4542.days().hours(22).minutes(30));
    /// ```
    ///
    /// # Example: using bigger units
    ///
    /// This example shows how to expand the span returned to bigger units.
    /// This makes use of a `From<(Unit, DateTime)> for DateTimeDifference`
    /// trait implementation.
    ///
    /// ```
    /// use jiff::{civil::date, Unit, ToSpan};
    ///
    /// let dt1 = date(1995, 12, 07).at(3, 24, 30, 3500);
    /// let dt2 = date(2019, 01, 31).at(15, 30, 0, 0);
    ///
    /// // The default limits durations to using "days" as the biggest unit.
    /// let span = dt2.since(dt1)?;
    /// assert_eq!(span.to_string(), "P8456dT12h5m29.9999965s");
    ///
    /// // But we can ask for units all the way up to years.
    /// let span = dt2.since((Unit::Year, dt1))?;
    /// assert_eq!(span.to_string(), "P23y1m24dT12h5m29.9999965s");
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: rounding the result
    ///
    /// This shows how one might find the difference between two datetimes and
    /// have the result rounded such that sub-seconds are removed.
    ///
    /// In this case, we need to hand-construct a [`DateTimeDifference`]
    /// in order to gain full configurability.
    ///
    /// ```
    /// use jiff::{civil::{DateTimeDifference, date}, Unit, ToSpan};
    ///
    /// let dt1 = date(1995, 12, 07).at(3, 24, 30, 3500);
    /// let dt2 = date(2019, 01, 31).at(15, 30, 0, 0);
    ///
    /// let span = dt2.since(
    ///     DateTimeDifference::from(dt1).smallest(Unit::Second),
    /// )?;
    /// assert_eq!(span, 8456.days().hours(12).minutes(5).seconds(29));
    ///
    /// // We can combine smallest and largest units too!
    /// let span = dt2.since(
    ///     DateTimeDifference::from(dt1)
    ///         .smallest(Unit::Second)
    ///         .largest(Unit::Year),
    /// )?;
    /// assert_eq!(span, 23.years().months(1).days(24).hours(12).minutes(5).seconds(29));
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: units biggers than days inhibit reversibility
    ///
    /// If you ask for units bigger than days, then adding the span
    /// returned to the `other` datetime is not guaranteed to result in the
    /// original datetime. For example:
    ///
    /// ```
    /// use jiff::{civil::date, Unit, ToSpan};
    ///
    /// let dt1 = date(2024, 3, 2).at(0, 0, 0, 0);
    /// let dt2 = date(2024, 5, 1).at(0, 0, 0, 0);
    ///
    /// let span = dt2.since((Unit::Month, dt1))?;
    /// assert_eq!(span, 1.month().days(30));
    /// let maybe_original = dt1.checked_add(span)?;
    /// // Not the same as the original datetime!
    /// assert_eq!(maybe_original, date(2024, 5, 2).at(0, 0, 0, 0));
    ///
    /// // But in the default configuration, days are always the biggest unit
    /// // and reversibility is guaranteed.
    /// let span = dt2.since(dt1)?;
    /// assert_eq!(span, 60.days());
    /// let is_original = dt1.checked_add(span)?;
    /// assert_eq!(is_original, dt2);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// This occurs because spans are added as if by adding the biggest units
    /// first, and then the smaller units. Because months vary in length,
    /// their meaning can change depending on how the span is added. In this
    /// case, adding one month to `2024-03-02` corresponds to 31 days, but
    /// subtracting one month from `2024-05-01` corresponds to 30 days.
    #[inline]
    pub fn since<A: Into<DateTimeDifference>>(
        self,
        other: A,
    ) -> Result<Span, Error> {
        let args: DateTimeDifference = other.into();
        let span = -args.until_with_largest_unit(self)?;
        if args.rounding_may_change_span() {
            span.round(args.round.relative(self))
        } else {
            Ok(span)
        }
    }

    /// Returns a span representing the elapsed time from this datetime until
    /// the given `other` datetime.
    ///
    /// When `other` occurs before this datetime, then the span returned will
    /// be negative.
    ///
    /// Depending on the input provided, the span returned is rounded. It may
    /// also be balanced up to bigger units than the default. By default, the
    /// span returned is balanced such that the biggest possible unit is days.
    ///
    /// This operation is configured by providing a [`DateTimeDifference`]
    /// value. Since this routine accepts anything that implements
    /// `Into<DateTimeDifference>`, once can pass a `DateTime` directly.
    /// One can also pass a `(Unit, DateTime)`, where `Unit` is treated as
    /// [`DateTimeDifference::largest`].
    ///
    /// # Properties
    ///
    /// It is guaranteed that if the returned span is subtracted from `other`,
    /// and if no rounding is requested, and if the largest unit requested is
    /// at most `Unit::Day`, then the original datetime will be returned.
    ///
    /// This routine is equivalent to `self.since(other).map(|span| -span)`
    /// if no rounding options are set. If rounding options are set, then
    /// it's equivalent to
    /// `self.since(other_without_rounding_options).map(|span| -span)`,
    /// followed by a call to [`Span::round`] with the appropriate rounding
    /// options set. This is because the negation of a span can result in
    /// different rounding results depending on the rounding mode.
    ///
    /// # Errors
    ///
    /// An error can occur in some cases when the requested configuration would
    /// result in a span that is beyond allowable limits. For example, the
    /// nanosecond component of a span cannot the span of time between the
    /// minimum and maximum datetime supported by Jiff. Therefore, if one
    /// requests a span with its largest unit set to [`Unit::Nanosecond`], then
    /// it's possible for this routine to fail.
    ///
    /// It is guaranteed that if one provides a datetime with the default
    /// [`DateTimeDifference`] configuration, then this routine will never
    /// fail.
    ///
    /// # Example
    ///
    /// ```
    /// # // See: https://github.com/rust-lang/rust/pull/121364
    /// # #![allow(unknown_lints, ambiguous_negative_literals)]
    /// use jiff::{civil::date, ToSpan};
    ///
    /// let earlier = date(2006, 8, 24).at(22, 30, 0, 0);
    /// let later = date(2019, 1, 31).at(21, 0, 0, 0);
    /// assert_eq!(earlier.until(later)?, 4542.days().hours(22).minutes(30));
    ///
    /// // Flipping the dates is fine, but you'll get a negative span.
    /// assert_eq!(later.until(earlier)?, -4542.days().hours(22).minutes(30));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: using bigger units
    ///
    /// This example shows how to expand the span returned to bigger units.
    /// This makes use of a `From<(Unit, DateTime)> for DateTimeDifference`
    /// trait implementation.
    ///
    /// ```
    /// use jiff::{civil::date, Unit, ToSpan};
    ///
    /// let dt1 = date(1995, 12, 07).at(3, 24, 30, 3500);
    /// let dt2 = date(2019, 01, 31).at(15, 30, 0, 0);
    ///
    /// // The default limits durations to using "days" as the biggest unit.
    /// let span = dt1.until(dt2)?;
    /// assert_eq!(span.to_string(), "P8456dT12h5m29.9999965s");
    ///
    /// // But we can ask for units all the way up to years.
    /// let span = dt1.until((Unit::Year, dt2))?;
    /// assert_eq!(span.to_string(), "P23y1m24dT12h5m29.9999965s");
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: rounding the result
    ///
    /// This shows how one might find the difference between two datetimes and
    /// have the result rounded such that sub-seconds are removed.
    ///
    /// In this case, we need to hand-construct a [`DateTimeDifference`]
    /// in order to gain full configurability.
    ///
    /// ```
    /// use jiff::{civil::{DateTimeDifference, date}, Unit, ToSpan};
    ///
    /// let dt1 = date(1995, 12, 07).at(3, 24, 30, 3500);
    /// let dt2 = date(2019, 01, 31).at(15, 30, 0, 0);
    ///
    /// let span = dt1.until(
    ///     DateTimeDifference::from(dt2).smallest(Unit::Second),
    /// )?;
    /// assert_eq!(span, 8456.days().hours(12).minutes(5).seconds(29));
    ///
    /// // We can combine smallest and largest units too!
    /// let span = dt1.until(
    ///     DateTimeDifference::from(dt2)
    ///         .smallest(Unit::Second)
    ///         .largest(Unit::Year),
    /// )?;
    /// assert_eq!(span, 23.years().months(1).days(24).hours(12).minutes(5).seconds(29));
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: units biggers than days inhibit reversibility
    ///
    /// If you ask for units bigger than days, then subtracting the span
    /// returned from the `other` datetime is not guaranteed to result in the
    /// original datetime. For example:
    ///
    /// ```
    /// use jiff::{civil::date, Unit, ToSpan};
    ///
    /// let dt1 = date(2024, 3, 2).at(0, 0, 0, 0);
    /// let dt2 = date(2024, 5, 1).at(0, 0, 0, 0);
    ///
    /// let span = dt1.until((Unit::Month, dt2))?;
    /// assert_eq!(span, 1.month().days(29));
    /// let maybe_original = dt2.checked_sub(span)?;
    /// // Not the same as the original datetime!
    /// assert_eq!(maybe_original, date(2024, 3, 3).at(0, 0, 0, 0));
    ///
    /// // But in the default configuration, days are always the biggest unit
    /// // and reversibility is guaranteed.
    /// let span = dt1.until(dt2)?;
    /// assert_eq!(span, 60.days());
    /// let is_original = dt2.checked_sub(span)?;
    /// assert_eq!(is_original, dt1);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// This occurs because span are added as if by adding the biggest units
    /// first, and then the smaller units. Because months vary in length,
    /// their meaning can change depending on how the span is added. In this
    /// case, adding one month to `2024-03-02` corresponds to 31 days, but
    /// subtracting one month from `2024-05-01` corresponds to 30 days.
    #[inline]
    pub fn until<A: Into<DateTimeDifference>>(
        self,
        other: A,
    ) -> Result<Span, Error> {
        let args: DateTimeDifference = other.into();
        let span = args.until_with_largest_unit(self)?;
        if args.rounding_may_change_span() {
            span.round(args.round.relative(self))
        } else {
            Ok(span)
        }
    }

    /// Rounds this datetime according to the [`DateTimeRound`] configuration
    /// given.
    ///
    /// The principal option is [`DateTimeRound::smallest`], which allows one
    /// to configure the smallest units in the returned datetime. Rounding
    /// is what determines whether that unit should keep its current value
    /// or whether it should be incremented. Moreover, the amount it should
    /// be incremented can be configured via [`DateTimeRound::increment`].
    /// Finally, the rounding strategy itself can be configured via
    /// [`DateTimeRound::mode`].
    ///
    /// Note that this routine is generic and accepts anything that
    /// implements `Into<DateTimeRound>`. Some notable implementations are:
    ///
    /// * `From<Unit> for DateTimeRound`, which will automatically create a
    /// `DateTimeRound::new().smallest(unit)` from the unit provided.
    /// * `From<(Unit, i64)> for DateTimeRound`, which will automatically
    /// create a `DateTimeRound::new().smallest(unit).increment(number)` from
    /// the unit and increment provided.
    ///
    /// # Errors
    ///
    /// This returns an error if the smallest unit configured on the given
    /// [`DateTimeRound`] is bigger than days. An error is also returned if
    /// the rounding increment is greater than 1 when the units are days.
    /// (Currently, rounding to the nearest week, month or year is not
    /// supported.)
    ///
    /// When the smallest unit is less than days, the rounding increment must
    /// divide evenly into the next highest unit after the smallest unit
    /// configured (and must not be equivalent to it). For example, if the
    /// smallest unit is [`Unit::Nanosecond`], then *some* of the valid values
    /// for the rounding increment are `1`, `2`, `4`, `5`, `100` and `500`.
    /// Namely, any integer that divides evenly into `1,000` nanoseconds since
    /// there are `1,000` nanoseconds in the next highest unit (microseconds).
    ///
    /// This can also return an error in some cases where rounding would
    /// require arithmetic that exceeds the maximum datetime value.
    ///
    /// # Example
    ///
    /// This is a basic example that demonstrates rounding a datetime to the
    /// nearest day. This also demonstrates calling this method with the
    /// smallest unit directly, instead of constructing a `DateTimeRound`
    /// manually.
    ///
    /// ```
    /// use jiff::{civil::date, Unit};
    ///
    /// let dt = date(2024, 6, 19).at(15, 0, 0, 0);
    /// assert_eq!(dt.round(Unit::Day)?, date(2024, 6, 20).at(0, 0, 0, 0));
    /// let dt = date(2024, 6, 19).at(10, 0, 0, 0);
    /// assert_eq!(dt.round(Unit::Day)?, date(2024, 6, 19).at(0, 0, 0, 0));
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
    /// use jiff::{civil::{DateTimeRound, date}, RoundMode, Unit};
    ///
    /// let dt = date(2024, 6, 19).at(15, 0, 0, 0);
    /// assert_eq!(dt.round(Unit::Day)?, date(2024, 6, 20).at(0, 0, 0, 0));
    /// // The default will round up to the next day for any time past noon,
    /// // but using truncation rounding will always round down.
    /// assert_eq!(
    ///     dt.round(
    ///         DateTimeRound::new().smallest(Unit::Day).mode(RoundMode::Trunc),
    ///     )?,
    ///     date(2024, 6, 19).at(0, 0, 0, 0),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: rounding to the nearest 5 minute increment
    ///
    /// ```
    /// use jiff::{civil::date, Unit};
    ///
    /// // rounds down
    /// let dt = date(2024, 6, 19).at(15, 27, 29, 999_999_999);
    /// assert_eq!(
    ///     dt.round((Unit::Minute, 5))?,
    ///     date(2024, 6, 19).at(15, 25, 0, 0),
    /// );
    /// // rounds up
    /// let dt = date(2024, 6, 19).at(15, 27, 30, 0);
    /// assert_eq!(
    ///     dt.round((Unit::Minute, 5))?,
    ///     date(2024, 6, 19).at(15, 30, 0, 0),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: overflow error
    ///
    /// This example demonstrates that it's possible for this operation to
    /// result in an error from datetime arithmetic overflow.
    ///
    /// ```
    /// use jiff::{civil::DateTime, Unit};
    ///
    /// let dt = DateTime::MAX;
    /// assert!(dt.round(Unit::Day).is_err());
    /// ```
    ///
    /// This occurs because rounding to the nearest day for the maximum
    /// datetime would result in rounding up to the next day. But the next day
    /// is greater than the maximum, and so this returns an error.
    ///
    /// If one were to use a rounding mode like [`RoundMode::Trunc`] (which
    /// will never round up), always set a correct increment and always used
    /// units less than or equal to days, then this routine is guaranteed to
    /// never fail:
    ///
    /// ```
    /// use jiff::{civil::{DateTime, DateTimeRound, date}, RoundMode, Unit};
    ///
    /// let round = DateTimeRound::new()
    ///     .smallest(Unit::Day)
    ///     .mode(RoundMode::Trunc);
    /// assert_eq!(
    ///     DateTime::MAX.round(round)?,
    ///     date(9999, 12, 31).at(0, 0, 0, 0),
    /// );
    /// assert_eq!(
    ///     DateTime::MIN.round(round)?,
    ///     date(-9999, 1, 1).at(0, 0, 0, 0),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn round(
        self,
        options: impl Into<DateTimeRound>,
    ) -> Result<DateTime, Error> {
        let options: DateTimeRound = options.into();
        options.round(t::NANOS_PER_CIVIL_DAY, self)
    }

    /// Return an iterator of periodic datetimes determined by the given span.
    ///
    /// The given span may be negative, in which case, the iterator will move
    /// backwards through time. The iterator won't stop until either the span
    /// itself overflows, or it would otherwise exceed the minimum or maximum
    /// `DateTime` value.
    ///
    /// # Example: when to check a glucose monitor
    ///
    /// When my cat had diabetes, my veterinarian installed a glucose monitor
    /// and instructed me to scan it about every 5 hours. This example lists
    /// all of the times I need to scan it for the 2 days following its
    /// installation:
    ///
    /// ```
    /// use jiff::{civil::datetime, ToSpan};
    ///
    /// let start = datetime(2023, 7, 15, 16, 30, 0, 0);
    /// let end = start.checked_add(2.days())?;
    /// let mut scan_times = vec![];
    /// for dt in start.series(5.hours()).take_while(|&dt| dt <= end) {
    ///     scan_times.push(dt);
    /// }
    /// assert_eq!(scan_times, vec![
    ///     datetime(2023, 7, 15, 16, 30, 0, 0),
    ///     datetime(2023, 7, 15, 21, 30, 0, 0),
    ///     datetime(2023, 7, 16, 2, 30, 0, 0),
    ///     datetime(2023, 7, 16, 7, 30, 0, 0),
    ///     datetime(2023, 7, 16, 12, 30, 0, 0),
    ///     datetime(2023, 7, 16, 17, 30, 0, 0),
    ///     datetime(2023, 7, 16, 22, 30, 0, 0),
    ///     datetime(2023, 7, 17, 3, 30, 0, 0),
    ///     datetime(2023, 7, 17, 8, 30, 0, 0),
    ///     datetime(2023, 7, 17, 13, 30, 0, 0),
    /// ]);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn series(self, period: Span) -> DateTimeSeries {
        DateTimeSeries { start: self, period, step: 0 }
    }

    /// Converts this datetime to a nanosecond timestamp assuming a Zulu time
    /// zone offset and where all days are exactly 24 hours long.
    #[inline]
    fn to_nanosecond(self) -> t::NoUnits128 {
        let day_nano = self.date().to_unix_epoch_days();
        let time_nano = self.time().to_nanosecond();
        (t::NoUnits128::rfrom(day_nano) * t::NANOS_PER_CIVIL_DAY) + time_nano
    }
}

/// Parsing and formatting using a "printf" style of API.
impl DateTime {
    /// Parses a civil datetime in `input` matching the given `format`.
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
    /// construct a civil datetime. For example, if an offset wasn't parsed.
    ///
    /// # Example
    ///
    /// This example shows how to parse a civil datetime:
    ///
    /// ```
    /// use jiff::civil::DateTime;
    ///
    /// let dt = DateTime::strptime("%F %H:%M", "2024-07-14 21:14")?;
    /// assert_eq!(dt.to_string(), "2024-07-14T21:14:00");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn strptime(
        format: impl AsRef<[u8]>,
        input: impl AsRef<[u8]>,
    ) -> Result<DateTime, Error> {
        fmt::strtime::parse(format, input).and_then(|tm| tm.to_datetime())
    }

    /// Formats this civil datetime according to the given `format`.
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
    /// This example shows how to format a civil datetime:
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt = date(2024, 7, 15).at(16, 24, 59, 0);
    /// let string = dt.strftime("%A, %B %e, %Y at %H:%M:%S").to_string();
    /// assert_eq!(string, "Monday, July 15, 2024 at 16:24:59");
    /// ```
    #[inline]
    pub fn strftime<'f, F: 'f + ?Sized + AsRef<[u8]>>(
        &self,
        format: &'f F,
    ) -> fmt::strtime::Display<'f> {
        fmt::strtime::Display { fmt: format.as_ref(), tm: (*self).into() }
    }
}

impl Default for DateTime {
    #[inline]
    fn default() -> DateTime {
        DateTime::ZERO
    }
}

impl core::fmt::Debug for DateTime {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        core::fmt::Display::fmt(self, f)
    }
}

impl core::fmt::Display for DateTime {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        use crate::fmt::StdFmtWrite;

        DEFAULT_DATETIME_PRINTER
            .print_datetime(self, StdFmtWrite(f))
            .map_err(|_| core::fmt::Error)
    }
}

impl core::str::FromStr for DateTime {
    type Err = Error;

    #[inline]
    fn from_str(string: &str) -> Result<DateTime, Error> {
        DEFAULT_DATETIME_PARSER.parse_datetime(string)
    }
}

/// Converts a [`Date`] to a [`DateTime`] with the time set to midnight.
impl From<Date> for DateTime {
    #[inline]
    fn from(date: Date) -> DateTime {
        date.to_datetime(Time::midnight())
    }
}

/// Converts a [`Zoned`] to a [`DateTime`].
impl From<Zoned> for DateTime {
    #[inline]
    fn from(zdt: Zoned) -> DateTime {
        zdt.datetime()
    }
}

/// Converts a [`&Zoned`](Zoned) to a [`DateTime`].
impl<'a> From<&'a Zoned> for DateTime {
    #[inline]
    fn from(zdt: &'a Zoned) -> DateTime {
        zdt.datetime()
    }
}

/// Adds a span of time to a datetime.
///
/// This uses checked arithmetic and panics on overflow. To handle overflow
/// without panics, use [`DateTime::checked_add`].
impl core::ops::Add<Span> for DateTime {
    type Output = DateTime;

    #[inline]
    fn add(self, rhs: Span) -> DateTime {
        self.checked_add(rhs).expect("adding span to datetime overflowed")
    }
}

/// Adds a span of time to a datetime in place.
///
/// This uses checked arithmetic and panics on overflow. To handle overflow
/// without panics, use [`DateTime::checked_add`].
impl core::ops::AddAssign<Span> for DateTime {
    #[inline]
    fn add_assign(&mut self, rhs: Span) {
        *self = *self + rhs
    }
}

/// Subtracts a span of time from a datetime.
///
/// This uses checked arithmetic and panics on overflow. To handle overflow
/// without panics, use [`DateTime::checked_sub`].
impl core::ops::Sub<Span> for DateTime {
    type Output = DateTime;

    #[inline]
    fn sub(self, rhs: Span) -> DateTime {
        self.checked_sub(rhs)
            .expect("subtracting span from datetime overflowed")
    }
}

/// Subtracts a span of time from a datetime in place.
///
/// This uses checked arithmetic and panics on overflow. To handle overflow
/// without panics, use [`DateTime::checked_sub`].
impl core::ops::SubAssign<Span> for DateTime {
    #[inline]
    fn sub_assign(&mut self, rhs: Span) {
        *self = *self - rhs
    }
}

/// Computes the span of time between two datetimes.
///
/// This will return a negative span when the datetime being subtracted is
/// greater.
///
/// Since this uses the default configuration for calculating a span between
/// two datetimes (no rounding and largest units is days), this will never
/// panic or fail in any way.
///
/// To configure the largest unit or enable rounding, use [`DateTime::since`].
impl core::ops::Sub for DateTime {
    type Output = Span;

    #[inline]
    fn sub(self, rhs: DateTime) -> Span {
        self.since(rhs).expect("since never fails when given DateTime")
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for DateTime {
    #[inline]
    fn serialize<S: serde::Serializer>(
        &self,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        serializer.collect_str(self)
    }
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for DateTime {
    #[inline]
    fn deserialize<D: serde::Deserializer<'de>>(
        deserializer: D,
    ) -> Result<DateTime, D::Error> {
        use serde::de;

        struct DateTimeVisitor;

        impl<'de> de::Visitor<'de> for DateTimeVisitor {
            type Value = DateTime;

            fn expecting(
                &self,
                f: &mut core::fmt::Formatter,
            ) -> core::fmt::Result {
                f.write_str("a datetime string")
            }

            #[inline]
            fn visit_bytes<E: de::Error>(
                self,
                value: &[u8],
            ) -> Result<DateTime, E> {
                DEFAULT_DATETIME_PARSER
                    .parse_datetime(value)
                    .map_err(de::Error::custom)
            }

            #[inline]
            fn visit_str<E: de::Error>(
                self,
                value: &str,
            ) -> Result<DateTime, E> {
                self.visit_bytes(value.as_bytes())
            }
        }

        deserializer.deserialize_bytes(DateTimeVisitor)
    }
}

#[cfg(test)]
impl quickcheck::Arbitrary for DateTime {
    fn arbitrary(g: &mut quickcheck::Gen) -> DateTime {
        let date = Date::arbitrary(g);
        let time = Time::arbitrary(g);
        DateTime::from_parts(date, time)
    }

    fn shrink(&self) -> alloc::boxed::Box<dyn Iterator<Item = DateTime>> {
        alloc::boxed::Box::new(
            (self.date(), self.time())
                .shrink()
                .map(|(date, time)| DateTime::from_parts(date, time)),
        )
    }
}

/// An iterator over periodic datetimes, created by [`DateTime::series`].
///
/// It is exhausted when the next value would exceed a [`Span`] or [`DateTime`]
/// value.
#[derive(Clone, Debug)]
pub struct DateTimeSeries {
    start: DateTime,
    period: Span,
    step: i64,
}

impl Iterator for DateTimeSeries {
    type Item = DateTime;

    #[inline]
    fn next(&mut self) -> Option<DateTime> {
        let span = self.period.checked_mul(self.step).ok()?;
        self.step = self.step.checked_add(1)?;
        let date = self.start.checked_add(span).ok()?;
        Some(date)
    }
}

/// Options for [`DateTime::since`] and [`DateTime::until`].
///
/// This type provides a way to configure the calculation of
/// spans between two [`DateTime`] values. In particular, both
/// `DateTime::since` and `DateTime::until` accept anything that implements
/// `Into<DateTimeDifference>`. There are a few key trait implementations that
/// make this convenient:
///
/// * `From<DateTime> for DateTimeDifference` will construct a configuration
/// consisting of just the datetime. So for example, `dt1.since(dt2)` returns
/// the span from `dt2` to `dt1`.
/// * `From<Date> for DateTimeDifference` will construct a configuration
/// consisting of just the datetime built from the date given at midnight on
/// that day.
/// * `From<(Unit, DateTime)>` is a convenient way to specify the largest units
/// that should be present on the span returned. By default, the largest units
/// are days. Using this trait implementation is equivalent to
/// `DateTimeDifference::new(datetime).largest(unit)`.
/// * `From<(Unit, Date)>` is like the one above, but with the time component
/// fixed to midnight.
///
/// One can also provide a `DateTimeDifference` value directly. Doing so
/// is necessary to use the rounding features of calculating a span. For
/// example, setting the smallest unit (defaults to [`Unit::Nanosecond`]), the
/// rounding mode (defaults to [`RoundMode::Trunc`]) and the rounding increment
/// (defaults to `1`). The defaults are selected such that no rounding occurs.
///
/// Rounding a span as part of calculating it is provided as a convenience.
/// Callers may choose to round the span as a distinct step via
/// [`Span::round`], but callers may need to provide a reference date
/// for rounding larger units. By coupling rounding with routines like
/// [`DateTime::since`], the reference date can be set automatically based on
/// the input to `DateTime::since`.
///
/// # Example
///
/// This example shows how to round a span between two datetimes to the nearest
/// half-hour, with ties breaking away from zero.
///
/// ```
/// use jiff::{civil::{DateTime, DateTimeDifference}, RoundMode, ToSpan, Unit};
///
/// let dt1 = "2024-03-15 08:14:00.123456789".parse::<DateTime>()?;
/// let dt2 = "2030-03-22 15:00".parse::<DateTime>()?;
/// let span = dt1.until(
///     DateTimeDifference::new(dt2)
///         .smallest(Unit::Minute)
///         .largest(Unit::Year)
///         .mode(RoundMode::HalfExpand)
///         .increment(30),
/// )?;
/// assert_eq!(span, 6.years().days(7).hours(7));
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Clone, Copy, Debug)]
pub struct DateTimeDifference {
    datetime: DateTime,
    round: SpanRound<'static>,
}

impl DateTimeDifference {
    /// Create a new default configuration for computing the span between the
    /// given datetime and some other datetime (specified as the receiver in
    /// [`DateTime::since`] or [`DateTime::until`]).
    #[inline]
    pub fn new(datetime: DateTime) -> DateTimeDifference {
        // We use truncation rounding by default since it seems that's
        // what is generally expected when computing the difference between
        // datetimes.
        //
        // See: https://github.com/tc39/proposal-temporal/issues/1122
        let round = SpanRound::new().mode(RoundMode::Trunc);
        DateTimeDifference { datetime, round }
    }

    /// Set the smallest units allowed in the span returned.
    ///
    /// When a largest unit is not specified and the smallest unit is days
    /// or greater, then the largest unit is automatically set to be equal to
    /// the smallest unit.
    ///
    /// # Errors
    ///
    /// The smallest units must be no greater than the largest units. If this
    /// is violated, then computing a span with this configuration will result
    /// in an error.
    ///
    /// # Example
    ///
    /// This shows how to round a span between two datetimes to the nearest
    /// number of weeks.
    ///
    /// ```
    /// use jiff::{
    ///     civil::{DateTime, DateTimeDifference},
    ///     RoundMode, ToSpan, Unit,
    /// };
    ///
    /// let dt1 = "2024-03-15 08:14".parse::<DateTime>()?;
    /// let dt2 = "2030-11-22 08:30".parse::<DateTime>()?;
    /// let span = dt1.until(
    ///     DateTimeDifference::new(dt2)
    ///         .smallest(Unit::Week)
    ///         .largest(Unit::Week)
    ///         .mode(RoundMode::HalfExpand),
    /// )?;
    /// assert_eq!(span, 349.weeks());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn smallest(self, unit: Unit) -> DateTimeDifference {
        DateTimeDifference { round: self.round.smallest(unit), ..self }
    }

    /// Set the largest units allowed in the span returned.
    ///
    /// When a largest unit is not specified and the smallest unit is days
    /// or greater, then the largest unit is automatically set to be equal to
    /// the smallest unit. Otherwise, when the largest unit is not specified,
    /// it is set to days.
    ///
    /// Once a largest unit is set, there is no way to change this rounding
    /// configuration back to using the "automatic" default. Instead, callers
    /// must create a new configuration.
    ///
    /// # Errors
    ///
    /// The largest units, when set, must be at least as big as the smallest
    /// units (which defaults to [`Unit::Nanosecond`]). If this is violated,
    /// then computing a span with this configuration will result in an error.
    ///
    /// # Example
    ///
    /// This shows how to round a span between two datetimes to units no
    /// bigger than seconds.
    ///
    /// ```
    /// use jiff::{civil::{DateTime, DateTimeDifference}, ToSpan, Unit};
    ///
    /// let dt1 = "2024-03-15 08:14".parse::<DateTime>()?;
    /// let dt2 = "2030-11-22 08:30".parse::<DateTime>()?;
    /// let span = dt1.until(
    ///     DateTimeDifference::new(dt2).largest(Unit::Second),
    /// )?;
    /// assert_eq!(span, 211076160.seconds());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn largest(self, unit: Unit) -> DateTimeDifference {
        DateTimeDifference { round: self.round.largest(unit), ..self }
    }

    /// Set the rounding mode.
    ///
    /// This defaults to [`RoundMode::Trunc`] since it's plausible that
    /// rounding "up" in the context of computing the span between
    /// two datetimes could be surprising in a number of cases. The
    /// [`RoundMode::HalfExpand`] mode corresponds to typical rounding you
    /// might have learned about in school. But a variety of other rounding
    /// modes exist.
    ///
    /// # Example
    ///
    /// This shows how to always round "up" towards positive infinity.
    ///
    /// ```
    /// use jiff::{
    ///     civil::{DateTime, DateTimeDifference},
    ///     RoundMode, ToSpan, Unit,
    /// };
    ///
    /// let dt1 = "2024-03-15 08:10".parse::<DateTime>()?;
    /// let dt2 = "2024-03-15 08:11".parse::<DateTime>()?;
    /// let span = dt1.until(
    ///     DateTimeDifference::new(dt2)
    ///         .smallest(Unit::Hour)
    ///         .mode(RoundMode::Ceil),
    /// )?;
    /// // Only one minute elapsed, but we asked to always round up!
    /// assert_eq!(span, 1.hour());
    ///
    /// // Since `Ceil` always rounds toward positive infinity, the behavior
    /// // flips for a negative span.
    /// let span = dt1.since(
    ///     DateTimeDifference::new(dt2)
    ///         .smallest(Unit::Hour)
    ///         .mode(RoundMode::Ceil),
    /// )?;
    /// assert_eq!(span, 0.hour());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn mode(self, mode: RoundMode) -> DateTimeDifference {
        DateTimeDifference { round: self.round.mode(mode), ..self }
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
    /// When the smallest unit is less than days, the rounding increment must
    /// divide evenly into the next highest unit after the smallest unit
    /// configured (and must not be equivalent to it). For example, if the
    /// smallest unit is [`Unit::Nanosecond`], then *some* of the valid values
    /// for the rounding increment are `1`, `2`, `4`, `5`, `100` and `500`.
    /// Namely, any integer that divides evenly into `1,000` nanoseconds since
    /// there are `1,000` nanoseconds in the next highest unit (microseconds).
    ///
    /// The error will occur when computing the span, and not when setting
    /// the increment here.
    ///
    /// # Example
    ///
    /// This shows how to round the span between two datetimes to the nearest
    /// 5 minute increment.
    ///
    /// ```
    /// use jiff::{
    ///     civil::{DateTime, DateTimeDifference},
    ///     RoundMode, ToSpan, Unit,
    /// };
    ///
    /// let dt1 = "2024-03-15 08:19".parse::<DateTime>()?;
    /// let dt2 = "2024-03-15 12:52".parse::<DateTime>()?;
    /// let span = dt1.until(
    ///     DateTimeDifference::new(dt2)
    ///         .smallest(Unit::Minute)
    ///         .increment(5)
    ///         .mode(RoundMode::HalfExpand),
    /// )?;
    /// assert_eq!(span, 4.hour().minutes(35));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn increment(self, increment: i64) -> DateTimeDifference {
        DateTimeDifference { round: self.round.increment(increment), ..self }
    }

    /// Returns true if and only if this configuration could change the span
    /// via rounding.
    #[inline]
    fn rounding_may_change_span(&self) -> bool {
        self.round.rounding_may_change_span_ignore_largest()
    }

    /// Returns the span of time from `dt1` to the datetime in this
    /// configuration. The biggest units allowed are determined by the
    /// `smallest` and `largest` settings, but defaults to `Unit::Day`.
    #[inline]
    fn until_with_largest_unit(&self, dt1: DateTime) -> Result<Span, Error> {
        let dt2 = self.datetime;
        let largest = self
            .round
            .get_largest()
            .unwrap_or_else(|| self.round.get_smallest().max(Unit::Day));
        if largest <= Unit::Day {
            let diff = dt2.to_nanosecond() - dt1.to_nanosecond();
            // Note that this can fail! If largest unit is nanoseconds and the
            // datetimes are far enough apart, a single i64 won't be able to
            // represent the time difference.
            //
            // This is only true for nanoseconds. A single i64 in units of
            // microseconds can represent the interval between all valid
            // datetimes. (At time of writing.)
            return Span::from_invariant_nanoseconds(largest, diff);
        }

        let (d1, mut d2) = (dt1.date(), dt2.date());
        let (t1, t2) = (dt1.time(), dt2.time());
        let sign = t::sign(d2, d1);
        let mut time_diff = t1.until_nanoseconds(t2);
        if time_diff.signum() == -sign {
            // These unwraps will always succeed, but the argument for why is
            // subtle. The key here is that the only way, e.g., d2.tomorrow()
            // can fail is when d2 is the max date. But, if d2 is the max date,
            // then it's impossible for `sign < 0` since the max date is at
            // least as big as every other date. And thus, d2.tomorrow() is
            // never reached in cases where it would fail.
            if sign > 0 {
                d2 = d2.yesterday().unwrap();
            } else if sign < 0 {
                d2 = d2.tomorrow().unwrap();
            }
            time_diff +=
                t::SpanNanoseconds::rfrom(t::NANOS_PER_CIVIL_DAY) * sign;
        }
        let date_span = d1.until((largest, d2))?;
        Ok(Span::from_invariant_nanoseconds(largest, time_diff)
            // Unlike in the <=Unit::Day case, this always succeeds because
            // every unit except for nanoseconds (which is not used here) can
            // represent all possible spans of time between any two civil
            // datetimes.
            .expect("difference between time always fits in span")
            .years_ranged(date_span.get_years_ranged())
            .months_ranged(date_span.get_months_ranged())
            .weeks_ranged(date_span.get_weeks_ranged())
            .days_ranged(date_span.get_days_ranged()))
    }
}

impl From<DateTime> for DateTimeDifference {
    #[inline]
    fn from(dt: DateTime) -> DateTimeDifference {
        DateTimeDifference::new(dt)
    }
}

impl From<Date> for DateTimeDifference {
    #[inline]
    fn from(date: Date) -> DateTimeDifference {
        DateTimeDifference::from(DateTime::from(date))
    }
}

impl From<Zoned> for DateTimeDifference {
    #[inline]
    fn from(zdt: Zoned) -> DateTimeDifference {
        DateTimeDifference::from(DateTime::from(zdt))
    }
}

impl<'a> From<&'a Zoned> for DateTimeDifference {
    #[inline]
    fn from(zdt: &'a Zoned) -> DateTimeDifference {
        DateTimeDifference::from(zdt.datetime())
    }
}

impl From<(Unit, DateTime)> for DateTimeDifference {
    #[inline]
    fn from((largest, dt): (Unit, DateTime)) -> DateTimeDifference {
        DateTimeDifference::from(dt).largest(largest)
    }
}

impl From<(Unit, Date)> for DateTimeDifference {
    #[inline]
    fn from((largest, date): (Unit, Date)) -> DateTimeDifference {
        DateTimeDifference::from(date).largest(largest)
    }
}

impl From<(Unit, Zoned)> for DateTimeDifference {
    #[inline]
    fn from((largest, zdt): (Unit, Zoned)) -> DateTimeDifference {
        DateTimeDifference::from((largest, DateTime::from(zdt)))
    }
}

impl<'a> From<(Unit, &'a Zoned)> for DateTimeDifference {
    #[inline]
    fn from((largest, zdt): (Unit, &'a Zoned)) -> DateTimeDifference {
        DateTimeDifference::from((largest, zdt.datetime()))
    }
}

/// Options for [`DateTime::round`].
///
/// This type provides a way to configure the rounding of a civil datetime. In
/// particular, `DateTime::round` accepts anything that implements the
/// `Into<DateTimeRound>` trait. There are some trait implementations that
/// therefore make calling `DateTime::round` in some common cases more
/// ergonomic:
///
/// * `From<Unit> for DateTimeRound` will construct a rounding
/// configuration that rounds to the unit given. Specifically,
/// `DateTimeRound::new().smallest(unit)`.
/// * `From<(Unit, i64)> for DateTimeRound` is like the one above, but also
/// specifies the rounding increment for [`DateTimeRound::increment`].
///
/// Note that in the default configuration, no rounding occurs.
///
/// # Example
///
/// This example shows how to round a datetime to the nearest second:
///
/// ```
/// use jiff::{civil::{DateTime, date}, Unit};
///
/// let dt: DateTime = "2024-06-20 16:24:59.5".parse()?;
/// assert_eq!(
///     dt.round(Unit::Second)?,
///     // The second rounds up and causes minutes to increase.
///     date(2024, 6, 20).at(16, 25, 0, 0),
/// );
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// The above makes use of the fact that `Unit` implements
/// `Into<DateTimeRound>`. If you want to change the rounding mode to, say,
/// truncation, then you'll need to construct a `DateTimeRound` explicitly
/// since there are no convenience `Into` trait implementations for
/// [`RoundMode`].
///
/// ```
/// use jiff::{civil::{DateTime, DateTimeRound, date}, RoundMode, Unit};
///
/// let dt: DateTime = "2024-06-20 16:24:59.5".parse()?;
/// assert_eq!(
///     dt.round(
///         DateTimeRound::new().smallest(Unit::Second).mode(RoundMode::Trunc),
///     )?,
///     // The second just gets truncated as if it wasn't there.
///     date(2024, 6, 20).at(16, 24, 59, 0),
/// );
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Clone, Copy, Debug)]
pub struct DateTimeRound {
    smallest: Unit,
    mode: RoundMode,
    increment: i64,
}

impl DateTimeRound {
    /// Create a new default configuration for rounding a [`DateTime`].
    #[inline]
    pub fn new() -> DateTimeRound {
        DateTimeRound {
            smallest: Unit::Nanosecond,
            mode: RoundMode::HalfExpand,
            increment: 1,
        }
    }

    /// Set the smallest units allowed in the datetime returned after rounding.
    ///
    /// Any units below the smallest configured unit will be used, along with
    /// the rounding increment and rounding mode, to determine the value of the
    /// smallest unit. For example, when rounding `2024-06-20T03:25:30` to the
    /// nearest minute, the `30` second unit will result in rounding the minute
    /// unit of `25` up to `26` and zeroing out everything below minutes.
    ///
    /// This defaults to [`Unit::Nanosecond`].
    ///
    /// # Errors
    ///
    /// The smallest units must be no greater than [`Unit::Day`]. And when the
    /// smallest unit is `Unit::Day`, the rounding increment must be equal to
    /// `1`. Otherwise an error will be returned from [`DateTime::round`].
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::{civil::{DateTimeRound, date}, Unit};
    ///
    /// let dt = date(2024, 6, 20).at(3, 25, 30, 0);
    /// assert_eq!(
    ///     dt.round(DateTimeRound::new().smallest(Unit::Minute))?,
    ///     date(2024, 6, 20).at(3, 26, 0, 0),
    /// );
    /// // Or, utilize the `From<Unit> for DateTimeRound` impl:
    /// assert_eq!(
    ///     dt.round(Unit::Minute)?,
    ///     date(2024, 6, 20).at(3, 26, 0, 0),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn smallest(self, unit: Unit) -> DateTimeRound {
        DateTimeRound { smallest: unit, ..self }
    }

    /// Set the rounding mode.
    ///
    /// This defaults to [`RoundMode::HalfExpand`], which rounds away from
    /// zero. It matches the kind of rounding you might have been taught in
    /// school.
    ///
    /// # Example
    ///
    /// This shows how to always round datetimes up towards positive infinity.
    ///
    /// ```
    /// use jiff::{civil::{DateTime, DateTimeRound, date}, RoundMode, Unit};
    ///
    /// let dt: DateTime = "2024-06-20 03:25:01".parse()?;
    /// assert_eq!(
    ///     dt.round(
    ///         DateTimeRound::new()
    ///             .smallest(Unit::Minute)
    ///             .mode(RoundMode::Ceil),
    ///     )?,
    ///     date(2024, 6, 20).at(3, 26, 0, 0),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn mode(self, mode: RoundMode) -> DateTimeRound {
        DateTimeRound { mode, ..self }
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
    /// When the smallest unit is `Unit::Day`, then the rounding increment must
    /// be `1` or else [`DateTime::round`] will return an error.
    ///
    /// For other units, the rounding increment must divide evenly into the
    /// next highest unit above the smallest unit set. The rounding increment
    /// must also not be equal to the next highest unit. For example, if the
    /// smallest unit is [`Unit::Nanosecond`], then *some* of the valid values
    /// for the rounding increment are `1`, `2`, `4`, `5`, `100` and `500`.
    /// Namely, any integer that divides evenly into `1,000` nanoseconds since
    /// there are `1,000` nanoseconds in the next highest unit (microseconds).
    ///
    /// # Example
    ///
    /// This example shows how to round a datetime to the nearest 10 minute
    /// increment.
    ///
    /// ```
    /// use jiff::{civil::{DateTime, DateTimeRound, date}, RoundMode, Unit};
    ///
    /// let dt: DateTime = "2024-06-20 03:24:59".parse()?;
    /// assert_eq!(
    ///     dt.round((Unit::Minute, 10))?,
    ///     date(2024, 6, 20).at(3, 20, 0, 0),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn increment(self, increment: i64) -> DateTimeRound {
        DateTimeRound { increment, ..self }
    }

    /// Does the actual rounding.
    ///
    /// A non-public configuration here is the length of a day. For civil
    /// datetimes, this should always be `NANOS_PER_CIVIL_DAY`. But this
    /// rounding routine is also used for `Zoned` rounding, and in that
    /// context, the length of a day can vary based on the time zone.
    pub(crate) fn round(
        &self,
        day_length: impl RInto<t::ZonedDayNanoseconds>,
        dt: DateTime,
    ) -> Result<DateTime, Error> {
        // ref: https://tc39.es/proposal-temporal/#sec-temporal.plaindatetime.prototype.round

        let day_length = t::NoUnits128::rfrom(day_length.rinto());
        let increment =
            increment::for_datetime(self.smallest, self.increment)?;
        // We permit rounding to any time unit and days, but nothing else.
        // We should support this, but Temporal doesn't. So for now, we're
        // sticking to what Temporal does because they're probably not doing
        // it for good reasons.
        match self.smallest {
            Unit::Year | Unit::Month | Unit::Week => {
                return Err(err!(
                    "rounding datetimes does not support {unit}",
                    unit = self.smallest.plural()
                ));
            }
            // We don't do any rounding in this case, so just bail now.
            Unit::Nanosecond if increment == 1 => {
                return Ok(dt);
            }
            _ => {}
        }

        let time_nanos = dt.time().to_nanosecond();
        let sign = t::NoUnits128::rfrom(dt.date().year_ranged().signum());
        let time_rounded = self.mode.round_by_unit_in_nanoseconds(
            time_nanos,
            self.smallest,
            increment,
        );
        let days = sign * time_rounded.div_ceil(day_length);
        let time_nanos = time_rounded.rem_ceil(day_length);
        let time = Time::from_nanosecond(time_nanos);

        let date_days = t::SpanDays::rfrom(dt.date().day_ranged());
        // OK because days is limited by the fact that the length of a day
        // can't be any smaller than 1 second, and the number of nanoseconds in
        // a civil day is capped.
        let days_len = (date_days - C(1)) + days;
        // OK because the first day of any month is always valid.
        let start = dt.date().first_of_month();
        // `days` should basically always be <= 1, and so `days_len` should
        // always be at most 1 greater (or less) than where we started. But
        // what if there is a time zone transition that makes 9999-12-31
        // shorter than 24 hours? And we are rounding 9999-12-31? Well, then
        // I guess this could overflow and fail. I suppose it could also fail
        // for really weird time zone data that made the length of a day really
        // short. But even then, you'd need to be close to the boundary of
        // supported datetimes.
        let end = start
            .checked_add(Span::new().days_ranged(days_len))
            .with_context(|| {
                err!("adding {days_len} days to {start} failed")
            })?;
        Ok(DateTime::from_parts(end, time))
    }
}

impl Default for DateTimeRound {
    #[inline]
    fn default() -> DateTimeRound {
        DateTimeRound::new()
    }
}

impl From<Unit> for DateTimeRound {
    #[inline]
    fn from(unit: Unit) -> DateTimeRound {
        DateTimeRound::default().smallest(unit)
    }
}

impl From<(Unit, i64)> for DateTimeRound {
    #[inline]
    fn from((unit, increment): (Unit, i64)) -> DateTimeRound {
        DateTimeRound::from(unit).increment(increment)
    }
}

/// A builder for setting the fields on a [`DateTime`].
///
/// This builder is constructed via [`DateTime::with`].
///
/// # Example
///
/// The builder ensures one can chain together the individual components of a
/// datetime without it failing at an intermediate step. For example, if you
/// had a date of `2024-10-31T00:00:00` and wanted to change both the day and
/// the month, and each setting was validated independent of the other, you
/// would need to be careful to set the day first and then the month. In some
/// cases, you would need to set the month first and then the day!
///
/// But with the builder, you can set values in any order:
///
/// ```
/// use jiff::civil::date;
///
/// let dt1 = date(2024, 10, 31).at(0, 0, 0, 0);
/// let dt2 = dt1.with().month(11).day(30).build()?;
/// assert_eq!(dt2, date(2024, 11, 30).at(0, 0, 0, 0));
///
/// let dt1 = date(2024, 4, 30).at(0, 0, 0, 0);
/// let dt2 = dt1.with().day(31).month(7).build()?;
/// assert_eq!(dt2, date(2024, 7, 31).at(0, 0, 0, 0));
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Clone, Copy, Debug)]
pub struct DateTimeWith {
    date_with: DateWith,
    time_with: TimeWith,
}

impl DateTimeWith {
    #[inline]
    fn new(original: DateTime) -> DateTimeWith {
        DateTimeWith {
            date_with: original.date().with(),
            time_with: original.time().with(),
        }
    }

    /// Create a new `DateTime` from the fields set on this configuration.
    ///
    /// An error occurs when the fields combine to an invalid datetime.
    ///
    /// For any fields not set on this configuration, the values are taken from
    /// the [`DateTime`] that originally created this configuration. When no
    /// values are set, this routine is guaranteed to succeed and will always
    /// return the original datetime without modification.
    ///
    /// # Example
    ///
    /// This creates a datetime corresponding to the last day in the year at
    /// noon:
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt = date(2023, 1, 1).at(12, 0, 0, 0);
    /// assert_eq!(
    ///     dt.with().day_of_year_no_leap(365).build()?,
    ///     date(2023, 12, 31).at(12, 0, 0, 0),
    /// );
    ///
    /// // It also works with leap years for the same input:
    /// let dt = date(2024, 1, 1).at(12, 0, 0, 0);
    /// assert_eq!(
    ///     dt.with().day_of_year_no_leap(365).build()?,
    ///     date(2024, 12, 31).at(12, 0, 0, 0),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: error for invalid datetime
    ///
    /// If the fields combine to form an invalid date, then an error is
    /// returned:
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt = date(2024, 11, 30).at(15, 30, 0, 0);
    /// assert!(dt.with().day(31).build().is_err());
    ///
    /// let dt = date(2024, 2, 29).at(15, 30, 0, 0);
    /// assert!(dt.with().year(2023).build().is_err());
    /// ```
    #[inline]
    pub fn build(self) -> Result<DateTime, Error> {
        let date = self.date_with.build()?;
        let time = self.time_with.build()?;
        Ok(DateTime::from_parts(date, time))
    }

    /// Set the year, month and day fields via the `Date` given.
    ///
    /// This overrides any previous year, month or day settings.
    ///
    /// # Example
    ///
    /// This shows how to create a new datetime with a different date:
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt1 = date(2005, 11, 5).at(15, 30, 0, 0);
    /// let dt2 = dt1.with().date(date(2017, 10, 31)).build()?;
    /// // The date changes but the time remains the same.
    /// assert_eq!(dt2, date(2017, 10, 31).at(15, 30, 0, 0));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn date(self, date: Date) -> DateTimeWith {
        DateTimeWith { date_with: date.with(), ..self }
    }

    /// Set the hour, minute, second, millisecond, microsecond and nanosecond
    /// fields via the `Time` given.
    ///
    /// This overrides any previous hour, minute, second, millisecond,
    /// microsecond, nanosecond or subsecond nanosecond settings.
    ///
    /// # Example
    ///
    /// This shows how to create a new datetime with a different time:
    ///
    /// ```
    /// use jiff::civil::{date, time};
    ///
    /// let dt1 = date(2005, 11, 5).at(15, 30, 0, 0);
    /// let dt2 = dt1.with().time(time(23, 59, 59, 123_456_789)).build()?;
    /// // The time changes but the date remains the same.
    /// assert_eq!(dt2, date(2005, 11, 5).at(23, 59, 59, 123_456_789));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn time(self, time: Time) -> DateTimeWith {
        DateTimeWith { time_with: time.with(), ..self }
    }

    /// Set the year field on a [`DateTime`].
    ///
    /// One can access this value via [`DateTime::year`].
    ///
    /// This overrides any previous year settings.
    ///
    /// # Errors
    ///
    /// This returns an error when [`DateTimeWith::build`] is called if the
    /// given year is outside the range `-9999..=9999`. This can also return an
    /// error if the resulting date is otherwise invalid.
    ///
    /// # Example
    ///
    /// This shows how to create a new datetime with a different year:
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt1 = date(2005, 11, 5).at(15, 30, 0, 0);
    /// assert_eq!(dt1.year(), 2005);
    /// let dt2 = dt1.with().year(2007).build()?;
    /// assert_eq!(dt2.year(), 2007);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: only changing the year can fail
    ///
    /// For example, while `2024-02-29T01:30:00` is valid,
    /// `2023-02-29T01:30:00` is not:
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt = date(2024, 2, 29).at(1, 30, 0, 0);
    /// assert!(dt.with().year(2023).build().is_err());
    /// ```
    #[inline]
    pub fn year(self, year: i16) -> DateTimeWith {
        DateTimeWith { date_with: self.date_with.year(year), ..self }
    }

    /// Set year of a datetime via its era and its non-negative numeric
    /// component.
    ///
    /// One can access this value via [`DateTime::era_year`].
    ///
    /// # Errors
    ///
    /// This returns an error when [`DateTimeWith::build`] is called if the
    /// year is outside the range for the era specified. For [`Era::BCE`], the
    /// range is `1..=10000`. For [`Era::CE`], the range is `1..=9999`.
    ///
    /// # Example
    ///
    /// This shows that `CE` years are equivalent to the years used by this
    /// crate:
    ///
    /// ```
    /// use jiff::civil::{Era, date};
    ///
    /// let dt1 = date(2005, 11, 5).at(8, 0, 0, 0);
    /// assert_eq!(dt1.year(), 2005);
    /// let dt2 = dt1.with().era_year(2007, Era::CE).build()?;
    /// assert_eq!(dt2.year(), 2007);
    ///
    /// // CE years are always positive and can be at most 9999:
    /// assert!(dt1.with().era_year(-5, Era::CE).build().is_err());
    /// assert!(dt1.with().era_year(10_000, Era::CE).build().is_err());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// But `BCE` years always correspond to years less than or equal to `0`
    /// in this crate:
    ///
    /// ```
    /// use jiff::civil::{Era, date};
    ///
    /// let dt1 = date(-27, 7, 1).at(8, 22, 30, 0);
    /// assert_eq!(dt1.year(), -27);
    /// assert_eq!(dt1.era_year(), (28, Era::BCE));
    ///
    /// let dt2 = dt1.with().era_year(509, Era::BCE).build()?;
    /// assert_eq!(dt2.year(), -508);
    /// assert_eq!(dt2.era_year(), (509, Era::BCE));
    ///
    /// let dt2 = dt1.with().era_year(10_000, Era::BCE).build()?;
    /// assert_eq!(dt2.year(), -9_999);
    /// assert_eq!(dt2.era_year(), (10_000, Era::BCE));
    ///
    /// // BCE years are always positive and can be at most 10000:
    /// assert!(dt1.with().era_year(-5, Era::BCE).build().is_err());
    /// assert!(dt1.with().era_year(10_001, Era::BCE).build().is_err());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: overrides `DateTimeWith::year`
    ///
    /// Setting this option will override any previous `DateTimeWith::year`
    /// option:
    ///
    /// ```
    /// use jiff::civil::{Era, date};
    ///
    /// let dt1 = date(2024, 7, 2).at(10, 27, 10, 123);
    /// let dt2 = dt1.with().year(2000).era_year(1900, Era::CE).build()?;
    /// assert_eq!(dt2, date(1900, 7, 2).at(10, 27, 10, 123));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// Similarly, `DateTimeWith::year` will override any previous call to
    /// `DateTimeWith::era_year`:
    ///
    /// ```
    /// use jiff::civil::{Era, date};
    ///
    /// let dt1 = date(2024, 7, 2).at(19, 0, 1, 1);
    /// let dt2 = dt1.with().era_year(1900, Era::CE).year(2000).build()?;
    /// assert_eq!(dt2, date(2000, 7, 2).at(19, 0, 1, 1));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn era_year(self, year: i16, era: Era) -> DateTimeWith {
        DateTimeWith { date_with: self.date_with.era_year(year, era), ..self }
    }

    /// Set the month field on a [`DateTime`].
    ///
    /// One can access this value via [`DateTime::month`].
    ///
    /// This overrides any previous month settings.
    ///
    /// # Errors
    ///
    /// This returns an error when [`DateTimeWith::build`] is called if the
    /// given month is outside the range `1..=12`. This can also return an
    /// error if the resulting date is otherwise invalid.
    ///
    /// # Example
    ///
    /// This shows how to create a new datetime with a different month:
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt1 = date(2005, 11, 5).at(18, 3, 59, 123_456_789);
    /// assert_eq!(dt1.month(), 11);
    /// let dt2 = dt1.with().month(6).build()?;
    /// assert_eq!(dt2.month(), 6);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: only changing the month can fail
    ///
    /// For example, while `2024-10-31T00:00:00` is valid,
    /// `2024-11-31T00:00:00` is not:
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt = date(2024, 10, 31).at(0, 0, 0, 0);
    /// assert!(dt.with().month(11).build().is_err());
    /// ```
    #[inline]
    pub fn month(self, month: i8) -> DateTimeWith {
        DateTimeWith { date_with: self.date_with.month(month), ..self }
    }

    /// Set the day field on a [`DateTime`].
    ///
    /// One can access this value via [`DateTime::day`].
    ///
    /// This overrides any previous day settings.
    ///
    /// # Errors
    ///
    /// This returns an error when [`DateTimeWith::build`] is called if the
    /// given given day is outside of allowable days for the corresponding year
    /// and month fields.
    ///
    /// # Example
    ///
    /// This shows some examples of setting the day, including a leap day:
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt1 = date(2024, 2, 5).at(21, 59, 1, 999);
    /// assert_eq!(dt1.day(), 5);
    /// let dt2 = dt1.with().day(10).build()?;
    /// assert_eq!(dt2.day(), 10);
    /// let dt3 = dt1.with().day(29).build()?;
    /// assert_eq!(dt3.day(), 29);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: changing only the day can fail
    ///
    /// This shows some examples that will fail:
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt1 = date(2023, 2, 5).at(22, 58, 58, 9_999);
    /// // 2023 is not a leap year
    /// assert!(dt1.with().day(29).build().is_err());
    ///
    /// // September has 30 days, not 31.
    /// let dt1 = date(2023, 9, 5).at(22, 58, 58, 9_999);
    /// assert!(dt1.with().day(31).build().is_err());
    /// ```
    #[inline]
    pub fn day(self, day: i8) -> DateTimeWith {
        DateTimeWith { date_with: self.date_with.day(day), ..self }
    }

    /// Set the day field on a [`DateTime`] via the ordinal number of a day
    /// within a year.
    ///
    /// When used, any settings for month are ignored since the month is
    /// determined by the day of the year.
    ///
    /// The valid values for `day` are `1..=366`. Note though that `366` is
    /// only valid for leap years.
    ///
    /// This overrides any previous day settings.
    ///
    /// # Errors
    ///
    /// This returns an error when [`DateTimeWith::build`] is called if the
    /// given day is outside the allowed range of `1..=366`, or when a value of
    /// `366` is given for a non-leap year.
    ///
    /// # Example
    ///
    /// This demonstrates that if a year is a leap year, then `60` corresponds
    /// to February 29:
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt = date(2024, 1, 1).at(23, 59, 59, 999_999_999);
    /// assert_eq!(
    ///     dt.with().day_of_year(60).build()?,
    ///     date(2024, 2, 29).at(23, 59, 59, 999_999_999),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// But for non-leap years, day 60 is March 1:
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt = date(2023, 1, 1).at(23, 59, 59, 999_999_999);
    /// assert_eq!(
    ///     dt.with().day_of_year(60).build()?,
    ///     date(2023, 3, 1).at(23, 59, 59, 999_999_999),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// And using `366` for a non-leap year will result in an error, since
    /// non-leap years only have 365 days:
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt = date(2023, 1, 1).at(0, 0, 0, 0);
    /// assert!(dt.with().day_of_year(366).build().is_err());
    /// // The maximal year is not a leap year, so it returns an error too.
    /// let dt = date(9999, 1, 1).at(0, 0, 0, 0);
    /// assert!(dt.with().day_of_year(366).build().is_err());
    /// ```
    #[inline]
    pub fn day_of_year(self, day: i16) -> DateTimeWith {
        DateTimeWith { date_with: self.date_with.day_of_year(day), ..self }
    }

    /// Set the day field on a [`DateTime`] via the ordinal number of a day
    /// within a year, but ignoring leap years.
    ///
    /// When used, any settings for month are ignored since the month is
    /// determined by the day of the year.
    ///
    /// The valid values for `day` are `1..=365`. The value `365` always
    /// corresponds to the last day of the year, even for leap years. It is
    /// impossible for this routine to return a datetime corresponding to
    /// February 29.
    ///
    /// This overrides any previous day settings.
    ///
    /// # Errors
    ///
    /// This returns an error when [`DateTimeWith::build`] is called if the
    /// given day is outside the allowed range of `1..=365`.
    ///
    /// # Example
    ///
    /// This demonstrates that `60` corresponds to March 1, regardless of
    /// whether the year is a leap year or not:
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt = date(2023, 1, 1).at(23, 59, 59, 999_999_999);
    /// assert_eq!(
    ///     dt.with().day_of_year_no_leap(60).build()?,
    ///     date(2023, 3, 1).at(23, 59, 59, 999_999_999),
    /// );
    ///
    /// let dt = date(2024, 1, 1).at(23, 59, 59, 999_999_999);
    /// assert_eq!(
    ///     dt.with().day_of_year_no_leap(60).build()?,
    ///     date(2024, 3, 1).at(23, 59, 59, 999_999_999),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// And using `365` for any year will always yield the last day of the
    /// year:
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt = date(2023, 1, 1).at(23, 59, 59, 999_999_999);
    /// assert_eq!(
    ///     dt.with().day_of_year_no_leap(365).build()?,
    ///     dt.last_of_year(),
    /// );
    ///
    /// let dt = date(2024, 1, 1).at(23, 59, 59, 999_999_999);
    /// assert_eq!(
    ///     dt.with().day_of_year_no_leap(365).build()?,
    ///     dt.last_of_year(),
    /// );
    ///
    /// let dt = date(9999, 1, 1).at(23, 59, 59, 999_999_999);
    /// assert_eq!(
    ///     dt.with().day_of_year_no_leap(365).build()?,
    ///     dt.last_of_year(),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// A value of `366` is out of bounds, even for leap years:
    ///
    /// ```
    /// use jiff::civil::date;
    ///
    /// let dt = date(2024, 1, 1).at(5, 30, 0, 0);
    /// assert!(dt.with().day_of_year_no_leap(366).build().is_err());
    /// ```
    #[inline]
    pub fn day_of_year_no_leap(self, day: i16) -> DateTimeWith {
        DateTimeWith {
            date_with: self.date_with.day_of_year_no_leap(day),
            ..self
        }
    }

    /// Set the hour field on a [`DateTime`].
    ///
    /// One can access this value via [`DateTime::hour`].
    ///
    /// This overrides any previous hour settings.
    ///
    /// # Errors
    ///
    /// This returns an error when [`DateTimeWith::build`] is called if the
    /// given hour is outside the range `0..=23`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::time;
    ///
    /// let dt1 = time(15, 21, 59, 0).on(2010, 6, 1);
    /// assert_eq!(dt1.hour(), 15);
    /// let dt2 = dt1.with().hour(3).build()?;
    /// assert_eq!(dt2.hour(), 3);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn hour(self, hour: i8) -> DateTimeWith {
        DateTimeWith { time_with: self.time_with.hour(hour), ..self }
    }

    /// Set the minute field on a [`DateTime`].
    ///
    /// One can access this value via [`DateTime::minute`].
    ///
    /// This overrides any previous minute settings.
    ///
    /// # Errors
    ///
    /// This returns an error when [`DateTimeWith::build`] is called if the
    /// given minute is outside the range `0..=59`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::time;
    ///
    /// let dt1 = time(15, 21, 59, 0).on(2010, 6, 1);
    /// assert_eq!(dt1.minute(), 21);
    /// let dt2 = dt1.with().minute(3).build()?;
    /// assert_eq!(dt2.minute(), 3);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn minute(self, minute: i8) -> DateTimeWith {
        DateTimeWith { time_with: self.time_with.minute(minute), ..self }
    }

    /// Set the second field on a [`DateTime`].
    ///
    /// One can access this value via [`DateTime::second`].
    ///
    /// This overrides any previous second settings.
    ///
    /// # Errors
    ///
    /// This returns an error when [`DateTimeWith::build`] is called if the
    /// given second is outside the range `0..=59`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::time;
    ///
    /// let dt1 = time(15, 21, 59, 0).on(2010, 6, 1);
    /// assert_eq!(dt1.second(), 59);
    /// let dt2 = dt1.with().second(3).build()?;
    /// assert_eq!(dt2.second(), 3);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn second(self, second: i8) -> DateTimeWith {
        DateTimeWith { time_with: self.time_with.second(second), ..self }
    }

    /// Set the millisecond field on a [`DateTime`].
    ///
    /// One can access this value via [`DateTime::millisecond`].
    ///
    /// This overrides any previous millisecond settings.
    ///
    /// # Errors
    ///
    /// This returns an error when [`DateTimeWith::build`] is called if the
    /// given millisecond is outside the range `0..=999`, or if both this and
    /// [`DateTimeWith::subsec_nanosecond`] are set.
    ///
    /// # Example
    ///
    /// This shows the relationship between [`DateTime::millisecond`] and
    /// [`DateTime::subsec_nanosecond`]:
    ///
    /// ```
    /// use jiff::civil::time;
    ///
    /// let dt1 = time(15, 21, 35, 0).on(2010, 6, 1);
    /// let dt2 = dt1.with().millisecond(123).build()?;
    /// assert_eq!(dt2.subsec_nanosecond(), 123_000_000);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn millisecond(self, millisecond: i16) -> DateTimeWith {
        DateTimeWith {
            time_with: self.time_with.millisecond(millisecond),
            ..self
        }
    }

    /// Set the microsecond field on a [`DateTime`].
    ///
    /// One can access this value via [`DateTime::microsecond`].
    ///
    /// This overrides any previous microsecond settings.
    ///
    /// # Errors
    ///
    /// This returns an error when [`DateTimeWith::build`] is called if the
    /// given microsecond is outside the range `0..=999`, or if both this and
    /// [`DateTimeWith::subsec_nanosecond`] are set.
    ///
    /// # Example
    ///
    /// This shows the relationship between [`DateTime::microsecond`] and
    /// [`DateTime::subsec_nanosecond`]:
    ///
    /// ```
    /// use jiff::civil::time;
    ///
    /// let dt1 = time(15, 21, 35, 0).on(2010, 6, 1);
    /// let dt2 = dt1.with().microsecond(123).build()?;
    /// assert_eq!(dt2.subsec_nanosecond(), 123_000);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn microsecond(self, microsecond: i16) -> DateTimeWith {
        DateTimeWith {
            time_with: self.time_with.microsecond(microsecond),
            ..self
        }
    }

    /// Set the nanosecond field on a [`DateTime`].
    ///
    /// One can access this value via [`DateTime::nanosecond`].
    ///
    /// This overrides any previous nanosecond settings.
    ///
    /// # Errors
    ///
    /// This returns an error when [`DateTimeWith::build`] is called if the
    /// given nanosecond is outside the range `0..=999`, or if both this and
    /// [`DateTimeWith::subsec_nanosecond`] are set.
    ///
    /// # Example
    ///
    /// This shows the relationship between [`DateTime::nanosecond`] and
    /// [`DateTime::subsec_nanosecond`]:
    ///
    /// ```
    /// use jiff::civil::time;
    ///
    /// let dt1 = time(15, 21, 35, 0).on(2010, 6, 1);
    /// let dt2 = dt1.with().nanosecond(123).build()?;
    /// assert_eq!(dt2.subsec_nanosecond(), 123);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn nanosecond(self, nanosecond: i16) -> DateTimeWith {
        DateTimeWith {
            time_with: self.time_with.nanosecond(nanosecond),
            ..self
        }
    }

    /// Set the subsecond nanosecond field on a [`DateTime`].
    ///
    /// If you want to access this value on `DateTime`, then use
    /// [`DateTime::subsec_nanosecond`].
    ///
    /// This overrides any previous subsecond nanosecond settings.
    ///
    /// # Errors
    ///
    /// This returns an error when [`DateTimeWith::build`] is called if the
    /// given subsecond nanosecond is outside the range `0..=999,999,999`,
    /// or if both this and one of [`DateTimeWith::millisecond`],
    /// [`DateTimeWith::microsecond`] or [`DateTimeWith::nanosecond`] are set.
    ///
    /// # Example
    ///
    /// This shows the relationship between constructing a `DateTime` value
    /// with subsecond nanoseconds and its individual subsecond fields:
    ///
    /// ```
    /// use jiff::civil::time;
    ///
    /// let dt1 = time(15, 21, 35, 0).on(2010, 6, 1);
    /// let dt2 = dt1.with().subsec_nanosecond(123_456_789).build()?;
    /// assert_eq!(dt2.millisecond(), 123);
    /// assert_eq!(dt2.microsecond(), 456);
    /// assert_eq!(dt2.nanosecond(), 789);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn subsec_nanosecond(self, subsec_nanosecond: i32) -> DateTimeWith {
        DateTimeWith {
            time_with: self.time_with.subsec_nanosecond(subsec_nanosecond),
            ..self
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        civil::{date, time},
        RoundMode, ToSpan, Unit,
    };

    use super::*;

    #[test]
    fn from_temporal_docs() {
        let dt = DateTime::from_parts(
            date(1995, 12, 7),
            time(3, 24, 30, 000_003_500),
        );

        let got = dt.round(Unit::Hour).unwrap();
        let expected =
            DateTime::from_parts(date(1995, 12, 7), time(3, 0, 0, 0));
        assert_eq!(got, expected);

        let got = dt.round((Unit::Minute, 30)).unwrap();
        let expected =
            DateTime::from_parts(date(1995, 12, 7), time(3, 30, 0, 0));
        assert_eq!(got, expected);

        let got = dt
            .round(
                DateTimeRound::new()
                    .smallest(Unit::Minute)
                    .increment(30)
                    .mode(RoundMode::Floor),
            )
            .unwrap();
        let expected =
            DateTime::from_parts(date(1995, 12, 7), time(3, 0, 0, 0));
        assert_eq!(got, expected);
    }

    #[test]
    fn since() {
        let later = date(2024, 5, 9).at(2, 0, 0, 0);
        let earlier = date(2024, 5, 8).at(3, 0, 0, 0);
        assert_eq!(later.since(earlier).unwrap(), 23.hours());

        let later = date(2024, 5, 9).at(3, 0, 0, 0);
        let earlier = date(2024, 5, 8).at(2, 0, 0, 0);
        assert_eq!(later.since(earlier).unwrap(), 1.days().hours(1));

        let later = date(2024, 5, 9).at(2, 0, 0, 0);
        let earlier = date(2024, 5, 10).at(3, 0, 0, 0);
        assert_eq!(later.since(earlier).unwrap(), -1.days().hours(1));

        let later = date(2024, 5, 9).at(3, 0, 0, 0);
        let earlier = date(2024, 5, 10).at(2, 0, 0, 0);
        assert_eq!(later.since(earlier).unwrap(), -23.hours());
    }

    #[test]
    fn until() {
        let a = date(9999, 12, 30).at(3, 0, 0, 0);
        let b = date(9999, 12, 31).at(2, 0, 0, 0);
        assert_eq!(a.until(b).unwrap(), 23.hours());

        let a = date(-9999, 1, 2).at(2, 0, 0, 0);
        let b = date(-9999, 1, 1).at(3, 0, 0, 0);
        assert_eq!(a.until(b).unwrap(), -23.hours());

        let a = date(1995, 12, 7).at(3, 24, 30, 3500);
        let b = date(2019, 1, 31).at(15, 30, 0, 0);
        assert_eq!(
            a.until(b).unwrap(),
            8456.days()
                .hours(12)
                .minutes(5)
                .seconds(29)
                .milliseconds(999)
                .microseconds(996)
                .nanoseconds(500)
        );
        assert_eq!(
            a.until((Unit::Year, b)).unwrap(),
            23.years()
                .months(1)
                .days(24)
                .hours(12)
                .minutes(5)
                .seconds(29)
                .milliseconds(999)
                .microseconds(996)
                .nanoseconds(500)
        );
        assert_eq!(
            b.until((Unit::Year, a)).unwrap(),
            -23.years()
                .months(1)
                .days(24)
                .hours(12)
                .minutes(5)
                .seconds(29)
                .milliseconds(999)
                .microseconds(996)
                .nanoseconds(500)
        );
        assert_eq!(
            a.until((Unit::Nanosecond, b)).unwrap(),
            730641929999996500i64.nanoseconds(),
        );

        let a = date(-9999, 1, 1).at(0, 0, 0, 0);
        let b = date(9999, 12, 31).at(23, 59, 59, 999_999_999);
        assert!(a.until((Unit::Nanosecond, b)).is_err());
        assert_eq!(
            a.until((Unit::Microsecond, b)).unwrap(),
            Span::new()
                .microseconds(631_107_417_600_000_000i64 - 1)
                .nanoseconds(999),
        );
    }

    #[test]
    fn until_month_lengths() {
        let jan1 = date(2020, 1, 1).at(0, 0, 0, 0);
        let feb1 = date(2020, 2, 1).at(0, 0, 0, 0);
        let mar1 = date(2020, 3, 1).at(0, 0, 0, 0);

        assert_eq!(jan1.until(feb1).unwrap(), 31.days());
        assert_eq!(jan1.until((Unit::Month, feb1)).unwrap(), 1.month());
        assert_eq!(feb1.until(mar1).unwrap(), 29.days());
        assert_eq!(feb1.until((Unit::Month, mar1)).unwrap(), 1.month());
        assert_eq!(jan1.until(mar1).unwrap(), 60.days());
        assert_eq!(jan1.until((Unit::Month, mar1)).unwrap(), 2.months());
    }

    #[test]
    fn datetime_size() {
        #[cfg(debug_assertions)]
        {
            assert_eq!(36, core::mem::size_of::<DateTime>());
        }
        #[cfg(not(debug_assertions))]
        {
            assert_eq!(12, core::mem::size_of::<DateTime>());
        }
    }
}
