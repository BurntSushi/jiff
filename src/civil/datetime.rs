use core::ops::{Add, AddAssign, Sub, SubAssign};

use crate::{
    civil::{Date, Time},
    error::Error,
    instant::{datetime_zulu_to_time_duration, Instant, TimeScale},
    round::{Round, Unit},
    span::{Span, TimeDuration},
    tz::TimeZone,
    util::{
        rangeint::{RFrom, RInto},
        t::{self, C},
    },
    zoned::Zoned,
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
/// A `DateTime` value behaves without regard to daylight savings time or time
/// zones in general. When doing arithmetic on datetimes with spans defined in
/// units of time (such as with [`DateTime::checked_add`]), days are considered
/// to always be precisely `86,400` seconds long.
///
/// # Default value
///
/// For convenience, this type implements the `Default` trait. Its default
/// value corresponds to `000-01-01T00:00:00.000000000`. That is, it is
/// the datetime corresponding to `DateTime::from_parts(Date::default(),
/// Time::default())`. One can also access this value via the `DateTime::ZERO`
/// constant.
///
/// # Leap seconds
///
/// Since this is a representation of civil datetime, a `DateTime` value does
/// not account for leap seconds or timezone transitions (such as DST). If a
/// `DateTime` value is parsed from a string containing a leap second (for
/// example, `2015-06-30T23:59:60`), then the leap second is automatically
/// clamped as if it were `59`. If you need leap second support, you'll need to
/// use a [`Instant`] with the `UTC` scale.
///
/// # Comparisons
///
/// The `DateTime` type provides both `Eq` and `Ord` trait implementations to
/// facilitate easy comparisons. When a datetime `dt1` occurs before a datetime
/// `dt2`, then `dt1 < dt2`. For example:
///
/// ```
/// use jiff::civil::DateTime;
///
/// let dt1 = DateTime::constant(2024, 3, 11, 1, 25, 15, 0);
/// let dt2 = DateTime::constant(2025, 1, 31, 0, 30, 0, 0);
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
/// use jiff::{civil::DateTime, ToSpan};
///
/// let start = DateTime::constant(2024, 2, 25, 15, 45, 0, 0);
/// let one_week_later = start + 1.weeks();
/// assert_eq!(one_week_later, DateTime::constant(2024, 3, 3, 15, 45, 0, 0));
/// ```
///
/// It is also possible to compute the span of time between two datetimes using
/// either [`DateTime::until`] or [`DateTime::since`]. It's also possible to
/// subtract two `DateTime` values directly via a `Sub` trait implementation:
///
/// ```
/// use jiff::{civil::DateTime, ToSpan};
///
/// let datetime1 = DateTime::constant(2024, 3, 3, 23, 30, 0, 0);
/// let datetime2 = DateTime::constant(2024, 2, 25, 22, 0, 0, 0);
/// assert_eq!(datetime1 - datetime2, 7.days().hours(1).minutes(30));
/// ```
///
/// # Rounding
///
/// TODO: Fill out this section once we've settled on a rounding API.
#[derive(Clone, Copy, Eq, PartialEq, PartialOrd, Ord)]
pub struct DateTime {
    date: Date,
    time: Time,
}

impl DateTime {
    /// The minimum representable Gregorian datetime.
    ///
    /// The minimum is chosen such that any [`Instant`] combined with any
    /// valid time zone offset can be infallibly converted to this type. This
    /// means that the minimum `Instant` is guaranteed to be bigger than the
    /// minimum `DateTime`.
    pub const MIN: DateTime = DateTime::constant(-9999, 1, 1, 0, 0, 0, 0);

    /// The maximum representable Gregorian datetime.
    ///
    /// The maximum is chosen such that any [`Instant`] combined with any
    /// valid time zone offset can be infallibly converted to this type. This
    /// means that the maximum `Instant` is guaranteed to be smaller than the
    /// maximum `DateTime`.
    pub const MAX: DateTime =
        DateTime::constant(9999, 12, 31, 23, 59, 59, 999_999_999);

    /// The first day of the zeroth year.
    ///
    /// This is guaranteed to be equivalent to `Date::default()`.
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
    /// hour, minute and second values.
    ///
    /// For convenience, this constructor does not accept a fractional
    /// nanosecond component and instead sets the fractional part to `0`.
    /// To set the fractional component, among other component values
    /// of a datetime after creating it, use [`DateTime::then_date`] or
    /// [`DateTime::then_time`] with one of the following routines:
    ///
    /// * [`Date::with_year`] creates a new date with the given year.
    /// * [`Date::with_month`] creates a new date with the given month.
    /// * [`Date::with_day`] creates a new date with the given day.
    /// * [`Time::with_subsec_nanosecond`] sets the whole fractional part.
    /// * [`Time::with_millisecond`] sets only the millisecond part.
    /// * [`Time::with_microsecond`] sets only the microsecond part.
    /// * [`Time::with_nanosecond`] sets only the nanosecond part.
    ///
    /// # Errors
    ///
    /// This returns an error when the given year-month-day-hour-minute-second
    /// does not correspond to a valid datetime. Namely, all of the following
    /// must be true:
    ///
    /// * The year must be in the range `-9999..=9999`.
    /// * The month must be in the range `1..=12`.
    /// * The day must be at least `1` and must be at most the number of days
    /// in the corresponding month. So for example, `2024-02-29` is valid but
    /// `2023-02-29` is not.
    /// * `0 <= hour <= 23`
    /// * `0 <= minute <= 59`
    /// * `0 <= second <= 59`
    ///
    /// # Example
    ///
    /// This shows an example of a valid datetime:
    ///
    /// ```
    /// use jiff::civil::DateTime;
    ///
    /// let d = DateTime::new(2024, 2, 29, 21, 30, 5).unwrap();
    /// assert_eq!(d.date().year(), 2024);
    /// assert_eq!(d.date().month(), 2);
    /// assert_eq!(d.date().day(), 29);
    /// assert_eq!(d.time().hour(), 21);
    /// assert_eq!(d.time().minute(), 30);
    /// assert_eq!(d.time().second(), 5);
    /// ```
    ///
    /// This shows some examples of invalid datetimes:
    ///
    /// ```
    /// use jiff::civil::DateTime;
    ///
    /// assert!(DateTime::new(2023, 2, 29, 21, 30, 5).is_err());
    /// assert!(DateTime::new(2015, 6, 30, 23, 59, 61).is_err());
    /// ```
    ///
    /// And this shows how to set the fractional nanosecond of a datetime:
    ///
    /// ```
    /// use jiff::civil::DateTime;
    ///
    /// let d = DateTime::new(2024, 2, 29, 21, 30, 5)?.then_time(|t| {
    ///     t.with_subsec_nanosecond(123_456_789)
    /// })?;
    /// assert_eq!(d.time().millisecond(), 123);
    /// assert_eq!(d.time().microsecond(), 456);
    /// assert_eq!(d.time().nanosecond(), 789);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn new(
        year: i16,
        month: i8,
        day: i8,
        hour: i8,
        minute: i8,
        second: i8,
    ) -> Result<DateTime, Error> {
        let date = Date::new(year, month, day)?;
        let time = Time::new(hour, minute, second)?;
        Ok(DateTime { date, time })
    }

    /// Creates a new `DateTime` value in a `const` context.
    ///
    /// # Panics
    ///
    /// This routine panics when [`DateTime::new`] would return an error. That
    /// is, when the given year-month-day-hour-minute-second-subsec does not
    /// correspond to a valid datetime. Namely, all of the following must be
    /// true:
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
    /// ```
    /// use jiff::civil::DateTime;
    ///
    /// let d = DateTime::constant(2024, 2, 29, 21, 30, 5, 123_456_789);
    /// assert_eq!(d.date().year(), 2024);
    /// assert_eq!(d.date().month(), 2);
    /// assert_eq!(d.date().day(), 29);
    /// assert_eq!(d.time().hour(), 21);
    /// assert_eq!(d.time().minute(), 30);
    /// assert_eq!(d.time().second(), 5);
    /// assert_eq!(d.time().millisecond(), 123);
    /// assert_eq!(d.time().microsecond(), 456);
    /// assert_eq!(d.time().nanosecond(), 789);
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

    /// Returns the current datetime.
    ///
    /// # Panics
    ///
    /// This panics if the system clock is set to a time value outside of the
    /// range `-9999-01-02T00:00:00Z..=9999-12-30T11:59:59.999999999Z`. The
    /// justification here is that it is reasonable to expect the system clock
    /// to be set to a somewhat sane, if imprecise, value.
    ///
    /// If you want to get the current time fallibly, use
    /// [`Instant::now_with_scale`] (where [`Unix`](crate::Unix) is the default
    /// time scale), and then use `Date::from(instant)`.
    ///
    /// # Example
    ///
    /// This example shows how to get the first day in the current month at
    /// the current time:
    ///
    /// ```
    /// use jiff::civil::DateTime;
    ///
    /// let dt = DateTime::now().map_date(|date| date.first_of_month());
    /// assert_eq!(dt.date().day(), 1);
    /// ```
    #[inline]
    pub fn now() -> DateTime {
        Instant::now().to_datetime()
    }

    /// Converts an instant in time to a Gregorian datetime.
    ///
    /// This is also available via a `From<Instant>` trait implementation.
    ///
    /// # Example
    ///
    /// This example demonstrates the Unix epoch:
    ///
    /// ```
    /// use jiff::{civil::DateTime, Instant};
    ///
    /// let instant = Instant::from_unix(0, 0).unwrap();
    /// let date = DateTime::from_instant(instant);
    /// assert_eq!(date, DateTime::constant(1970, 1, 1, 0, 0, 0, 0));
    /// ```
    ///
    /// This example shows how negative Unix timestamps are handled:
    ///
    /// ```
    /// use jiff::{civil::DateTime, Instant};
    ///
    /// let instant = Instant::from_unix(0, -1).unwrap();
    /// let date = DateTime::from_instant(instant);
    /// assert_eq!(
    ///     date,
    ///     DateTime::constant(1969, 12, 31, 23, 59, 59, 999_999_999),
    /// );
    /// ```
    #[inline]
    pub fn from_instant<S: TimeScale>(instant: Instant<S>) -> DateTime {
        instant.to_datetime()
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
    /// use jiff::civil::{Date, DateTime, Time};
    ///
    /// let dt = DateTime::from_parts(
    ///     Date::constant(2024, 6, 6),
    ///     Time::constant(6, 0, 0, 0),
    /// );
    /// assert_eq!(dt, DateTime::constant(2024, 6, 6, 6, 0, 0, 0));
    /// ```
    #[inline]
    pub const fn from_parts(date: Date, time: Time) -> DateTime {
        DateTime { date, time }
    }

    /// Returns a new datetime with its date component set to the given value.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::{Date, DateTime};
    ///
    /// let dt = DateTime::constant(2024, 3, 5, 2, 22, 22, 0);
    /// assert_eq!(
    ///     dt.with_date(Date::constant(2023, 10, 1)),
    ///     DateTime::constant(2023, 10, 1, 2, 22, 22, 0),
    /// );
    /// ```
    #[inline]
    pub fn with_date(self, date: Date) -> DateTime {
        DateTime::from_parts(date, self.time())
    }

    /// Returns a new datetime with its time component set to the given value.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::{DateTime, Time};
    ///
    /// let dt = DateTime::constant(2024, 3, 5, 2, 22, 22, 0);
    /// assert_eq!(
    ///     dt.with_time(Time::midnight()),
    ///     DateTime::constant(2024, 3, 5, 0, 0, 0, 0),
    /// );
    /// ```
    #[inline]
    pub fn with_time(self, time: Time) -> DateTime {
        DateTime::from_parts(self.date(), time)
    }

    /// Return a new `DateTime` with its `Date` component set to the value
    /// returned by the given closure.
    ///
    /// The closure is called with this datetime's date component.
    ///
    /// If you want to set the date based on a fallible routine, use
    /// [`DateTime::then_date`] instead.
    ///
    /// # Example
    ///
    /// This example shows how to get a `DateTime` at the following day with
    /// the same time, but where we saturate if the next day would otherwise
    /// overflow the bounds of a `DateTime`.
    ///
    /// ```
    /// use jiff::{civil::DateTime, ToSpan};
    ///
    /// let dt = DateTime::constant(2024, 2, 28, 17, 30, 0, 0);
    /// let tomorrow = dt.map_date(|d| d.saturating_add(1.days()));
    /// assert_eq!(tomorrow, DateTime::constant(2024, 2, 29, 17, 30, 0, 0));
    ///
    /// // If we're already at the maximal date, then the same date is returned
    /// // because we're using saturating arithmetic.
    /// let dt = DateTime::constant(9999, 12, 31, 17, 30, 0, 0);
    /// let tomorrow = dt.map_date(|d| d.saturating_add(1.days()));
    /// assert_eq!(tomorrow, dt);
    /// ```
    #[inline]
    pub fn map_date(self, map: impl FnOnce(Date) -> Date) -> DateTime {
        DateTime { date: map(self.date), ..self }
    }

    /// Return a new `DateTime` with its `Time` component set to the value
    /// returned by the given closure.
    ///
    /// The closure is called with this datetime's time component.
    ///
    /// # Example
    ///
    /// This example shows how to get a `DateTime` with the time set to five
    /// minutes later without crossing into the next day.
    ///
    /// ```
    /// use jiff::{civil::DateTime, ToSpan};
    ///
    /// let dt = DateTime::constant(2024, 2, 28, 17, 30, 0, 0);
    /// let five_later = dt.map_time(|t| t.saturating_add(5.minutes()));
    /// assert_eq!(five_later, DateTime::constant(2024, 2, 28, 17, 35, 0, 0));
    ///
    /// // If we're within 5 minutes of the day's end, then we'll be capped
    /// // at the maximal part of the current day.
    /// // because we're using saturating arithmetic.
    /// let dt = DateTime::constant(2024, 2, 28, 23, 58, 0, 0);
    /// let five_later = dt.map_time(|t| t.saturating_add(5.minutes()));
    /// assert_eq!(
    ///     five_later,
    ///     DateTime::constant(2024, 2, 28, 23, 59, 59, 999_999_999),
    /// );
    /// ```
    #[inline]
    pub fn map_time(self, map: impl FnOnce(Time) -> Time) -> DateTime {
        DateTime { time: map(self.time), ..self }
    }

    /// Given a closure that fallibly returns a `Date`, this creates a new
    /// `DateTime` with the `Date` returned when the closure is successful.
    /// Otherwise, the error returned by the closure is returned.
    ///
    /// If you want to set the date based on an infallible routine, use
    /// [`DateTime::map_date`] instead.
    ///
    /// # Example
    ///
    /// This example shows how to get a `DateTime` for the following Thursday
    /// at the same time:
    ///
    /// ```
    /// use jiff::{civil::{DateTime, Weekday}, ToSpan};
    ///
    /// let dt = DateTime::constant(2024, 2, 23, 17, 30, 0, 0);
    /// let next_thurs = dt.then_date(|d| {
    ///     d.nth_weekday(1, Weekday::Thursday)
    /// })?;
    /// assert_eq!(next_thurs, DateTime::constant(2024, 2, 29, 17, 30, 0, 0));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// The [`Date::nth_weekday`] routine can fail when the day would exceed
    /// the limits of `Date`. In this case, the error is returned instead of
    /// a new `DateTime`:
    ///
    /// ```
    /// use jiff::{civil::{DateTime, Weekday}, ToSpan};
    ///
    /// let dt = DateTime::constant(2024, 2, 23, 17, 30, 0, 0);
    /// assert!(dt.then_date(|d| {
    ///     d.nth_weekday(i32::MAX, Weekday::Thursday)
    /// }).is_err());
    /// ```
    #[inline]
    pub fn then_date<E>(
        self,
        then: impl FnOnce(Date) -> Result<Date, E>,
    ) -> Result<DateTime, E> {
        Ok(DateTime { date: then(self.date)?, ..self })
    }

    /// Given a closure that fallibly returns a `Time`, this creates a new
    /// `DateTime` with the `Time` returned when the closure is successful.
    /// Otherwise, the error returned by the closure is returned.
    ///
    /// If you want to set the time based on an infallible routine, use
    /// [`DateTime::map_time`] instead.
    ///
    /// # Example
    ///
    /// This example shows how to get a `DateTime` with the time set to five
    /// minutes later, but where an error is returned if this would cross over
    /// into the next day:
    ///
    /// ```
    /// use jiff::{civil::DateTime, ToSpan};
    ///
    /// let dt = DateTime::constant(2024, 2, 28, 17, 30, 0, 0);
    /// let five_later = dt.then_time(|t| t.checked_add(5.minutes()))?;
    /// assert_eq!(five_later, DateTime::constant(2024, 2, 28, 17, 35, 0, 0));
    ///
    /// // If we're within 5 minutes of the day's end, then the checked
    /// // arithmetic will fail and we'll get an error.
    /// let dt = DateTime::constant(2024, 2, 28, 23, 58, 0, 0);
    /// assert!(dt.then_time(|t| t.checked_add(5.minutes())).is_err());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn then_time<E>(
        self,
        then: impl FnOnce(Time) -> Result<Time, E>,
    ) -> Result<DateTime, E> {
        Ok(DateTime { time: then(self.time)?, ..self })
    }

    /// Returns the date component of this datetime.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::{Date, DateTime};
    ///
    /// let dt = DateTime::constant(2024, 3, 14, 18, 45, 0, 0);
    /// assert_eq!(dt.date(), Date::constant(2024, 3, 14));
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
    /// use jiff::civil::{DateTime, Time};
    ///
    /// let dt = DateTime::constant(2024, 3, 14, 18, 45, 0, 0);
    /// assert_eq!(dt.time(), Time::constant(18, 45, 0, 0));
    /// ```
    #[inline]
    pub fn time(self) -> Time {
        self.time
    }

    /// TODO: Temporal doesn't have this sort of routine, instead requiring a
    /// conversion to a Zoned type. From there you can get an instant. I'm
    /// not sure I buy that ceremony, but it might be wise to start with
    /// that.
    #[inline]
    pub(crate) fn to_zulu<S: TimeScale>(self) -> Result<Instant<S>, Error> {
        Instant::from_datetime_zulu(self)
    }

    #[inline]
    pub fn to_zoned<S: TimeScale>(
        self,
        iana_time_zone_name: &str,
    ) -> Result<Zoned<S>, Error> {
        let tz = crate::tz::db().get(iana_time_zone_name)?;
        self.to_zoned_with(tz)
    }

    #[inline]
    pub fn to_zoned_with<S: TimeScale>(
        self,
        tz: TimeZone,
    ) -> Result<Zoned<S>, Error> {
        let instant = tz.to_instant_with_scale(self)?;
        Ok(Zoned::new(instant, tz))
    }

    /// Add the given span of time to this datetime. If the sum would overflow
    /// the minimum or maximum datetime values, then an error is returned.
    ///
    /// # Properties
    ///
    /// This routine is _not_ commutative because some additions may
    /// be ambiguous. For example, adding `1 month` to the datetime
    /// `2024-03-31T00:00:00` will produce `2024-04-30T00:00:00` since April
    /// has only 30 days in a month. Moreover, subtracting `1 month` from
    /// `2024-04-30T00:00:00` will produce `2024-03-30T00:00:00`, which is not
    /// the date we started with.
    ///
    /// If spans of time are limited to units of days (or less), then this
    /// routine _is_ commutative.
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
    /// use jiff::{civil::DateTime, ToSpan};
    ///
    /// let dt = DateTime::constant(1995, 12, 7, 3, 24, 30, 3_500);
    /// let got = dt.checked_add(20.years().months(4).nanoseconds(500))?;
    /// assert_eq!(got, DateTime::constant(2016, 4, 7, 3, 24, 30, 4_000));
    ///
    /// let dt = DateTime::constant(2019, 1, 31, 15, 30, 0, 0);
    /// let got = dt.checked_add(1.months())?;
    /// assert_eq!(got, DateTime::constant(2019, 2, 28, 15, 30, 0, 0));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// Negative spans are also supported:
    ///
    /// ```
    /// use jiff::{civil::DateTime, ToSpan};
    ///
    /// let dt = DateTime::constant(2024, 3, 31, 19, 5, 59, 999_999_999);
    /// assert_eq!(
    ///     dt.checked_add(-1.months())?,
    ///     DateTime::constant(2024, 2, 29, 19, 5, 59, 999_999_999),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// Exceeding the bounds of `DateTime` in either direction results in an
    /// error:
    ///
    /// ```
    /// use jiff::{civil::DateTime, ToSpan};
    ///
    /// let dt = DateTime::constant(2024, 3, 31, 13, 13, 13, 13);
    /// assert!(dt.checked_add(9000.years()).is_err());
    /// assert!(dt.checked_add(-19000.years()).is_err());
    /// ```
    #[inline]
    pub fn checked_add(self, span: Span) -> Result<DateTime, Error> {
        let (new_time, leftovers) =
            self.time().overflowing_add(span.only_lower(Unit::Day))?;
        let new_date = self
            .date()
            .checked_add(span.without_lower(Unit::Day))?
            .checked_add(leftovers)?;
        Ok(DateTime::from_parts(new_date, new_time))
    }

    /// Subtract the given span of time from this datetime. If the difference
    /// would overflow the minimum or maximum datetime values, then an error is
    /// returned.
    ///
    /// # Properties
    ///
    /// This routine is _not_ commutative because some additions may
    /// be ambiguous. For example, adding `1 month` to the datetime
    /// `2024-03-31T00:00:00` will produce `2024-04-30T00:00:00` since April
    /// has only 30 days in a month. Moreover, subtracting `1 month` from
    /// `2024-04-30T00:00:00` will produce `2024-03-30T00:00:00`, which is not
    /// the date we started with.
    ///
    /// If spans of time are limited to units of days (or less), then this
    /// routine _is_ commutative.
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
    /// use jiff::{civil::DateTime, ToSpan};
    ///
    /// let dt = DateTime::constant(1995, 12, 7, 3, 24, 30, 3_500);
    /// let got = dt.checked_sub(20.years().months(4).nanoseconds(500))?;
    /// assert_eq!(got, DateTime::constant(1975, 8, 7, 3, 24, 30, 3_000));
    ///
    /// let dt = DateTime::constant(2019, 2, 28, 15, 30, 0, 0);
    /// let got = dt.checked_sub(1.months())?;
    /// assert_eq!(got, DateTime::constant(2019, 1, 28, 15, 30, 0, 0));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// Negative spans are also supported:
    ///
    /// ```
    /// use jiff::{civil::DateTime, ToSpan};
    ///
    /// let dt = DateTime::constant(2024, 3, 31, 19, 5, 59, 999_999_999);
    /// assert_eq!(
    ///     dt.checked_sub(-1.months())?,
    ///     DateTime::constant(2024, 4, 30, 19, 5, 59, 999_999_999),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// Exceeding the bounds of `DateTime` in either direction results in an
    /// error:
    ///
    /// ```
    /// use jiff::{civil::DateTime, ToSpan};
    ///
    /// let dt = DateTime::constant(2024, 3, 31, 13, 13, 13, 13);
    /// assert!(dt.checked_sub(19000.years()).is_err());
    /// assert!(dt.checked_sub(-9000.years()).is_err());
    /// ```
    #[inline]
    pub fn checked_sub(self, span: Span) -> Result<DateTime, Error> {
        self.checked_add(span.negate())
    }

    /// Add the given span of time to this datetime. If the sum would overflow
    /// the minimum or maximum datetime values, then the result saturates.
    ///
    /// # Properties
    ///
    /// This routine is _not_ commutative because some additions may
    /// be ambiguous. For example, adding `1 month` to the datetime
    /// `2024-03-31T00:00:00` will produce `2024-04-30T00:00:00` since April
    /// has only 30 days in a month. Moreover, subtracting `1 month` from
    /// `2024-04-30T00:00:00` will produce `2024-03-30T00:00:00`, which is not
    /// the date we started with.
    ///
    /// If spans of time are limited to units of days (or less), then this
    /// routine _is_ commutative.
    ///
    /// # Example
    ///
    /// This shows a few examples of adding spans of time to various dates.
    /// We make use of the [`ToSpan`](crate::ToSpan) trait for convenient
    /// creation of spans.
    ///
    /// ```
    /// use jiff::{civil::DateTime, ToSpan};
    ///
    /// let dt = DateTime::constant(1995, 12, 7, 3, 24, 30, 3_500);
    /// let got = dt.saturating_add(20.years().months(4).nanoseconds(500));
    /// assert_eq!(got, DateTime::constant(2016, 4, 7, 3, 24, 30, 4_000));
    ///
    /// let dt = DateTime::constant(2019, 1, 31, 15, 30, 0, 0);
    /// let got = dt.saturating_add(1.months());
    /// assert_eq!(got, DateTime::constant(2019, 2, 28, 15, 30, 0, 0));
    /// ```
    ///
    /// Negative spans are also supported:
    ///
    /// ```
    /// use jiff::{civil::DateTime, ToSpan};
    ///
    /// let dt = DateTime::constant(2024, 3, 31, 19, 5, 59, 999_999_999);
    /// assert_eq!(
    ///     dt.saturating_add(-1.months()),
    ///     DateTime::constant(2024, 2, 29, 19, 5, 59, 999_999_999),
    /// );
    /// ```
    ///
    /// Exceeding the bounds of `DateTime` in either direction results in
    /// saturation:
    ///
    /// ```
    /// use jiff::{civil::DateTime, ToSpan};
    ///
    /// let dt = DateTime::constant(2024, 3, 31, 13, 13, 13, 13);
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
    /// This routine is _not_ commutative because some additions may
    /// be ambiguous. For example, adding `1 month` to the datetime
    /// `2024-03-31T00:00:00` will produce `2024-04-30T00:00:00` since April
    /// has only 30 days in a month. Moreover, subtracting `1 month` from
    /// `2024-04-30T00:00:00` will produce `2024-03-30T00:00:00`, which is not
    /// the date we started with.
    ///
    /// If spans of time are limited to units of days (or less), then this
    /// routine _is_ commutative.
    ///
    /// # Example
    ///
    /// This shows a few examples of subtracting spans of time to various
    /// dates. We make use of the [`ToSpan`](crate::ToSpan) trait for
    /// convenient creation of spans.
    ///
    /// ```
    /// use jiff::{civil::DateTime, ToSpan};
    ///
    /// let dt = DateTime::constant(1995, 12, 7, 3, 24, 30, 3_500);
    /// let got = dt.saturating_sub(20.years().months(4).nanoseconds(500));
    /// assert_eq!(got, DateTime::constant(1975, 8, 7, 3, 24, 30, 3_000));
    ///
    /// let dt = DateTime::constant(2019, 2, 28, 15, 30, 0, 0);
    /// let got = dt.saturating_sub(1.months());
    /// assert_eq!(got, DateTime::constant(2019, 1, 28, 15, 30, 0, 0));
    /// ```
    ///
    /// Negative spans are also supported:
    ///
    /// ```
    /// use jiff::{civil::DateTime, ToSpan};
    ///
    /// let dt = DateTime::constant(2024, 3, 31, 19, 5, 59, 999_999_999);
    /// assert_eq!(
    ///     dt.saturating_sub(-1.months()),
    ///     DateTime::constant(2024, 4, 30, 19, 5, 59, 999_999_999),
    /// );
    /// ```
    ///
    /// Exceeding the bounds of `DateTime` in either direction results in
    /// saturation:
    ///
    /// ```
    /// use jiff::{civil::DateTime, ToSpan};
    ///
    /// let dt = DateTime::constant(2024, 3, 31, 13, 13, 13, 13);
    /// assert_eq!(DateTime::MIN, dt.saturating_sub(19000.years()));
    /// assert_eq!(DateTime::MAX, dt.saturating_sub(-9000.years()));
    /// ```
    #[inline]
    pub fn saturating_sub(self, span: Span) -> DateTime {
        self.saturating_add(span.negate())
    }

    /// Returns a span representing the elapsed time from this datetime since
    /// the given `other` datetime.
    ///
    /// When `other` occurs after this datetime, then the span returned will be
    /// negative.
    ///
    /// # Properties
    ///
    /// It is guaranteed that if the returned span is added to `other`, then
    /// the original datetime will be returned.
    ///
    /// Note that this guarantee only applies to the span returned. If the
    /// span is rounded, then this property may not hold.
    ///
    /// This property is upheld by the fact that the span returned will always
    /// be in units of days or smaller. To represent the span in other units,
    /// round the span.
    ///
    /// TODO: Show an example of span rounding resulting in the aforementioned
    /// property failing.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::{civil::DateTime, ToSpan};
    ///
    /// let earlier = DateTime::constant(2006, 8, 24, 22, 30, 0, 0);
    /// let later = DateTime::constant(2019, 1, 31, 21, 0, 0, 0);
    /// assert_eq!(later.since(earlier), 4542.days().hours(22).minutes(30));
    ///
    /// // Flipping the dates is fine, but you'll get a negative span.
    /// let earlier = DateTime::constant(2006, 8, 24, 22, 30, 0, 0);
    /// let later = DateTime::constant(2019, 1, 31, 21, 0, 0, 0);
    /// assert_eq!(earlier.since(later), -4542.days().hours(22).minutes(30));
    /// ```
    #[inline]
    pub fn since(self, other: DateTime) -> Span {
        -self.until(other)
    }

    #[inline]
    pub fn since_with_largest_unit(
        self,
        largest: Unit,
        other: DateTime,
    ) -> Result<Span, Error> {
        self.until_with_largest_unit(largest, other).map(|span| -span)
    }

    /// Returns a span representing the elapsed time from this datetime until
    /// the given `other` datetime.
    ///
    /// When `other` occurs before this datetime, then the span returned will
    /// be negative.
    ///
    /// # Properties
    ///
    /// It is guaranteed that if the returned span is subtracted from `other`,
    /// then the original datetime will be returned.
    ///
    /// Note that this guarantee only applies to the span returned. If the
    /// span is rounded, then this property may not hold.
    ///
    /// This property is upheld by the fact that the span returned will always
    /// be in units of days or smaller. To represent the span in other units,
    /// round the span.
    ///
    /// TODO: Show an example of span rounding resulting in the aforementioned
    /// property failing.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::{civil::DateTime, ToSpan};
    ///
    /// let earlier = DateTime::constant(2006, 8, 24, 22, 30, 0, 0);
    /// let later = DateTime::constant(2019, 1, 31, 21, 0, 0, 0);
    /// assert_eq!(earlier.until(later), 4542.days().hours(22).minutes(30));
    ///
    /// // Flipping the dates is fine, but you'll get a negative span.
    /// let earlier = DateTime::constant(2006, 8, 24, 22, 30, 0, 0);
    /// let later = DateTime::constant(2019, 1, 31, 21, 0, 0, 0);
    /// assert_eq!(later.until(earlier), -4542.days().hours(22).minutes(30));
    /// ```
    #[inline]
    pub fn until(self, other: DateTime) -> Span {
        self.until_with_largest_unit(Unit::Day, other)
            .expect("until with day units always succeeds")
    }

    #[inline]
    pub(crate) fn until_with_largest_unit(
        self,
        largest: Unit,
        mut other: DateTime,
    ) -> Result<Span, Error> {
        if largest <= Unit::Day {
            use crate::instant::private::Nanoseconds;

            // We circumvent materializing an Instant here because not all
            // datetimes are guaranteed to be representable as an Instant.
            //
            // FIXME: I think we should just avoid using TimeDuration in
            // Instant and go directly to u128 nanoseconds.
            let nanos1 = datetime_zulu_to_time_duration(self).to_nanoseconds();
            let nanos2 =
                datetime_zulu_to_time_duration(other).to_nanoseconds();
            let diff = nanos2 - nanos1;
            // Note that this can fail! If largest unit is nanoseconds and the
            // datetimes are far enough apart, a single i64 won't be able to
            // represent the time difference.
            //
            // This is only true for nanoseconds. A single i64 in units of
            // microseconds can represent the interval between all valid
            // datetimes. (At time of writing.)
            return Span::from_invariant_nanoseconds(largest, diff);
        }

        let (d1, mut d2) = (self.date(), other.date());
        let (t1, t2) = (self.time(), other.time());
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
        let date_span = d1.until_with_largest_unit(largest, d2);
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

    #[inline]
    pub fn round(self, options: impl Into<Round>) -> DateTime {
        self.try_round(options).expect("invalid round options")
    }

    #[inline]
    pub fn try_round(
        self,
        options: impl Into<Round>,
    ) -> Result<DateTime, Error> {
        options.into().round_datetime(None, self)
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
    /// use jiff::{civil::DateTime, ToSpan};
    ///
    /// let start = DateTime::constant(2023, 7, 15, 16, 30, 0, 0);
    /// let end = start.checked_add(2.days())?;
    /// let mut scan_times = vec![];
    /// for dt in start.series(5.hours()).take_while(|&dt| dt <= end) {
    ///     scan_times.push(dt);
    /// }
    /// assert_eq!(scan_times, vec![
    ///     DateTime::constant(2023, 7, 15, 16, 30, 0, 0),
    ///     DateTime::constant(2023, 7, 15, 21, 30, 0, 0),
    ///     DateTime::constant(2023, 7, 16, 2, 30, 0, 0),
    ///     DateTime::constant(2023, 7, 16, 7, 30, 0, 0),
    ///     DateTime::constant(2023, 7, 16, 12, 30, 0, 0),
    ///     DateTime::constant(2023, 7, 16, 17, 30, 0, 0),
    ///     DateTime::constant(2023, 7, 16, 22, 30, 0, 0),
    ///     DateTime::constant(2023, 7, 17, 3, 30, 0, 0),
    ///     DateTime::constant(2023, 7, 17, 8, 30, 0, 0),
    ///     DateTime::constant(2023, 7, 17, 13, 30, 0, 0),
    /// ]);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn series(self, period: Span) -> DateTimeSeries {
        DateTimeSeries { start: self, period, step: 0 }
    }
}

impl Default for DateTime {
    fn default() -> DateTime {
        DateTime::ZERO
    }
}

impl core::fmt::Display for DateTime {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        use crate::format::{temporal::DateTimePrinter, FmtWrite};

        static P: DateTimePrinter = DateTimePrinter::new();
        // Printing to `f` should never fail.
        Ok(P.print_datetime(self, FmtWrite(f)).unwrap())
    }
}

impl core::fmt::Debug for DateTime {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "{:?}T{:?}", self.date(), self.time())
    }
}

impl<S: TimeScale> From<Instant<S>> for DateTime {
    #[inline]
    fn from(time: Instant<S>) -> DateTime {
        DateTime::from_instant(time)
    }
}

/// Adds a span of time to a datetime.
///
/// This uses checked arithmetic and panics on overflow. To handle overflow
/// without panics, use [`DateTime::checked_add`].
impl Add<Span> for DateTime {
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
impl AddAssign<Span> for DateTime {
    #[inline]
    fn add_assign(&mut self, rhs: Span) {
        *self = self.add(rhs);
    }
}

/// Subtracts a span of time from a datetime.
///
/// This uses checked arithmetic and panics on overflow. To handle overflow
/// without panics, use [`DateTime::checked_sub`].
impl Sub<Span> for DateTime {
    type Output = DateTime;

    #[inline]
    fn sub(self, rhs: Span) -> DateTime {
        self.checked_sub(rhs).expect("subing span to datetime overflowed")
    }
}

/// Subtracts a span of time from a datetime in place.
///
/// This uses checked arithmetic and panics on overflow. To handle overflow
/// without panics, use [`DateTime::checked_sub`].
impl SubAssign<Span> for DateTime {
    #[inline]
    fn sub_assign(&mut self, rhs: Span) {
        *self = self.sub(rhs);
    }
}

/// Computes the span of time between two datetimes.
///
/// This will return a negative span when the datetime being subtracted is
/// greater.
impl Sub for DateTime {
    type Output = Span;

    #[inline]
    fn sub(self, rhs: DateTime) -> Span {
        self.since(rhs)
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

/// An iterator over periodic datetimes.
///
/// This iterator is created by [`DateTime::series`].
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

    fn next(&mut self) -> Option<DateTime> {
        let span = self.period.checked_mul(self.step).ok()?;
        self.step = self.step.checked_add(1)?;
        let date = self.start.checked_add(span).ok()?;
        Some(date)
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        round::{RoundMode, Unit},
        ToSpan,
    };

    use super::*;

    #[test]
    fn from_temporal_docs() {
        let dt = DateTime::from_parts(
            Date::constant(1995, 12, 7),
            Time::constant(3, 24, 30, 000_003_500),
        );

        let got = dt.round(Unit::Hour);
        let expected = DateTime::from_parts(
            Date::constant(1995, 12, 7),
            Time::constant(3, 0, 0, 0),
        );
        assert_eq!(got, expected);

        let got = dt.round(Unit::Minute.increment(30));
        let expected = DateTime::from_parts(
            Date::constant(1995, 12, 7),
            Time::constant(3, 30, 0, 0),
        );
        assert_eq!(got, expected);

        let got = dt.round(Unit::Minute.increment(30).mode(RoundMode::Floor));
        let expected = DateTime::from_parts(
            Date::constant(1995, 12, 7),
            Time::constant(3, 0, 0, 0),
        );
        assert_eq!(got, expected);
    }

    #[test]
    fn since() {
        let later = DateTime::constant(2024, 5, 9, 2, 0, 0, 0);
        let earlier = DateTime::constant(2024, 5, 8, 3, 0, 0, 0);
        assert_eq!(later.since(earlier), 23.hours());

        let later = DateTime::constant(2024, 5, 9, 3, 0, 0, 0);
        let earlier = DateTime::constant(2024, 5, 8, 2, 0, 0, 0);
        assert_eq!(later.since(earlier), 1.days().hours(1));

        let later = DateTime::constant(2024, 5, 9, 2, 0, 0, 0);
        let earlier = DateTime::constant(2024, 5, 10, 3, 0, 0, 0);
        assert_eq!(later.since(earlier), -1.days().hours(1));

        let later = DateTime::constant(2024, 5, 9, 3, 0, 0, 0);
        let earlier = DateTime::constant(2024, 5, 10, 2, 0, 0, 0);
        assert_eq!(later.since(earlier), -23.hours());
    }

    #[test]
    fn until() {
        let a = DateTime::constant(9999, 12, 30, 3, 0, 0, 0);
        let b = DateTime::constant(9999, 12, 31, 2, 0, 0, 0);
        assert_eq!(a.until(b), 23.hours());

        let a = DateTime::constant(-9999, 1, 2, 2, 0, 0, 0);
        let b = DateTime::constant(-9999, 1, 1, 3, 0, 0, 0);
        assert_eq!(a.until(b), -23.hours());

        let a = DateTime::constant(1995, 12, 7, 3, 24, 30, 3500);
        let b = DateTime::constant(2019, 1, 31, 15, 30, 0, 0);
        assert_eq!(
            a.until(b),
            8456.days()
                .hours(12)
                .minutes(5)
                .seconds(29)
                .milliseconds(999)
                .microseconds(996)
                .nanoseconds(500)
        );
        assert_eq!(
            a.until_with_largest_unit(Unit::Year, b).unwrap(),
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
            b.until_with_largest_unit(Unit::Year, a).unwrap(),
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
            a.until_with_largest_unit(Unit::Nanosecond, b).unwrap(),
            730641929999996500i64.nanoseconds(),
        );

        let a = DateTime::constant(-9999, 1, 1, 0, 0, 0, 0);
        let b = DateTime::constant(9999, 12, 31, 23, 59, 59, 999_999_999);
        assert!(a.until_with_largest_unit(Unit::Nanosecond, b).is_err());
        assert_eq!(
            a.until_with_largest_unit(Unit::Microsecond, b).unwrap(),
            Span::new()
                .microseconds_ranged(t::SpanMicroseconds::MAX_SELF - C(1))
                .nanoseconds_ranged(C(999)),
        );
    }

    #[test]
    fn until_month_lengths() {
        let jan1 = DateTime::constant(2020, 1, 1, 0, 0, 0, 0);
        let feb1 = DateTime::constant(2020, 2, 1, 0, 0, 0, 0);
        let mar1 = DateTime::constant(2020, 3, 1, 0, 0, 0, 0);

        assert_eq!(jan1.until(feb1), 31.days());
        assert_eq!(
            jan1.until_with_largest_unit(Unit::Month, feb1).unwrap(),
            1.month()
        );
        assert_eq!(feb1.until(mar1), 29.days());
        assert_eq!(
            feb1.until_with_largest_unit(Unit::Month, mar1).unwrap(),
            1.month()
        );
        assert_eq!(jan1.until(mar1), 60.days());
        assert_eq!(
            jan1.until_with_largest_unit(Unit::Month, mar1).unwrap(),
            2.months()
        );
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
