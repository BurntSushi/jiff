use core::ops::{Add, AddAssign, Sub, SubAssign};

use crate::{
    civil::{Date, DateTime},
    error::Error,
    instant::Instant,
    round::{Round, Unit},
    span::{Span, TimeDuration},
    util::{
        rangeint::{RFrom, RInto},
        t::{
            self, CivilDayNanosecond, Hour, Microsecond, Millisecond, Minute,
            Nanosecond, NoUnits, Second, SpanNanoseconds, SubsecNanosecond,
            UtcSecond,
        },
    },
};

// TODO: This type is largely complete. I believe all of its intended
// operations are implemented. The only thing remaining is documenting its
// `round` routines, which I specifically omitted in my first pass because I'm
// unsure of the rounding API at present.

/// A representation of civil "wall clock" time.
///
/// Conceptually, a `Time` value corresponds to the typical hours and minutes
/// that you might see on a clock. This type also contains the second and
/// nanosecond associated with a time.
///
/// # Civil time
///
/// A `Time` value behaves as if it corresponds precisely to a single
/// nanosecond within a day, where all days have `86,400` seconds. That
/// is, any given `Time` value corresponds to a nanosecond in the range
/// `[0, 86399999999999]`, where `0` corresponds to `00:00:00.000000000`
/// ([`Time::MIN`]) and `86399999999999` corresponds to `23:59:59.999999999`
/// ([`Time::MAX`]). Moreover, in civil time, all hours have the same number
/// of minutes, all minutes have the same number of seconds and all seconds
/// have the same number of nanoseconds.
///
/// # Default value
///
/// For convenience, this type implements the `Default` trait. Its default
/// value is midnight. i.e., `00:00:00.000000000`.
///
/// # Leap seconds
///
/// TODO: Re-work this section.
///
/// Since this is a representation of civil time, a `Time` value does not
/// account for leap seconds or timezone transitions (such as DST). If a
/// `Time` value is parsed from a string containing a leap second (for
/// example, `23:59:60`), then the leap second is automatically clamped as
/// if it were `59`. If you need leap second support, you'll need to use a
/// [`Instant`] with the `UTC` scale.
///
/// ```
/// use jiff::civil::Time;
///
/// let t1 = Time::constant(23, 59, 60, 0);
/// assert_eq!(t1.second(), 60);
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
/// It is also possible to compute the span of time between two points using
/// either [`Time::until`] or [`Time::since`]. It's also possible to subtract
/// two `Time` values directly via a `Sub` trait implementation:
///
/// ```
/// use jiff::{civil::Time, ToSpan};
///
/// let time1 = Time::constant(22, 0, 0, 0);
/// let time2 = Time::constant(20, 10, 1, 0);
/// assert_eq!(time1 - time2, 1.hours().minutes(49).seconds(59));
/// ```
///
/// # Rounding
///
/// TODO: Fill out this section once we've settled on a rounding API.
#[derive(Clone, Copy, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct Time {
    hour: Hour,
    minute: Minute,
    second: UtcSecond,
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

    /// Creates a new `Time` value from its component hour, minute and second
    /// values.
    ///
    /// For convenience, this constructor does not accept a fractional
    /// nanosecond component and instead sets the fractional part to `0`. To
    /// set the fractional nanosecond in whole or in part, use one of the
    /// following routines:
    ///
    /// * [`Time::constant`] sets the whole fractional part.
    /// * [`Time::with_subsec_nanosecond`] sets the whole fractional part.
    /// * [`Time::with_millisecond`] sets only the millisecond part.
    /// * [`Time::with_microsecond`] sets only the microsecond part.
    /// * [`Time::with_nanosecond`] sets only the nanosecond part.
    ///
    /// # Errors
    ///
    /// This returns an error unless *all* of the following conditions are
    /// true:
    ///
    /// * `0 <= hour <= 23`
    /// * `0 <= minute <= 59`
    /// * `0 <= second <= 59`
    ///
    /// # Example
    ///
    /// This shows an example of a valid time:
    ///
    /// ```
    /// use jiff::civil::Time;
    ///
    /// let t = Time::new(21, 30, 5).unwrap();
    /// assert_eq!(t.hour(), 21);
    /// assert_eq!(t.minute(), 30);
    /// assert_eq!(t.second(), 5);
    /// ```
    ///
    /// This shows an example of an invalid time:
    ///
    /// ```
    /// use jiff::civil::Time;
    ///
    /// assert!(Time::new(21, 30, 61).is_err());
    /// ```
    #[inline]
    pub fn new(hour: i8, minute: i8, second: i8) -> Result<Time, Error> {
        let hour = Hour::try_new("hour", hour)?;
        let minute = Minute::try_new("minute", minute)?;
        let second = UtcSecond::try_new("second", second)?;
        Ok(Time::new_ranged(hour, minute, second))
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
        if !UtcSecond::contains(second) {
            panic!("invalid second");
        }
        if !SubsecNanosecond::contains(subsec_nanosecond) {
            panic!("invalid nanosecond");
        }
        let hour = Hour::new_unchecked(hour);
        let minute = Minute::new_unchecked(minute);
        let second = UtcSecond::new_unchecked(second);
        let subsec_nanosecond =
            SubsecNanosecond::new_unchecked(subsec_nanosecond);
        Time { hour, minute, second, subsec_nanosecond }
    }

    /// Returns the current time.
    ///
    /// # Panics
    ///
    /// This panics if the system clock is set to a time value outside of the
    /// range `-9999-01-01T00:00:00Z..=9999-12-31T11:59:59.999999999Z`. The
    /// justification here is that it is reasonable to expect the system clock
    /// to be set to a somewhat sane, if imprecise, value.
    ///
    /// If you want to get the current time fallibly, use
    /// [`Instant::now_with_scale`] (where [`Unix`](crate::Unix) is the default
    /// time scale), and then use `Time::from(instant)`.
    ///
    /// # Example
    ///
    /// This example shows how to get the current time, rounded to the nearest
    /// multiple of 5 minutes.
    ///
    /// ```
    /// use jiff::{civil::Time, round::Unit};
    ///
    /// let t = Time::now().round(Unit::Minute.increment(5));
    /// assert_eq!(0, t.minute() % 5);
    /// ```
    #[inline]
    pub fn now() -> Time {
        Time::from(Instant::now())
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

    /// Return a new `Time` value with the hour component set to the given
    /// value.
    ///
    /// One can access this value via [`Time::hour`].
    ///
    /// # Errors
    ///
    /// This returns an error if the given hour is outside the range `0..=23`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::Time;
    ///
    /// let t1 = Time::constant(15, 21, 59, 0);
    /// assert_eq!(t1.hour(), 15);
    /// let t2 = t1.with_hour(3)?;
    /// assert_eq!(t2.hour(), 3);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn with_hour(self, hour: i8) -> Result<Time, Error> {
        let hour = Hour::try_new("hour", hour)?;
        Ok(self.with_hour_ranged(hour))
    }

    /// Return a new `Time` value with the minute component set to the given
    /// value.
    ///
    /// One can access this value via [`Time::minute`].
    ///
    /// # Errors
    ///
    /// This returns an error if the given minute is outside the range
    /// `0..=59`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::Time;
    ///
    /// let t1 = Time::constant(15, 21, 59, 0);
    /// assert_eq!(t1.minute(), 21);
    /// let t2 = t1.with_minute(3)?;
    /// assert_eq!(t2.minute(), 3);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn with_minute(self, minute: i8) -> Result<Time, Error> {
        let minute = Minute::try_new("minute", minute)?;
        Ok(self.with_minute_ranged(minute))
    }

    /// Return a new `Time` value with the second component set to the given
    /// value.
    ///
    /// One can access this value via [`Time::second`].
    ///
    /// Note that since this type represents civil time, this type does
    /// not deal with leap seconds. They are considered out-of-range. Leap
    /// seconds can be handled with the [`Instant`](crate::Instant) or
    /// [`Zoned`](crate::Zoned) types.
    ///
    /// # Errors
    ///
    /// This returns an error if the given second is outside the range
    /// `0..=59`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::Time;
    ///
    /// let t1 = Time::constant(15, 21, 59, 0);
    /// assert_eq!(t1.second(), 59);
    /// let t2 = t1.with_second(3)?;
    /// assert_eq!(t2.second(), 3);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn with_second(self, second: i8) -> Result<Time, Error> {
        let second = UtcSecond::try_new("second", second)?;
        Ok(self.with_second_ranged(second))
    }

    /// Return a new `Time` value with the millisecond component of the
    /// fraction part of its time set to the given value.
    ///
    /// One can access this value via [`Time::millisecond`].
    ///
    /// # Errors
    ///
    /// This returns an error if the given millisecond is outside the range
    /// `0..=999`.
    ///
    /// # Example
    ///
    /// This shows the relationship between [`Time::with_millisecond`] and
    /// [`Time::subsec_nanosecond`]:
    ///
    /// ```
    /// use jiff::civil::Time;
    ///
    /// let t = Time::new(15, 21, 35).unwrap().with_millisecond(123).unwrap();
    /// assert_eq!(t.subsec_nanosecond(), 123_000_000);
    /// ```
    #[inline]
    pub fn with_millisecond(
        mut self,
        millisecond: i16,
    ) -> Result<Time, Error> {
        let millisecond = Millisecond::try_new("millisecond", millisecond)?;
        Ok(self.with_millisecond_ranged(millisecond))
    }

    /// Return a new `Time` value with the microsecond component of the
    /// fraction part of its time set to the given value.
    ///
    /// One can access this value via [`Time::microsecond`].
    ///
    /// # Errors
    ///
    /// This returns an error if the given microsecond is outside the range
    /// `0..=999`.
    ///
    /// # Example
    ///
    /// This shows the relationship between [`Time::with_microsecond`] and
    /// [`Time::subsec_nanosecond`]:
    ///
    /// ```
    /// use jiff::civil::Time;
    ///
    /// let t = Time::new(15, 21, 35).unwrap().with_microsecond(456).unwrap();
    /// assert_eq!(t.subsec_nanosecond(), 456_000);
    /// ```
    #[inline]
    pub fn with_microsecond(
        mut self,
        microsecond: i16,
    ) -> Result<Time, Error> {
        let microsecond = Microsecond::try_new("microsecond", microsecond)?;
        Ok(self.with_microsecond_ranged(microsecond))
    }

    /// Return a new `Time` value with the nanosecond component of the
    /// fraction part of its time set to the given value.
    ///
    /// One can access this value via [`Time::nanosecond`].
    ///
    /// Note that this is distinct from [`Time::with_subsec_nanosecond`]. This
    /// only accepts a value up to (and not including) `1_000` corresponding
    /// to the nanosecond units of this time.
    ///
    /// # Errors
    ///
    /// This returns an error if the given nanosecond is outside the range
    /// `0..=999`.
    ///
    /// # Example
    ///
    /// This shows the relationship between [`Time::with_nanosecond`] and
    /// [`Time::subsec_nanosecond`]:
    ///
    /// ```
    /// use jiff::civil::Time;
    ///
    /// let t = Time::new(15, 21, 35)
    ///     .unwrap()
    ///     .with_millisecond(123)
    ///     .unwrap()
    ///     .with_nanosecond(789)
    ///     .unwrap();
    /// assert_eq!(t.subsec_nanosecond(), 123_000_789);
    /// ```
    #[inline]
    pub fn with_nanosecond(mut self, nanosecond: i16) -> Result<Time, Error> {
        let nanosecond = Nanosecond::try_new("nanosecond", nanosecond)?;
        Ok(self.with_nanosecond_ranged(nanosecond))
    }

    /// Return a new `Time` value with the fractional nanosecond component
    /// set to the given value.
    ///
    /// If you want to access this value on `Time`, then use
    /// [`Time::subsec_nanosecond`].
    ///
    /// # Example
    ///
    /// This shows the relationship between constructing a `Time` value with
    /// routines like `with_subsec_nanosecond` and accessing one part of the
    /// fractional nanoseconds:
    ///
    /// ```
    /// use jiff::civil::Time;
    ///
    /// let t = Time::new(15, 21, 35)
    ///     .unwrap()
    ///     .with_subsec_nanosecond(987_000_000)
    ///     .unwrap();
    /// assert_eq!(t.millisecond(), 987);
    /// ```
    #[inline]
    pub fn with_subsec_nanosecond(
        mut self,
        subsec_nanosecond: i32,
    ) -> Result<Time, Error> {
        let subsec_nanosecond =
            SubsecNanosecond::try_new("subsec_nanosecond", subsec_nanosecond)?;
        Ok(self.with_subsec_nanosecond_ranged(subsec_nanosecond))
    }

    /// If this `Time` value corresponds to a leap second, then this returns a
    /// `Time` value that skips the leap second.
    ///
    /// In other words, this returns the point in time following the leap
    /// second, wrapping around to `00:00:00` if necessary.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::Time;
    ///
    /// let t1 = Time::constant(15, 59, 60, 0);
    /// assert_eq!(t1.skip_leap_second(), Time::constant(16, 0, 0, 0));
    ///
    /// let t1 = Time::constant(23, 59, 60, 0);
    /// assert_eq!(t1.skip_leap_second(), Time::constant(0, 0, 0, 0));
    ///
    /// let t1 = Time::constant(23, 59, 60, 500_000_000);
    /// assert_eq!(t1.skip_leap_second(), Time::constant(0, 0, 0, 500_000_000));
    /// ```
    #[inline]
    pub fn skip_leap_second(self) -> Time {
        if self.is_leap_second() {
            self.wrapping_add(Span::new().seconds(1))
        } else {
            self
        }
    }

    /// If this `Time` value corresponds to a leap second, then this returns a
    /// `Time` value that rewinds to the previous second value.
    ///
    /// In other words, this returns the point in time preceding the leap
    /// second.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::Time;
    ///
    /// let t1 = Time::constant(15, 59, 60, 0);
    /// assert_eq!(t1.rewind_leap_second(), Time::constant(15, 59, 59, 0));
    ///
    /// let t1 = Time::constant(23, 59, 60, 0);
    /// assert_eq!(t1.rewind_leap_second(), Time::constant(23, 59, 59, 0));
    ///
    /// let t1 = Time::constant(23, 59, 60, 500_000_000);
    /// assert_eq!(
    ///     t1.rewind_leap_second(),
    ///     Time::constant(23, 59, 59, 500_000_000),
    /// );
    /// ```
    #[inline]
    pub fn rewind_leap_second(self) -> Time {
        if self.is_leap_second() {
            self.with_second_ranged(UtcSecond::N::<59>())
        } else {
            self
        }
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
        self.utc_second_ranged().get()
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
    /// [`Time::with_subsec_nanosecond`].
    ///
    /// # Example
    ///
    /// This shows the relationship between constructing a `Time` value with
    /// routines like `with_millisecond` and accessing the entire fractional
    /// part as a nanosecond:
    ///
    /// ```
    /// use jiff::civil::Time;
    ///
    /// let t = Time::new(15, 21, 35).unwrap().with_millisecond(987).unwrap();
    /// assert_eq!(t.subsec_nanosecond(), 987_000_000);
    /// ```
    ///
    /// # Example: nanoseconds from an instant in time
    ///
    /// This shows how the fractional nanosecond part of a `Time` value
    /// manifests from a specific instant in time.
    ///
    /// ```
    /// use jiff::{civil, Instant};
    ///
    /// // 1,234 nanoseconds after the Unix epoch.
    /// let t = Instant::from_unix(0, 1_234).unwrap();
    /// let time = t.to_datetime().time();
    /// assert_eq!(time.subsec_nanosecond(), 1_234);
    ///
    /// // 1,234 nanoseconds before the Unix epoch.
    /// let t = Instant::from_unix(0, -1_234).unwrap();
    /// let time = t.to_datetime().time();
    /// // The nanosecond is equal to `1_000_000_000 - 1_234`.
    /// assert_eq!(time.subsec_nanosecond(), 999998766);
    /// // Looking at the other components of the time value might help.
    /// assert_eq!(time.hour(), 23);
    /// assert_eq!(time.minute(), 59);
    /// assert_eq!(time.second(), 59);
    /// ```
    #[inline]
    pub fn subsec_nanosecond(self) -> i32 {
        self.subsec_nanosecond_ranged().get()
    }

    /// Returns true if this `Time` value corresponds to a leap second.
    ///
    /// A leap second occurs when the second value is `60`. Since this is a
    /// representation of civil time, there is no
    /// restriction on what the other components of a `Time` can be. For
    /// example, the most recent leap second (at time of writing) occurred on
    /// `2016-12-31T23:59:60Z`, which corresponds to
    /// `2017-01-01T05:29:60+5:30[Asia/Kolkata]`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::Time;
    ///
    /// let t = Time::constant(23, 59, 60, 0);
    /// assert!(t.is_leap_second());
    ///
    /// let t = Time::constant(23, 59, 60, 123_456_789);
    /// assert!(t.is_leap_second());
    ///
    /// let t = Time::constant(5, 29, 60, 0);
    /// assert!(t.is_leap_second());
    /// ```
    #[inline]
    pub fn is_leap_second(self) -> bool {
        self.second() == 60
    }

    /// Given a [`Date`], this constructs a [`DateTime`] value with its time
    /// component equal to this time.
    ///
    /// This is a convenience function for [`DateTime::from_parts`].
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::{Date, DateTime, Time};
    ///
    /// let date = Date::constant(2010, 3, 14);
    /// let time = Time::constant(2, 30, 0, 0);
    /// assert_eq!(DateTime::from_parts(date, time), time.to_datetime(date));
    /// ```
    #[inline]
    pub fn to_datetime(self, date: Date) -> DateTime {
        DateTime::from_parts(date, self)
    }

    /// Returns the span of time since the other time given from this time.
    ///
    /// When `other` is later than this time, the span returned will be
    /// negative.
    ///
    /// # Properties
    ///
    /// Adding the span returned to the `other` time will always equal this
    /// time.
    ///
    /// # Examples
    ///
    /// This shows how to get the difference in time between two points.
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// let t1 = Time::constant(22, 35, 3, 500_000_000);
    /// let t2 = Time::constant(22, 35, 1, 0);
    /// let span = t1.since(t2);
    /// assert_eq!(span, 2.seconds().milliseconds(500));
    /// ```
    ///
    /// This shows what happens when the `other` time occurs before this one:
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// let t1 = Time::constant(22, 35, 1, 0);
    /// let t2 = Time::constant(22, 35, 3, 500_000_000);
    /// let span = t1.since(t2);
    /// assert_eq!(span, -2.seconds().milliseconds(500));
    /// ```
    #[inline]
    pub fn since(self, other: Time) -> Span {
        -self.until(other)
    }

    /// Returns the span of time from this time value until the other given.
    ///
    /// When `other` is earlier than this time, the span returned will be
    /// negative.
    ///
    /// # Properties
    ///
    /// Adding the span returned to this time will always equal the `other`
    /// time given.
    ///
    /// # Examples
    ///
    /// This shows how to get the difference in time between two points.
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// let t1 = Time::constant(22, 35, 1, 0);
    /// let t2 = Time::constant(22, 35, 3, 500_000_000);
    /// let span = t1.until(t2);
    /// assert_eq!(span, 2.seconds().milliseconds(500));
    /// ```
    ///
    /// This shows what happens when the `other` time occurs before this one:
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// let t1 = Time::constant(22, 35, 3, 500_000_000);
    /// let t2 = Time::constant(22, 35, 1, 0);
    /// let span = t1.until(t2);
    /// assert_eq!(span, -2.seconds().milliseconds(500));
    /// ```
    #[inline]
    pub fn until(self, other: Time) -> Span {
        if self == other {
            return Span::new();
        }
        let start = self.to_civil_nanosecond();
        let end = other.to_civil_nanosecond();
        let span = Span::from_invariant_nanoseconds(Unit::Hour, end - start)
            .expect("difference in civil times is always in bounds");
        span
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
    /// # Examples
    ///
    /// This shows how to add nanoseconds to a time value:
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
    /// This shows how to add a span with multiple different units to a time
    /// value:
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
    /// Adding an empty span is a no-op:
    ///
    /// ```
    /// use jiff::{civil::Time, Span};
    ///
    /// let t = Time::constant(20, 10, 1, 0);
    /// assert_eq!(t, t.wrapping_add(Span::new()));
    /// ```
    ///
    /// If adding the span would overflow the maximum time value, then the time
    /// wraps around to the beginning.
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
        let mut sum = self.to_civil_nanosecond().without_bounds();
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
        Time::from_civil_nanosecond(civil_day_nanosecond)
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
    /// # Examples
    ///
    /// This shows how to subtract nanoseconds from a time value:
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
    /// This shows how to subtract a span with multiple different units from a
    /// time value:
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
    /// Subtracting an empty span is a no-op:
    ///
    /// ```
    /// use jiff::{civil::Time, Span};
    ///
    /// let t = Time::constant(20, 10, 1, 0);
    /// assert_eq!(t, t.wrapping_sub(Span::new()));
    /// ```
    ///
    /// If subtracting the span would overflow the minimum time value, then the
    /// time wraps around to the beginning.
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
    /// This returns an error in two cases:
    ///
    /// 1. When the given span's interval overflows the maximum allowed
    /// duration.
    /// 2. When adding the span to a time value would exceed the maximum
    /// allowed value (`23:59:59.999999999`). This also automatically happens
    /// whenever the given span has any non-zero values for units bigger than
    /// hours.
    ///
    /// # Examples
    ///
    /// This shows how to add nanoseconds to a time value:
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
    /// This shows how to add a span with multiple different units to a time
    /// value:
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
    /// Adding an empty span is a no-op:
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
    /// This example shows one kind of overflow, where the span given has a
    /// non-zero unit that always exceeds the maximum time value:
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// // doesn't matter what our time value is in this example
    /// let t = Time::constant(0, 0, 0, 0);
    /// assert!(t.checked_add(1.days()).is_err());
    /// ```
    ///
    /// And finally, if adding the span would overflow the maximum time value,
    /// then an error is returned.
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// // okay
    /// let t = Time::constant(23, 59, 59, 999_999_998);
    /// assert_eq!(t.with_nanosecond(999)?, t.checked_add(1.nanoseconds())?);
    ///
    /// // not okay
    /// let t = Time::constant(23, 59, 59, 999_999_999);
    /// assert!(t.checked_add(1.nanoseconds()).is_err());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
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
    /// # Examples
    ///
    /// This shows how to subtract nanoseconds from a time value:
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
    /// This shows how to subtract a span with multiple different units from a
    /// time value:
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
    /// Subtracting an empty span is a no-op:
    ///
    /// ```
    /// use jiff::{civil::Time, Span};
    ///
    /// let t = Time::constant(20, 10, 1, 0);
    /// assert_eq!(t, t.checked_sub(Span::new())?);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// This example shows one kind of overflow, where the span given has a
    /// non-zero unit that always exceeds the minimum time value:
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// // doesn't matter what our time value is in this example
    /// let t = Time::constant(23, 59, 59, 999_999_999);
    /// assert!(t.checked_sub(1.days()).is_err());
    /// ```
    ///
    /// And finally, if subtracting the span would overflow the minimum time
    /// value, then an error is returned.
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// // okay
    /// let t = Time::constant(0, 0, 0, 1);
    /// assert_eq!(t.with_nanosecond(0)?, t.checked_sub(1.nanoseconds())?);
    ///
    /// // not okay
    /// let t = Time::constant(0, 0, 0, 0);
    /// assert!(t.checked_sub(1.nanoseconds()).is_err());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn checked_sub(self, span: Span) -> Result<Time, Error> {
        self.checked_add(span.negate())
    }

    /// Add the given span to this time and saturate if the addition would
    /// otherwise overflow.
    ///
    /// # Examples
    ///
    /// This shows how to add nanoseconds to a time value:
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
    /// This shows how to add a span with multiple different units to a time
    /// value:
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
    /// Adding an empty span is a no-op:
    ///
    /// ```
    /// use jiff::{civil::Time, Span};
    ///
    /// let t = Time::constant(20, 10, 1, 0);
    /// assert_eq!(t, t.saturating_add(Span::new()));
    /// ```
    ///
    /// This example shows one kind of overflow, where the span given has a
    /// non-zero unit that always exceeds the maximum time value and thus
    /// results in saturation:
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// // doesn't matter what our time value is in this example
    /// let t = Time::constant(0, 0, 0, 0);
    /// assert_eq!(Time::MAX, t.saturating_add(1.days()));
    /// ```
    ///
    /// And finally, if adding the span would overflow the maximum time value,
    /// then saturation occurs:
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// // no saturation
    /// let t = Time::constant(23, 59, 59, 999_999_998);
    /// assert_eq!(
    ///     t.with_nanosecond(999).unwrap(),
    ///     t.saturating_add(1.nanoseconds()),
    /// );
    ///
    /// // saturates
    /// let t = Time::constant(23, 59, 59, 999_999_999);
    /// assert_eq!(Time::MAX, t.saturating_add(1.nanoseconds()));
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
    /// # Examples
    ///
    /// This shows how to subtract nanoseconds from a time value:
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
    /// This shows how to subtract a span with multiple different units from a
    /// time value:
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
    /// Subtracting an empty span is a no-op:
    ///
    /// ```
    /// use jiff::{civil::Time, Span};
    ///
    /// let t = Time::constant(20, 10, 1, 0);
    /// assert_eq!(t, t.saturating_sub(Span::new()));
    /// ```
    ///
    /// This example shows one kind of overflow, where the span given has a
    /// non-zero unit that always exceeds the minimum time value and thus
    /// results in saturation:
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// // doesn't matter what our time value is in this example
    /// let t = Time::constant(23, 59, 59, 999_999_999);
    /// assert_eq!(Time::MIN, t.saturating_sub(1.days()));
    /// ```
    ///
    /// And finally, if subtracting the span would overflow the minimum time
    /// value, then saturation occurs.
    ///
    /// ```
    /// use jiff::{civil::Time, ToSpan};
    ///
    /// // no saturation
    /// let t = Time::constant(0, 0, 0, 1);
    /// assert_eq!(
    ///     t.with_nanosecond(0).unwrap(),
    ///     t.saturating_sub(1.nanoseconds()),
    /// );
    ///
    /// // saturates
    /// let t = Time::constant(0, 0, 0, 0);
    /// assert_eq!(Time::MIN, t.saturating_sub(1.nanoseconds()));
    /// ```
    #[inline]
    pub fn saturating_sub(self, span: Span) -> Time {
        self.saturating_add(span.negate())
    }

    /// Adds the given span to the this time value, and returns the resulting
    /// time with any overflowing amount in the span returned.
    ///
    /// This isn't part of the public API because it seems a little odd that
    /// this returns a `Result`. In theory it should be infallible, but I don't
    /// think there's any way around that. Namely, if e.g., `span.hours` and
    /// `span.minutes` are their maximal values, then the overflow itself could
    /// overflow. See the `overflowing_add_overflows` unit test. This is all
    /// probably fine and we can probably publish this function as a fallible
    /// routine, but I wasn't 100% certain of it.
    ///
    /// This also returns an error if the span given has any non-zero units
    /// greater than an hour. This might seem a little counter-intuitive since
    /// anything bigger should just be considered as part of the overflow. But
    /// what happens when you do `3am - (1 month 2 hours)`? You'd need a way to
    /// break apart "1 month," which cannot be done without a reference date.
    /// Which, of course, we don't have here.
    ///
    /// So overall this routine is a bit specialized and I'm not sure how
    /// generally useful it is. But it is used in crucial points in other parts
    /// of this crate.
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
        let time_nanos = self.to_civil_nanosecond();
        let sum = span_nanos + time_nanos;
        let days = t::SpanDays::try_new(
            "overflowing-days",
            sum.div_floor(t::NANOS_PER_CIVIL_DAY),
        )?;
        let time_nanos = sum.rem_floor(t::NANOS_PER_CIVIL_DAY);
        let time = Time::from_civil_nanosecond(time_nanos);
        Ok((time, Span::new().days_ranged(days)))
    }

    /// Adds the given span to the this time value, and returns the resulting
    /// time with any overflowing amount in the span returned.
    ///
    /// See `Time::overflowing_add` for why this isn't public.
    #[inline]
    pub(crate) fn overflowing_sub(
        self,
        span: Span,
    ) -> Result<(Time, Span), Error> {
        self.overflowing_add(span.negate())
    }

    #[inline]
    pub fn round(self, options: impl Into<Round>) -> Time {
        self.try_round(options).expect("invalid round options")
    }

    #[inline]
    pub fn try_round(self, options: impl Into<Round>) -> Result<Time, Error> {
        options.into().round_time(self)
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
        second: impl RInto<UtcSecond>,
    ) -> Time {
        let subsec_nanosecond = SubsecNanosecond::MIN_SELF;
        Time {
            hour: hour.rinto(),
            minute: minute.rinto(),
            second: second.rinto(),
            subsec_nanosecond,
        }
    }

    #[inline]
    pub(crate) fn with_hour_ranged(mut self, hour: impl RInto<Hour>) -> Time {
        Time { hour: hour.rinto(), ..self }
    }

    #[inline]
    pub(crate) fn with_minute_ranged(
        mut self,
        minute: impl RInto<Minute>,
    ) -> Time {
        Time { minute: minute.rinto(), ..self }
    }

    #[inline]
    pub(crate) fn with_second_ranged(
        mut self,
        second: impl RInto<UtcSecond>,
    ) -> Time {
        Time { second: second.rinto(), ..self }
    }

    #[inline]
    pub(crate) fn with_millisecond_ranged(
        mut self,
        millisecond: impl RInto<Millisecond>,
    ) -> Time {
        let (_, microsecond, nanosecond) = self.to_subsec_parts_ranged();
        self.with_subsec_parts_ranged(millisecond, microsecond, nanosecond)
    }

    #[inline]
    pub(crate) fn with_microsecond_ranged(
        mut self,
        microsecond: impl RInto<Microsecond>,
    ) -> Time {
        let (millisecond, _, nanosecond) = self.to_subsec_parts_ranged();
        self.with_subsec_parts_ranged(millisecond, microsecond, nanosecond)
    }

    #[inline]
    pub(crate) fn with_nanosecond_ranged(
        mut self,
        nanosecond: impl RInto<Nanosecond>,
    ) -> Time {
        let (millisecond, microsecond, _) = self.to_subsec_parts_ranged();
        self.with_subsec_parts_ranged(millisecond, microsecond, nanosecond)
    }

    /// Set the fractional part given its ranged total number of nanoseconds
    /// (up to 1 second).
    #[inline]
    pub(crate) fn with_subsec_nanosecond_ranged(
        mut self,
        subsec_nanosecond: impl RInto<SubsecNanosecond>,
    ) -> Time {
        Time { subsec_nanosecond: subsec_nanosecond.rinto(), ..self }
    }

    /// Set the fractional parts of this time to the given units via ranged
    /// types.
    #[inline]
    pub(crate) fn with_subsec_parts_ranged(
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
        self.with_subsec_nanosecond_ranged(subsec_nanosecond)
    }

    /// Return the fractional part of this time in its corresponding
    /// ranged millisecond, microsecond and nanosecond units.
    #[inline]
    pub(crate) fn to_subsec_parts_ranged(
        self,
    ) -> (Millisecond, Microsecond, Nanosecond) {
        let mut subsec_nanosecond = self.subsec_nanosecond_ranged();
        let nanosecond = subsec_nanosecond % t::NANOS_PER_MICRO;
        subsec_nanosecond /= t::NANOS_PER_MICRO;
        let microsecond = subsec_nanosecond % t::MICROS_PER_MILLI;
        subsec_nanosecond /= t::MICROS_PER_MILLI;
        let millisecond = subsec_nanosecond;
        (millisecond.rinto(), microsecond.rinto(), nanosecond.rinto())
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
    pub(crate) fn utc_second_ranged(self) -> UtcSecond {
        self.second
    }

    #[inline]
    pub(crate) fn second_ranged(self) -> Second {
        self.utc_second_ranged()
            .clamp(Second::MIN_SELF, Second::MAX_SELF)
            .rinto()
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
        let t1 = t::SpanNanoseconds::rfrom(self.to_civil_nanosecond());
        let t2 = t::SpanNanoseconds::rfrom(other.to_civil_nanosecond());
        t2 - t1
    }

    /// Converts this time value to the number of nanoseconds that has elapsed
    /// since `00:00:00.000000000`.
    ///
    /// The maximum possible value that can be returned represents the time
    /// `23:59:59.999999999`.
    #[inline]
    pub(crate) fn to_civil_nanosecond(&self) -> CivilDayNanosecond {
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
    pub(crate) fn from_civil_nanosecond(
        nanosecond: impl RInto<CivilDayNanosecond>,
    ) -> Time {
        let nanosecond = nanosecond.rinto();
        let hour = nanosecond / t::NANOS_PER_HOUR;
        let minute = (nanosecond % t::NANOS_PER_HOUR) / t::NANOS_PER_MINUTE;
        let second = (nanosecond % t::NANOS_PER_MINUTE) / t::NANOS_PER_SECOND;
        let subsec_nanosecond = nanosecond % t::NANOS_PER_SECOND;
        Time::new_ranged(hour, minute, second)
            .with_subsec_nanosecond_ranged(subsec_nanosecond)
    }
}

impl Default for Time {
    fn default() -> Time {
        Time::midnight()
    }
}

impl core::fmt::Display for Time {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        use crate::format::{temporal::DateTimePrinter, FmtWrite};

        static P: DateTimePrinter = DateTimePrinter::new();
        // Printing to `f` should never fail.
        Ok(P.print_time(self, FmtWrite(f)).unwrap())
    }
}

impl core::fmt::Debug for Time {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        let nanos = self.subsec_nanosecond_ranged();
        if nanos == 0 {
            write!(
                f,
                "{:02}:{:02}:{:02}",
                self.hour_ranged(),
                self.minute_ranged(),
                self.utc_second_ranged()
            )
        } else {
            write!(
                f,
                "{:02}:{:02}:{:02}.{:09}",
                self.hour_ranged(),
                self.minute_ranged(),
                self.utc_second_ranged(),
                nanos
            )
        }
    }
}

/// Adds a span of time. This uses wrapping arithmetic.
///
/// For checked arithmetic, see [`Time::checked_add`].
impl Add<Span> for Time {
    type Output = Time;

    #[inline]
    fn add(self, rhs: Span) -> Time {
        self.wrapping_add(rhs)
    }
}

/// Adds a span of time in place. This uses wrapping arithmetic.
///
/// For checked arithmetic, see [`Time::checked_add`].
impl AddAssign<Span> for Time {
    #[inline]
    fn add_assign(&mut self, rhs: Span) {
        *self = self.add(rhs);
    }
}

/// Subtracts a span of time. This uses wrapping arithmetic.
///
/// For checked arithmetic, see [`Time::checked_sub`].
impl Sub<Span> for Time {
    type Output = Time;

    #[inline]
    fn sub(self, rhs: Span) -> Time {
        self.wrapping_sub(rhs)
    }
}

/// Subtracts a span of time in place. This uses wrapping arithmetic.
///
/// For checked arithmetic, see [`Time::checked_sub`].
impl SubAssign<Span> for Time {
    #[inline]
    fn sub_assign(&mut self, rhs: Span) {
        *self = self.sub(rhs);
    }
}

/// Computes the span of time between two times.
///
/// This will return a negative span when the time being subtracted is greater.
impl Sub for Time {
    type Output = Span;

    #[inline]
    fn sub(self, rhs: Time) -> Span {
        self.since(rhs)
    }
}

impl From<Instant> for Time {
    fn from(instant: Instant) -> Time {
        instant.to_datetime().time()
    }
}

#[cfg(test)]
impl quickcheck::Arbitrary for Time {
    fn arbitrary(g: &mut quickcheck::Gen) -> Time {
        let hour = Hour::arbitrary(g);
        let minute = Minute::arbitrary(g);
        let second = UtcSecond::arbitrary(g);
        let subsec_nanosecond = SubsecNanosecond::arbitrary(g);
        Time::new_ranged(hour, minute, second)
            .with_subsec_nanosecond_ranged(subsec_nanosecond)
    }

    fn shrink(&self) -> alloc::boxed::Box<dyn Iterator<Item = Time>> {
        alloc::boxed::Box::new(
            (
                self.hour_ranged(),
                self.minute_ranged(),
                self.utc_second_ranged(),
                self.subsec_nanosecond_ranged(),
            )
                .shrink()
                .map(
                    |(hour, minute, second, subsec_nanosecond)| {
                        Time::new_ranged(hour, minute, second)
                            .with_subsec_nanosecond_ranged(subsec_nanosecond)
                    },
                ),
        )
    }
}

/// An iterator over periodic times.
///
/// This iterator is created by [`Time::series`].
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

    fn next(&mut self) -> Option<Time> {
        let span = self.period.checked_mul(self.step).ok()?;
        self.step = self.step.checked_add(1)?;
        let time = self.start.checked_add(span).ok()?;
        Some(time)
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
        assert!(Time::new(24, 0, 0).is_err());
        assert!(Time::new(23, 60, 0).is_err());
        assert!(Time::new(23, 59, 61).is_err());
        assert!(Time::new(-1, 0, 0).is_err());
        assert!(Time::new(0, -1, 0).is_err());
        assert!(Time::new(0, 0, -1).is_err());

        assert!(Time::new(0, 0, 0)
            .unwrap()
            .with_subsec_nanosecond(1_000_000_000)
            .is_err());
        assert!(Time::new(0, 0, 0)
            .unwrap()
            .with_subsec_nanosecond(-1)
            .is_err());
        assert!(Time::new(23, 59, 59)
            .unwrap()
            .with_subsec_nanosecond(1_000_000_000)
            .is_err());
        assert!(Time::new(23, 59, 59)
            .unwrap()
            .with_subsec_nanosecond(-1)
            .is_err());
    }

    #[test]
    fn rounding_cross_midnight() {
        use crate::round::{Round, Unit};

        let t1 = Time::constant(23, 59, 59, 999_999_999);

        let t2 = t1.round(Unit::Nanosecond);
        assert_eq!(t2, t1);

        let t2 = t1.round(Unit::Millisecond);
        assert_eq!(t2, Time::constant(0, 0, 0, 0));

        let t2 = t1.round(Unit::Microsecond);
        assert_eq!(t2, Time::constant(0, 0, 0, 0));

        let t2 = t1.round(Unit::Millisecond);
        assert_eq!(t2, Time::constant(0, 0, 0, 0));

        let t2 = t1.round(Unit::Second);
        assert_eq!(t2, Time::constant(0, 0, 0, 0));

        let t2 = t1.round(Unit::Minute);
        assert_eq!(t2, Time::constant(0, 0, 0, 0));

        let t2 = t1.round(Unit::Hour);
        assert_eq!(t2, Time::constant(0, 0, 0, 0));

        let t1 = Time::constant(22, 15, 0, 0);
        assert_eq!(
            Time::constant(22, 30, 0, 0),
            t1.round(Unit::Minute.increment(30))
        );
    }

    quickcheck::quickcheck! {
        fn prop_ordering_same_as_civil_nanosecond(
            civil_nanosecond1: CivilDayNanosecond,
            civil_nanosecond2: CivilDayNanosecond
        ) -> bool {
            let t1 = Time::from_civil_nanosecond(civil_nanosecond1);
            let t2 = Time::from_civil_nanosecond(civil_nanosecond2);
            t1.cmp(&t2) == civil_nanosecond1.cmp(&civil_nanosecond2)
        }

        fn prop_checked_add_then_sub(
            time: Time,
            nano_span: CivilDayNanosecond
        ) -> quickcheck::TestResult {
            let time = time.skip_leap_second();
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
            let time = time.skip_leap_second();
            let span = Span::new().nanoseconds(nano_span.get());
            let sum = time.wrapping_add(span);
            let diff = sum.wrapping_sub(span);
            time == diff
        }

        fn prop_checked_add_equals_wrapping_add(
            time: Time,
            nano_span: CivilDayNanosecond
        ) -> quickcheck::TestResult {
            let time = time.skip_leap_second();
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
            let time = time.skip_leap_second();
            let span = Span::new().nanoseconds(nano_span.get());
            let Ok(diff_checked) = time.checked_sub(span) else {
                return quickcheck::TestResult::discard()
            };
            let diff_wrapped = time.wrapping_sub(span);
            quickcheck::TestResult::from_bool(diff_checked == diff_wrapped)
        }

        fn prop_until_then_add(t1: Time, t2: Time) -> bool {
            let (t1, t2) = (t1.skip_leap_second(), t2.skip_leap_second());
            let span = t1.until(t2);
            t1.checked_add(span).unwrap() == t2
        }

        fn prop_until_then_sub(t1: Time, t2: Time) -> bool {
            let (t1, t2) = (t1.skip_leap_second(), t2.skip_leap_second());
            let span = t1.until(t2);
            t2.checked_sub(span).unwrap() == t1
        }

        fn prop_since_then_add(t1: Time, t2: Time) -> bool {
            let (t1, t2) = (t1.skip_leap_second(), t2.skip_leap_second());
            let span = t1.since(t2);
            t2.checked_add(span).unwrap() == t1
        }

        fn prop_since_then_sub(t1: Time, t2: Time) -> bool {
            let (t1, t2) = (t1.skip_leap_second(), t2.skip_leap_second());
            let span = t1.since(t2);
            t1.checked_sub(span).unwrap() == t2
        }

        fn prop_until_is_since_negated(t1: Time, t2: Time) -> bool {
            let (t1, t2) = (t1.skip_leap_second(), t2.skip_leap_second());
            t1.until(t2).get_nanoseconds()
                == t1.since(t2).negate().get_nanoseconds()
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
    fn overflowing_sub() {
        let t1 = Time::constant(4, 30, 0, 0);
        let (t2, span) = t1.overflowing_sub(5.hours()).unwrap();
        assert_eq!(t2, Time::constant(23, 30, 0, 0));
        assert_eq!(span, -1.days());
    }

    #[test]
    fn overflowing_sub_overflows() {
        let t1 = Time::constant(23, 30, 0, 0);
        let span = Span::new()
            .hours(t::SpanHours::MAX_REPR)
            .minutes(t::SpanMinutes::MAX_REPR)
            .seconds(t::SpanSeconds::MAX_REPR)
            .milliseconds(t::SpanMilliseconds::MAX_REPR)
            .microseconds(t::SpanMicroseconds::MAX_REPR)
            .nanoseconds(t::SpanNanoseconds::MAX_REPR);
        assert!(t1.overflowing_sub(span).is_err());
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
