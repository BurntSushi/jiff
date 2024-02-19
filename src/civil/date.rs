use crate::{
    civil::{DateTime, Era, ISOWeekDate, Time, Weekday},
    error::Error,
    round::Unit,
    span,
    util::{
        common::{
            days_in_month, days_in_month_unranged, is_leap_year,
            saturate_day_in_month,
        },
        rangeint::{ri16, ri8, RFrom, RInto, TryRFrom},
        t::{
            self, Constant, Day, Month, NoUnits, Sign, UnixEpochDays, Year, C,
        },
    },
    Instant, Span, TimeScale,
};

/// A representation of a civil date in the Gregorian calendar.
///
/// A `Date` value corresponds to a triple of year, month and day. Every
/// `Date` value is guaranteed to be a valid Gregorian calendar date. For
/// example, both `2023-02-29` and `2023-11-31` are both invalid and cannot be
/// represented by a `Date`.
///
/// # Civil dates
///
/// A `Date` value behaves without regard to daylight savings time or time
/// zones in general. When doing arithmetic on dates with spans defined in
/// units of time (such as with [`Date::checked_add`]), days are considered to
/// always be precisely `86,400` seconds long.
///
/// # Default value
///
/// For convenience, this type implements the `Default` trait. Its default
/// value corresponds `000-01-01`. One can also access this value via the
/// `Date::ZERO` constant.
///
/// # Rounding
///
/// Rounding dates is currently not supported. If you want this functionality,
/// please participate in the [issue tracking its support][add-date-rounding].
///
/// [add-date-rounding]: https://github.com/BurntSushi/jiff/issues/1
///
/// # Comparisons
///
/// The `Date` type provides both `Eq` and `Ord` trait implementations to
/// facilitate easy comparisons. When a date `d1` occurs before a date `d2`,
/// then `d1 < d2`. For example:
///
/// ```
/// use jiff::civil::Date;
///
/// let d1 = Date::constant(2024, 3, 11);
/// let d2 = Date::constant(2025, 1, 31);
/// assert!(d1 < d2);
/// ```
///
/// # Arithmetic
///
/// This type provides routines for adding and subtracting spans of time, as
/// well as computing the span of time between two `Date` values.
///
/// For adding or subtracting spans of time, one can use any of the following
/// routines:
///
/// * [`Date::checked_add`] or [`Date::checked_sub`] for checked arithmetic.
/// * [`Date::saturating_add`] or [`Date::saturating_sub`] for saturating
/// arithmetic.
///
/// Additionally, checked arithmetic is available via the `Add` and `Sub`
/// trait implementations. When the result overflows, a panic occurs.
///
/// ```
/// use jiff::{civil::Date, ToSpan};
///
/// let start = Date::constant(2024, 2, 25);
/// let one_week_later = start + 1.weeks();
/// assert_eq!(one_week_later, Date::constant(2024, 3, 3));
/// ```
///
/// It is also possible to compute the span of time between two dates using
/// either [`Date::until`] or [`Date::since`]. It's also possible to subtract
/// two `Date` values directly via a `Sub` trait implementation:
///
/// ```
/// use jiff::{civil::Date, ToSpan};
///
/// let date1 = Date::constant(2024, 3, 3);
/// let date2 = Date::constant(2024, 2, 25);
/// assert_eq!(date1 - date2, 7.days());
/// ```
#[derive(Clone, Copy)]
pub struct Date {
    year: Year,
    month: Month,
    day: Day,
}

impl Date {
    /// The minimum representable Gregorian date.
    ///
    /// The minimum is chosen such that any [`Instant`] combined with any
    /// valid time zone offset can be infallibly converted to this type. This
    /// means that the minimum `Instant` is guaranteed to be bigger than the
    /// minimum `Date`.
    pub const MIN: Date = Date::constant(-9999, 1, 1);

    /// The maximum representable Gregorian date.
    ///
    /// The maximum is chosen such that any [`Instant`] combined with any
    /// valid time zone offset can be infallibly converted to this type. This
    /// means that the maximum `Instant` is guaranteed to be smaller than the
    /// maximum `Date`.
    pub const MAX: Date = Date::constant(9999, 12, 31);

    /// The first day of the zeroth year.
    ///
    /// This is guaranteed to be equivalent to `Date::default()`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::Date;
    ///
    /// assert_eq!(Date::ZERO, Date::default());
    /// ```
    pub const ZERO: Date = Date::constant(0, 1, 1);

    /// Creates a new `Date` value from its component year, month and day
    /// values.
    ///
    /// To set the component values of a date after creating it, use one
    /// of the following routines:
    ///
    /// * [`Date::with_year`] creates a new date with the given year.
    /// * [`Date::with_month`] creates a new date with the given month.
    /// * [`Date::with_day`] creates a new date with the given day.
    ///
    /// # Errors
    ///
    /// This returns an error when the given year-month-day does not
    /// correspond to a valid date. Namely, all of the following must be
    /// true:
    ///
    /// * The year must be in the range `-9999..=9999`.
    /// * The month must be in the range `1..=12`.
    /// * The day must be at least `1` and must be at most the number of days
    /// in the corresponding month. So for example, `2024-02-29` is valid but
    /// `2023-02-29` is not.
    ///
    /// # Example
    ///
    /// This shows an example of a valid date:
    ///
    /// ```
    /// use jiff::civil::Date;
    ///
    /// let d = Date::new(2024, 2, 29).unwrap();
    /// assert_eq!(d.year(), 2024);
    /// assert_eq!(d.month(), 2);
    /// assert_eq!(d.day(), 29);
    /// ```
    ///
    /// This shows an example of an invalid date:
    ///
    /// ```
    /// use jiff::civil::Date;
    ///
    /// assert!(Date::new(2023, 2, 29).is_err());
    /// ```
    #[inline]
    pub fn new(year: i16, month: i8, day: i8) -> Result<Date, Error> {
        let year = Year::try_new("year", year)?;
        let month = Month::try_new("month", month)?;
        let day = Day::try_new("day", day)?;
        Date::new_ranged(year, month, day)
    }

    #[inline]
    pub(crate) fn constrain(year: i16, month: i8, day: i8) -> Date {
        let year = Year::constrain(year);
        let month = Month::constrain(month);
        let day = Day::constrain(day);
        Date::constrain_ranged(year, month, day)
    }

    /// Creates a new `Date` value in a `const` context.
    ///
    /// # Panics
    ///
    /// This routine panics when [`Date::new`] would return an error. That is,
    /// when the given year-month-day does not correspond to a valid date.
    /// Namely, all of the following must be true:
    ///
    /// * The year must be in the range `-9999..=9999`.
    /// * The month must be in the range `1..=12`.
    /// * The day must be at least `1` and must be at most the number of days
    /// in the corresponding month. So for example, `2024-02-29` is valid but
    /// `2023-02-29` is not.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::Date;
    ///
    /// let d = Date::constant(2024, 2, 29);
    /// assert_eq!(d.year(), 2024);
    /// assert_eq!(d.month(), 2);
    /// assert_eq!(d.day(), 29);
    /// ```
    #[inline]
    pub const fn constant(year: i16, month: i8, day: i8) -> Date {
        if !Year::contains(year) {
            panic!("invalid year");
        }
        if !Month::contains(month) {
            panic!("invalid month");
        }
        if day > days_in_month_unranged(year, month) {
            panic!("invalid day");
        }
        let year = Year::new_unchecked(year);
        let month = Month::new_unchecked(month);
        let day = Day::new_unchecked(day);
        Date { year, month, day }
    }

    /// Returns the current date.
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
    /// This example shows how to get the first day in the current month:
    ///
    /// ```
    /// use jiff::civil::Date;
    ///
    /// let d = Date::now().first_of_month();
    /// assert_eq!(d.day(), 1);
    /// ```
    #[inline]
    pub fn now() -> Date {
        Date::from(Instant::now())
    }

    /// Converts an instant in time to a Gregorian date.
    ///
    /// This is also available via a `From<Instant>` trait implementation.
    ///
    /// # Example
    ///
    /// This example demonstrates the Unix epoch:
    ///
    /// ```
    /// use jiff::{civil::Date, Instant};
    ///
    /// let instant = Instant::from_unix(0, 0).unwrap();
    /// let date = Date::from_instant(instant);
    /// assert_eq!(date, Date::constant(1970, 1, 1));
    /// ```
    ///
    /// This example shows how negative Unix timestamps are handled:
    ///
    /// ```
    /// use jiff::{civil::Date, Instant};
    ///
    /// let instant = Instant::from_unix(-1, 0).unwrap();
    /// let date = Date::from_instant(instant);
    /// assert_eq!(date, Date::constant(1969, 12, 31));
    /// ```
    #[inline]
    pub fn from_instant<S: TimeScale>(instant: Instant<S>) -> Date {
        instant.to_date()
    }

    /// Construct a Gregorian date from an [ISO 8601 week date].
    ///
    /// The [`ISOWeekDate`] type describes itself in more detail, but in
    /// breif, the ISO week date calendar system eschews months in favor of
    /// weeks.
    ///
    /// The minimum and maximum values of an `ISOWeekDate` correspond
    /// precisely to the minimum and maximum values of a `Date`. Therefore,
    /// converting between them is lossless and infallible.
    ///
    /// This routine is equivalent to [`ISOWeekDate::to_date`]. It is also
    /// available via a `From<ISOWeekDate>` trait implementation for `Date`.
    ///
    /// [ISO 8601 week date]: https://en.wikipedia.org/wiki/ISO_week_date
    ///
    /// # Example
    ///
    /// This shows a number of examples demonstrating the conversion from an
    /// ISO 8601 week date to a Gregorian date.
    ///
    /// ```
    /// use jiff::civil::{Date, ISOWeekDate, Weekday};
    ///
    /// let weekdate = ISOWeekDate::new(1994, 52, Weekday::Sunday).unwrap();
    /// let date = Date::from_iso_week_date(weekdate);
    /// assert_eq!(date, Date::constant(1995, 1, 1));
    ///
    /// let weekdate = ISOWeekDate::new(1997, 1, Weekday::Tuesday).unwrap();
    /// let date = Date::from_iso_week_date(weekdate);
    /// assert_eq!(date, Date::constant(1996, 12, 31));
    ///
    /// let weekdate = ISOWeekDate::new(2020, 1, Weekday::Monday).unwrap();
    /// let date = Date::from_iso_week_date(weekdate);
    /// assert_eq!(date, Date::constant(2019, 12, 30));
    ///
    /// let weekdate = ISOWeekDate::new(2024, 10, Weekday::Saturday).unwrap();
    /// let date = Date::from_iso_week_date(weekdate);
    /// assert_eq!(date, Date::constant(2024, 3, 9));
    ///
    /// let weekdate = ISOWeekDate::new(9999, 52, Weekday::Friday).unwrap();
    /// let date = Date::from_iso_week_date(weekdate);
    /// assert_eq!(date, Date::constant(9999, 12, 31));
    /// ```
    #[inline]
    pub fn from_iso_week_date(weekdate: ISOWeekDate) -> Date {
        let mut days = iso_week_start_from_year(weekdate.year_ranged());
        let year = t::NoUnits16::rfrom(weekdate.year_ranged());
        let week = t::NoUnits16::rfrom(weekdate.week_ranged());
        let weekday = t::NoUnits16::rfrom(
            weekdate.weekday().to_monday_zero_offset_ranged(),
        );
        let [week, weekday] = t::NoUnits16::vary_many(
            [year, week, weekday],
            |[year, week, weekday]| {
                // This is weird, but because the max ISO week date is actually
                // 9999-W52-4, we need to explicitly cap our maximum computed
                // values here. This is only required because the maximums of
                // each component of an ISO week date combine to represent an
                // out-of-bounds Gregorian date.
                //
                // Note that this is purely done at the service of ranged
                // integers. Otherwise, our ranged integers will compute a
                // max value bigger than what can really occur, and then panic.
                // So we use these caps to say, "no range integer, it truly
                // won't exceed 9999-W52-4."
                if year == 9999 {
                    if week >= 52 {
                        [week.min(C(52)), weekday.min(C(4))]
                    } else {
                        [week, weekday]
                    }
                } else {
                    [week, weekday]
                }
            },
        );
        days += (UnixEpochDays::rfrom(week) - C(1)) * C(7);
        days += weekday;
        Date::from_unix_epoch_days(days)
    }

    /// Return a new `Date` value with the year component set to the given
    /// value.
    ///
    /// One can access this value via [`Date::year`].
    ///
    /// # Errors
    ///
    /// This returns an error if the given year is outside the range
    /// `-9999..=9999`. This can also return an error if the resulting date
    /// is otherwise invalid.
    ///
    /// # Example
    ///
    /// This shows how to create a new date with a different year:
    ///
    /// ```
    /// use jiff::civil::Date;
    ///
    /// let d1 = Date::constant(2005, 11, 5);
    /// assert_eq!(d1.year(), 2005);
    /// let d2 = d1.with_year(2007)?;
    /// assert_eq!(d2.year(), 2007);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// This shows how calling this method on a valid date with a valid year
    /// can fail:
    ///
    /// ```
    /// use jiff::civil::Date;
    ///
    /// let d1 = Date::constant(2024, 2, 29);
    /// assert!(d1.with_year(2023).is_err());
    /// ```
    #[inline]
    pub fn with_year(self, year: i16) -> Result<Date, Error> {
        let year = Year::try_new("year", year)?;
        self.with_year_ranged(year)
    }

    /// Return a new `Date` value with the year component set to the given
    /// era year.
    ///
    /// One can access this value via [`Date::era_year`].
    ///
    /// # Errors
    ///
    /// This returns an error if the given year is outside the range for the
    /// era specified. For [`Era::BCE`], the range is `1..=10000`. For
    /// [`Era::CE`], the range is `1..=9999`.
    ///
    /// # Example
    ///
    /// This shows that `CE` years are equivalent to the years used by this
    /// crate:
    ///
    /// ```
    /// use jiff::civil::{Date, Era};
    ///
    /// let d1 = Date::constant(2005, 11, 5);
    /// assert_eq!(d1.year(), 2005);
    /// let d2 = d1.with_era_year(2007, Era::CE)?;
    /// assert_eq!(d2.year(), 2007);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// But `BCE` years always correspond to years less than or equal to `0`
    /// in this crate:
    ///
    /// ```
    /// use jiff::civil::{Date, Era};
    ///
    /// let d1 = Date::constant(-27, 7, 1);
    /// assert_eq!(d1.year(), -27);
    /// assert_eq!(d1.era_year(), (28, Era::BCE));
    ///
    /// let d2 = d1.with_era_year(509, Era::BCE)?;
    /// assert_eq!(d2.year(), -508);
    /// assert_eq!(d2.era_year(), (509, Era::BCE));
    ///
    /// let d2 = d1.with_era_year(10_000, Era::BCE)?;
    /// assert_eq!(d2.year(), -9_999);
    /// assert_eq!(d2.era_year(), (10_000, Era::BCE));
    ///
    /// // BCE years are always positive and can be at most 10000:
    /// assert!(d1.with_era_year(-5, Era::BCE).is_err());
    /// assert!(d1.with_era_year(10_001, Era::BCE).is_err());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn with_era_year(self, year: i16, era: Era) -> Result<Date, Error> {
        match era {
            Era::CE => self.with_year(year),
            Era::BCE => {
                let year = t::YearBCE::try_new("BCE year", year)?;
                self.with_year_ranged(-year + C(1))
            }
        }
    }

    /// Return a new `Date` value with the month component set to the given
    /// value.
    ///
    /// One can access this value via [`Date::month`].
    ///
    /// # Errors
    ///
    /// This returns an error if the given month is outside the range `1..=12`.
    /// This can also return an error if the resulting date is otherwise
    /// invalid.
    ///
    /// # Example
    ///
    /// This shows how to create a new date with a different month:
    ///
    /// ```
    /// use jiff::civil::Date;
    ///
    /// let d1 = Date::constant(2005, 11, 5);
    /// assert_eq!(d1.month(), 11);
    /// let d2 = d1.with_month(6)?;
    /// assert_eq!(d2.month(), 6);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// This shows how calling this method on a valid date with a valid month
    /// can fail:
    ///
    /// ```
    /// use jiff::civil::Date;
    ///
    /// let d1 = Date::constant(2024, 10, 31);
    /// assert!(d1.with_month(11).is_err());
    /// ```
    #[inline]
    pub fn with_month(self, month: i8) -> Result<Date, Error> {
        let month = Month::try_new("month", month)?;
        self.with_month_ranged(month)
    }

    /// Return a new `Date` value with the day component set to the given
    /// value.
    ///
    /// One can access this value via [`Date::day`].
    ///
    /// # Errors
    ///
    /// This returns an error if the given day is outside of allowable days
    /// for the year and month components on this date.
    ///
    /// # Example
    ///
    /// This shows some examples of setting the day, including a leap day:
    ///
    /// ```
    /// use jiff::civil::Date;
    ///
    /// let d1 = Date::constant(2024, 2, 5);
    /// assert_eq!(d1.day(), 5);
    /// let d2 = d1.with_day(10)?;
    /// assert_eq!(d2.day(), 10);
    /// let d3 = d1.with_day(29)?;
    /// assert_eq!(d3.day(), 29);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// This shows some examples that will fail:
    ///
    /// ```
    /// use jiff::civil::Date;
    ///
    /// let d1 = Date::constant(2023, 2, 5);
    /// // 2023 is not a leap year
    /// assert!(d1.with_day(29).is_err());
    ///
    /// // September has 30 days, not 31.
    /// let d1 = Date::constant(2023, 9, 5);
    /// assert!(d1.with_day(31).is_err());
    /// ```
    #[inline]
    pub fn with_day(self, day: i8) -> Result<Date, Error> {
        let day = Day::try_new("day", day)?;
        self.with_day_ranged(day)
    }

    /// Returns the date for the given day-of-year for this date's year.
    ///
    /// The valid values for `day` are `1..=366`. Note though that `366` is
    /// only valid for leap years.
    ///
    /// # Errors
    ///
    /// This returns an error when the given day is outside the allowed range
    /// of `1..=366`, or when a value of `366` is given for a non-leap year.
    ///
    /// # Example
    ///
    /// This demonstrates that if a year is a leap year, then `60` corresponds
    /// to February 29:
    ///
    /// ```
    /// use jiff::civil::Date;
    ///
    /// let d = Date::constant(2024, 1, 1);
    /// assert_eq!(d.with_day_of_year(60)?, Date::constant(2024, 2, 29));
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// But for non-leap years, day 60 is March 1:
    ///
    /// ```
    /// use jiff::civil::Date;
    ///
    /// let d = Date::constant(2023, 1, 1);
    /// assert_eq!(d.with_day_of_year(60)?, Date::constant(2023, 3, 1));
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// And using `366` for a non-leap year will result in an error, since
    /// non-leap years only have 365 days:
    ///
    /// ```
    /// use jiff::civil::Date;
    ///
    /// let d = Date::constant(2023, 1, 1);
    /// assert!(d.with_day_of_year(366).is_err());
    /// // The maximal year is not a leap year, so it returns an error too.
    /// let d = Date::constant(9999, 1, 1);
    /// assert!(d.with_day_of_year(366).is_err());
    /// ```
    #[inline]
    pub fn with_day_of_year(self, day: i16) -> Result<Date, Error> {
        type DayOfYear = ri16<1, 366>;

        let day = DayOfYear::try_new("day-of-year", day)?;
        let end = self
            .first_of_year()
            .checked_add(Span::new().days_ranged(day - C(1)))?;
        // If we overflowed into the next year, then `day` is too big.
        if end.year() != self.year() {
            // This can only happen given day=366 and this is a leap year.
            debug_assert_eq!(day, 366);
            debug_assert!(!self.in_leap_year());
            return Err(Error::signed("day-of-year", day, 1, 365));
        }
        Ok(end)
    }

    /// Returns the date for the given day-of-year for this date's year, but
    /// ignores leap years.
    ///
    /// The valid values for `day` are `1..=365`. The value `365` always
    /// corresponds to the last day of the year, even for leap years. It is
    /// impossible for this routine to return a date corresponding to February
    /// 29.
    ///
    /// # Errors
    ///
    /// This returns an error when the given day is outside the allowed range
    /// of `1..=365`.
    ///
    /// # Example
    ///
    /// This demonstrates that `60` corresponds to March 1, regardless of
    /// whether the year is a leap year or not:
    ///
    /// ```
    /// use jiff::civil::Date;
    ///
    /// let d = Date::constant(2023, 1, 1);
    /// assert_eq!(
    ///     d.with_day_of_year_no_leap(60)?,
    ///     Date::constant(2023, 3, 1),
    /// );
    ///
    /// let d = Date::constant(2024, 1, 1);
    /// assert_eq!(
    ///     d.with_day_of_year_no_leap(60)?,
    ///     Date::constant(2024, 3, 1),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// And using `365` for any year will always yield the last day of the
    /// year:
    ///
    /// ```
    /// use jiff::civil::Date;
    ///
    /// let d = Date::constant(2023, 1, 1);
    /// assert_eq!(d.with_day_of_year_no_leap(365)?, d.last_of_year());
    /// let d = Date::constant(2024, 1, 1);
    /// assert_eq!(d.with_day_of_year_no_leap(365)?, d.last_of_year());
    /// let d = Date::constant(9999, 1, 1);
    /// assert_eq!(d.with_day_of_year_no_leap(365)?, d.last_of_year());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// A value of `366` is out of bounds, even for leap years:
    ///
    /// ```
    /// use jiff::civil::Date;
    ///
    /// let d = Date::constant(2024, 1, 1);
    /// assert!(d.with_day_of_year_no_leap(366).is_err());
    /// ```
    #[inline]
    pub fn with_day_of_year_no_leap(
        self,
        mut day: i16,
    ) -> Result<Date, Error> {
        type DayOfYear = ri16<1, 365>;

        let _ = DayOfYear::try_new("day-of-year", day)?;
        if self.in_leap_year() {
            if day >= 60 {
                day += 1;
            }
        }
        self.with_day_of_year(day)
    }

    /// Returns the year for this date.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::Date;
    ///
    /// let d1 = Date::constant(2024, 3, 9);
    /// assert_eq!(d1.year(), 2024);
    ///
    /// let d2 = Date::constant(-2024, 3, 9);
    /// assert_eq!(d2.year(), -2024);
    ///
    /// let d3 = Date::constant(0, 3, 9);
    /// assert_eq!(d3.year(), 0);
    /// ```
    #[inline]
    pub fn year(self) -> i16 {
        self.year_ranged().get()
    }

    /// Returns the year and its era.
    ///
    /// This crate specifically allows years to be negative or `0`, where as
    /// years written for the Gregorian calendar are always positive and
    /// greater than `0`. In the Gregorian calendar, the era labels `BCE` and
    /// `CE` are used to disambiguate between years less than or equal to `0`
    /// and years greater than `0`, respectively.
    ///
    /// The crate is designed this way do that years in the latest era (that
    /// is, `CE`) are aligned with years in this crate.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::{Date, Era};
    ///
    /// let d = Date::constant(2024, 10, 3);
    /// assert_eq!(d.era_year(), (2024, Era::CE));
    ///
    /// let d = Date::constant(1, 10, 3);
    /// assert_eq!(d.era_year(), (1, Era::CE));
    ///
    /// let d = Date::constant(0, 10, 3);
    /// assert_eq!(d.era_year(), (1, Era::BCE));
    ///
    /// let d = Date::constant(-1, 10, 3);
    /// assert_eq!(d.era_year(), (2, Era::BCE));
    ///
    /// let d = Date::constant(-10, 10, 3);
    /// assert_eq!(d.era_year(), (11, Era::BCE));
    ///
    /// let d = Date::constant(-9_999, 10, 3);
    /// assert_eq!(d.era_year(), (10_000, Era::BCE));
    /// ```
    #[inline]
    pub fn era_year(self) -> (i16, Era) {
        let year = self.year_ranged();
        if year >= 1 {
            (year.get(), Era::CE)
        } else {
            // We specifically ensure our min/max bounds on `Year` always leave
            // room in its representation to add or subtract 1, so this will
            // never fail.
            let year = -t::YearBCE::rfrom(year.min(C(0)));
            let era_year = year + C(1);
            (era_year.get(), Era::BCE)
        }
    }

    /// Returns the month for this date.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::Date;
    ///
    /// let d1 = Date::constant(2024, 3, 9);
    /// assert_eq!(d1.month(), 3);
    /// ```
    #[inline]
    pub fn month(self) -> i8 {
        self.month_ranged().get()
    }

    /// Returns the day for this date.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::Date;
    ///
    /// let d1 = Date::constant(2024, 2, 29);
    /// assert_eq!(d1.day(), 29);
    /// ```
    #[inline]
    pub fn day(self) -> i8 {
        self.day_ranged().get()
    }

    /// Returns the weekday corresponding to this date.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::{Date, Weekday};
    ///
    /// // The Unix epoch was on a Thursday.
    /// let d1 = Date::constant(1970, 1, 1);
    /// assert_eq!(d1.weekday(), Weekday::Thursday);
    /// // One can also get the weekday as an offset in a variety of schemes.
    /// assert_eq!(d1.weekday().to_monday_zero_offset(), 3);
    /// assert_eq!(d1.weekday().to_monday_one_offset(), 4);
    /// assert_eq!(d1.weekday().to_sunday_zero_offset(), 4);
    /// assert_eq!(d1.weekday().to_sunday_one_offset(), 5);
    /// ```
    #[inline]
    pub fn weekday(self) -> Weekday {
        weekday_from_unix_epoch_days(self.to_unix_epoch_days())
    }

    /// Returns the ordinal day of the year that this date resides in.
    ///
    /// For leap years, this always returns a value in the range `1..=366`.
    /// Otherwise, the value is in the range `1..=365`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::Date;
    ///
    /// let d = Date::constant(2006, 8, 24);
    /// assert_eq!(d.day_of_year(), 236);
    ///
    /// let d = Date::constant(2023, 12, 31);
    /// assert_eq!(d.day_of_year(), 365);
    ///
    /// let d = Date::constant(2024, 12, 31);
    /// assert_eq!(d.day_of_year(), 366);
    /// ```
    #[inline]
    pub fn day_of_year(self) -> i16 {
        type DayOfYear = ri16<1, 366>;

        let days = C(1) + self.since_days_ranged(self.first_of_year());
        DayOfYear::rfrom(days).get()
    }

    /// Returns the ordinal day of the year that this date resides in, but
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
    /// use jiff::civil::Date;
    ///
    /// let d = Date::constant(2006, 8, 24);
    /// assert_eq!(d.day_of_year_no_leap(), Some(236));
    ///
    /// let d = Date::constant(2023, 12, 31);
    /// assert_eq!(d.day_of_year_no_leap(), Some(365));
    ///
    /// let d = Date::constant(2024, 12, 31);
    /// assert_eq!(d.day_of_year_no_leap(), Some(365));
    ///
    /// let d = Date::constant(2024, 2, 29);
    /// assert_eq!(d.day_of_year_no_leap(), None);
    /// ```
    #[inline]
    pub fn day_of_year_no_leap(self) -> Option<i16> {
        let mut days = self.day_of_year();
        if self.in_leap_year() {
            // day=60 is Feb 29
            if days == 60 {
                return None;
            } else if days > 60 {
                days -= 1;
            }
        }
        Some(days)
    }

    /// Returns the first date of the month that this date resides in.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::Date;
    ///
    /// let d = Date::constant(2024, 2, 29);
    /// assert_eq!(d.first_of_month(), Date::constant(2024, 2, 1));
    /// ```
    #[inline]
    pub fn first_of_month(self) -> Date {
        Date::new_ranged(self.year_ranged(), self.month_ranged(), C(1))
            .expect("first day of month is always valid")
    }

    /// Returns the last date of the month that this date resides in.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::Date;
    ///
    /// let d = Date::constant(2024, 2, 5);
    /// assert_eq!(d.last_of_month(), Date::constant(2024, 2, 29));
    /// ```
    #[inline]
    pub fn last_of_month(self) -> Date {
        let max_day = self.days_in_month_ranged();
        Date::new_ranged(self.year_ranged(), self.month_ranged(), max_day)
            .expect("last day of month is always valid")
    }

    /// Returns the total number of days in the the month in which this date
    /// resides.
    ///
    /// This is guaranteed to always return one of the following values,
    /// depending on the year and the month: 28, 29, 30 or 31.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::Date;
    ///
    /// let d = Date::constant(2024, 2, 10);
    /// assert_eq!(d.days_in_month(), 29);
    ///
    /// let d = Date::constant(2023, 2, 10);
    /// assert_eq!(d.days_in_month(), 28);
    ///
    /// let d = Date::constant(2024, 8, 15);
    /// assert_eq!(d.days_in_month(), 31);
    /// ```
    #[inline]
    pub fn days_in_month(self) -> i8 {
        self.days_in_month_ranged().get()
    }

    /// Returns the first date of the year that this date resides in.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::Date;
    ///
    /// let d = Date::constant(2024, 2, 29);
    /// assert_eq!(d.first_of_year(), Date::constant(2024, 1, 1));
    /// ```
    #[inline]
    pub fn first_of_year(self) -> Date {
        Date::new_ranged(self.year_ranged(), C(1), C(1))
            .expect("first day of year is always valid")
    }

    /// Returns the last date of the year that this date resides in.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::Date;
    ///
    /// let d = Date::constant(2024, 2, 5);
    /// assert_eq!(d.last_of_year(), Date::constant(2024, 12, 31));
    /// ```
    #[inline]
    pub fn last_of_year(self) -> Date {
        Date::new_ranged(self.year_ranged(), C(12), C(31))
            .expect("last day of year is always valid")
    }

    /// Returns the total number of days in the the year in which this date
    /// resides.
    ///
    /// This is guaranteed to always return either `365` or `366`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::Date;
    ///
    /// let d = Date::constant(2024, 7, 10);
    /// assert_eq!(d.days_in_year(), 366);
    ///
    /// let d = Date::constant(2023, 7, 10);
    /// assert_eq!(d.days_in_year(), 365);
    /// ```
    #[inline]
    pub fn days_in_year(self) -> i16 {
        if self.in_leap_year() {
            366
        } else {
            365
        }
    }

    /// Returns true if and only if the year in which this date resides is a
    /// leap year.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::Date;
    ///
    /// assert!(Date::constant(2024, 1, 1).in_leap_year());
    /// assert!(!Date::constant(2023, 12, 31).in_leap_year());
    /// ```
    #[inline]
    pub fn in_leap_year(self) -> bool {
        is_leap_year(self.year_ranged())
    }

    /// Returns the "nth" weekday from the beginning or end of the month in
    /// which this date resides.
    ///
    /// The `nth` parameter can be positive or negative. A positive value
    /// computes the "nth" weekday from the beginning of the month. A negative
    /// value computes the "nth" weekday from the end of the month. So for
    /// example, use `-1` to "find the last weekday" in this date's month.
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
    /// use jiff::civil::{Date, Weekday};
    ///
    /// let month = Date::constant(2017, 3, 1);
    /// let second_friday = month.nth_weekday_of_month(2, Weekday::Friday)?;
    /// assert_eq!(second_friday, Date::constant(2017, 3, 10));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// This shows how to do the reverse of the above. That is, the nth _last_
    /// weekday in a month:
    ///
    /// ```
    /// use jiff::civil::{Date, Weekday};
    ///
    /// let month = Date::constant(2024, 3, 1);
    /// let last_thursday = month.nth_weekday_of_month(-1, Weekday::Thursday)?;
    /// assert_eq!(last_thursday, Date::constant(2024, 3, 28));
    /// let second_last_thursday = month.nth_weekday_of_month(
    ///     -2,
    ///     Weekday::Thursday,
    /// )?;
    /// assert_eq!(second_last_thursday, Date::constant(2024, 3, 21));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// This routine can return an error if there isn't an `nth` weekday
    /// for this month. For example, March 2024 only has 4 Mondays:
    ///
    /// ```
    /// use jiff::civil::{Date, Weekday};
    ///
    /// let month = Date::constant(2024, 3, 25);
    /// let fourth_monday = month.nth_weekday_of_month(4, Weekday::Monday)?;
    /// assert_eq!(fourth_monday, Date::constant(2024, 3, 25));
    /// // There is no 5th Monday.
    /// assert!(month.nth_weekday_of_month(5, Weekday::Monday).is_err());
    /// // Same goes for counting backwards.
    /// assert!(month.nth_weekday_of_month(-5, Weekday::Monday).is_err());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn nth_weekday_of_month(
        self,
        nth: i8,
        weekday: Weekday,
    ) -> Result<Date, Error> {
        type Nth = ri8<-5, 5>;

        let nth = Nth::try_new("nth", nth)?;
        if nth == 0 {
            Err(Error::specific("nth weekday", 0))
        } else if nth > 0 {
            let nth = nth.max(C(1));
            let first_weekday = self.first_of_month().weekday();
            let diff = weekday.since_ranged(first_weekday);
            let day = Day::rfrom(diff) + C(1) + (nth - C(1)) * C(7);
            self.with_day_ranged(day)
        } else {
            let nth = nth.min(C(-1));
            let last = self.last_of_month();
            let last_weekday = last.weekday();
            let diff = last_weekday.since_ranged(weekday);
            let day = last.day_ranged()
                - Day::rfrom(diff)
                - (nth.abs() - C(1)) * C(7);
            // Our math can go below 1 when nth is -5 and there is no "5th from
            // last" weekday in this month. Since this is outside the bounds
            // of `Day`, we can't let this boundary condition escape. So we
            // check it here.
            if day < 1 {
                return Err(day.to_error_with_bounds(
                    "day",
                    1,
                    self.days_in_month(),
                ));
            }
            self.with_day_ranged(day)
        }
    }

    /// Returns the "nth" weekday from this date, not including itself.
    ///
    /// The `nth` parameter can be positive or negative. A positive value
    /// computes the "nth" weekday starting at the day after this date and
    /// going forwards in time. A negative value computes the "nth" weekday
    /// starting at the day before this date and going backwards in time.
    ///
    /// For example, if this date's weekday is a Sunday and the first Sunday is
    /// asked for (that is, `date.nth_weekday(1, Weekday::Sunday)`), then the
    /// result is a week from this date corresponding to the following Sunday.
    ///
    /// # Errors
    ///
    /// This returns an error when `nth` is `0`, or if it would otherwise result
    /// in a date that overflows the minimum/maximum values of `Date`.
    ///
    /// # Example
    ///
    /// This example shows how to find the "nth" weekday going forwards in
    /// time:
    ///
    /// ```
    /// use jiff::civil::{Date, Weekday};
    ///
    /// // Use a Sunday in March as our start date.
    /// let d = Date::constant(2024, 3, 10);
    /// assert_eq!(d.weekday(), Weekday::Sunday);
    ///
    /// // The first next Monday is tomorrow!
    /// let next_monday = d.nth_weekday(1, Weekday::Monday)?;
    /// assert_eq!(next_monday, Date::constant(2024, 3, 11));
    ///
    /// // But the next Sunday is a week away, because this doesn't
    /// // include the current weekday.
    /// let next_sunday = d.nth_weekday(1, Weekday::Sunday)?;
    /// assert_eq!(next_sunday, Date::constant(2024, 3, 17));
    ///
    /// // "not this Thursday, but next Thursday"
    /// let next_next_thursday = d.nth_weekday(2, Weekday::Thursday)?;
    /// assert_eq!(next_next_thursday, Date::constant(2024, 3, 21));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// This example shows how to find the "nth" weekday going backwards in
    /// time:
    ///
    /// ```
    /// use jiff::civil::{Date, Weekday};
    ///
    /// // Use a Sunday in March as our start date.
    /// let d = Date::constant(2024, 3, 10);
    /// assert_eq!(d.weekday(), Weekday::Sunday);
    ///
    /// // "last Saturday" was yesterday!
    /// let last_saturday = d.nth_weekday(-1, Weekday::Saturday)?;
    /// assert_eq!(last_saturday, Date::constant(2024, 3, 9));
    ///
    /// // "last Sunday" was a week ago.
    /// let last_sunday = d.nth_weekday(-1, Weekday::Sunday)?;
    /// assert_eq!(last_sunday, Date::constant(2024, 3, 3));
    ///
    /// // "not last Thursday, but the one before"
    /// let prev_prev_thursday = d.nth_weekday(-2, Weekday::Thursday)?;
    /// assert_eq!(prev_prev_thursday, Date::constant(2024, 2, 29));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// This example shows that overflow results in an error in either
    /// direction:
    ///
    /// ```
    /// use jiff::civil::{Date, Weekday};
    ///
    /// let d = Date::MAX;
    /// assert_eq!(d.weekday(), Weekday::Friday);
    /// assert!(d.nth_weekday(1, Weekday::Saturday).is_err());
    ///
    /// let d = Date::MIN;
    /// assert_eq!(d.weekday(), Weekday::Monday);
    /// assert!(d.nth_weekday(-1, Weekday::Sunday).is_err());
    /// ```
    ///
    /// # Example: the start of Israeli summer time
    ///
    /// Israeli law says (at present, 2024-03-11) that DST or "summer time"
    /// starts on the Friday before the last Sunday in March. We can find that
    /// date using both `nth_weekday` and [`Date::nth_weekday_of_month`]:
    ///
    /// ```
    /// use jiff::civil::{Date, Weekday};
    ///
    /// let march = Date::constant(2024, 3, 1);
    /// let last_sunday = march.nth_weekday_of_month(-1, Weekday::Sunday)?;
    /// let dst_starts_on = last_sunday.nth_weekday(-1, Weekday::Friday)?;
    /// assert_eq!(dst_starts_on, Date::constant(2024, 3, 29));
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
    /// use jiff::civil::{Date, Weekday};
    ///
    /// let d = Date::constant(2024, 3, 15);
    /// // For weeks starting with Sunday.
    /// let start_of_week = d.tomorrow()?.nth_weekday(-1, Weekday::Sunday)?;
    /// assert_eq!(start_of_week, Date::constant(2024, 3, 10));
    /// // For weeks starting with Monday.
    /// let start_of_week = d.tomorrow()?.nth_weekday(-1, Weekday::Monday)?;
    /// assert_eq!(start_of_week, Date::constant(2024, 3, 11));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// In the above example, we first get the date after the current one
    /// because `nth_weekday` does not consider itself when counting. This
    /// works as expected even at the boundaries of a week:
    ///
    /// ```
    /// use jiff::civil::{Date, Weekday};
    ///
    /// // The start of the week.
    /// let d = Date::constant(2024, 3, 10);
    /// let start_of_week = d.tomorrow()?.nth_weekday(-1, Weekday::Sunday)?;
    /// assert_eq!(start_of_week, Date::constant(2024, 3, 10));
    /// // The end of the week.
    /// let d = Date::constant(2024, 3, 16);
    /// let start_of_week = d.tomorrow()?.nth_weekday(-1, Weekday::Sunday)?;
    /// assert_eq!(start_of_week, Date::constant(2024, 3, 10));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn nth_weekday(
        self,
        nth: i32,
        weekday: Weekday,
    ) -> Result<Date, Error> {
        // ref: http://howardhinnant.github.io/date_algorithms.html#next_weekday

        let nth = t::SpanWeeks::try_new("nth weekday", nth)?;
        if nth == 0 {
            Err(Error::specific("nth weekday", 0))
        } else if nth > 0 {
            let nth = nth.max(C(1));
            let weekday_diff = weekday.since_ranged(self.weekday().next());
            let diff = (nth - C(1)) * C(7) + weekday_diff;
            let start = self.tomorrow()?.to_unix_epoch_days();
            let end = start.try_checked_add("days", diff)?;
            Ok(Date::from_unix_epoch_days(end))
        } else {
            let nth: t::SpanWeeks = nth.min(C(-1)).abs();
            let weekday_diff = self.weekday().previous().since_ranged(weekday);
            let diff = (nth - C(1)) * C(7) + weekday_diff;
            let start = self.yesterday()?.to_unix_epoch_days();
            let end = start.try_checked_sub("days", diff)?;
            Ok(Date::from_unix_epoch_days(end))
        }
    }

    /// Returns the date immediately following this one.
    ///
    /// # Errors
    ///
    /// This returns an error when this date is the maximum value.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::Date;
    ///
    /// let d = Date::constant(2024, 2, 28);
    /// assert_eq!(d.tomorrow()?, Date::constant(2024, 2, 29));
    ///
    /// // The max doesn't have a tomorrow.
    /// assert!(Date::MAX.tomorrow().is_err());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn tomorrow(self) -> Result<Date, Error> {
        let day = self.to_unix_epoch_days();
        let next = day.try_checked_add("days", C(1))?;
        Ok(Date::from_unix_epoch_days(next))
    }

    /// Returns the date immediately preceding this one.
    ///
    /// # Errors
    ///
    /// This returns an error when this date is the minimum value.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::civil::Date;
    ///
    /// let d = Date::constant(2024, 3, 1);
    /// assert_eq!(d.yesterday()?, Date::constant(2024, 2, 29));
    ///
    /// // The min doesn't have a yesterday.
    /// assert!(Date::MIN.yesterday().is_err());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn yesterday(self) -> Result<Date, Error> {
        let day = self.to_unix_epoch_days();
        let next = day.try_checked_sub("days", C(1))?;
        Ok(Date::from_unix_epoch_days(next))
    }

    /// Construct an [ISO 8601 week date] from this Gregorian date.
    ///
    /// The [`ISOWeekDate`] type describes itself in more detail, but in
    /// brief, the ISO week date calendar system eschews months in favor of
    /// weeks.
    ///
    /// The minimum and maximum values of an `ISOWeekDate` correspond
    /// precisely to the minimum and maximum values of a `Date`. Therefore,
    /// converting between them is lossless and infallible.
    ///
    /// This routine is equivalent to [`ISOWeekDate::from_date`].
    ///
    /// [ISO 8601 week date]: https://en.wikipedia.org/wiki/ISO_week_date
    ///
    /// # Example
    ///
    /// This shows a number of examples demonstrating the conversion from an
    /// ISO 8601 week date to a Gregorian date.
    ///
    /// ```
    /// use jiff::civil::{Date, Weekday};
    ///
    /// let weekdate = Date::constant(1995, 1, 1).to_iso_week_date();
    /// assert_eq!(weekdate.year(), 1994);
    /// assert_eq!(weekdate.week(), 52);
    /// assert_eq!(weekdate.weekday(), Weekday::Sunday);
    ///
    /// let weekdate = Date::constant(1996, 12, 31).to_iso_week_date();
    /// assert_eq!(weekdate.year(), 1997);
    /// assert_eq!(weekdate.week(), 1);
    /// assert_eq!(weekdate.weekday(), Weekday::Tuesday);
    ///
    /// let weekdate = Date::constant(2019, 12, 30).to_iso_week_date();
    /// assert_eq!(weekdate.year(), 2020);
    /// assert_eq!(weekdate.week(), 1);
    /// assert_eq!(weekdate.weekday(), Weekday::Monday);
    ///
    /// let weekdate = Date::constant(2024, 3, 9).to_iso_week_date();
    /// assert_eq!(weekdate.year(), 2024);
    /// assert_eq!(weekdate.week(), 10);
    /// assert_eq!(weekdate.weekday(), Weekday::Saturday);
    ///
    /// let weekdate = Date::MIN.to_iso_week_date();
    /// assert_eq!(weekdate.year(), -9999);
    /// assert_eq!(weekdate.week(), 1);
    /// assert_eq!(weekdate.weekday(), Weekday::Monday);
    ///
    /// let weekdate = Date::MAX.to_iso_week_date();
    /// assert_eq!(weekdate.year(), 9999);
    /// assert_eq!(weekdate.week(), 52);
    /// assert_eq!(weekdate.weekday(), Weekday::Friday);
    /// ```
    #[inline]
    pub fn to_iso_week_date(self) -> ISOWeekDate {
        let days = t::NoUnits32::rfrom(self.to_unix_epoch_days());
        let year = t::NoUnits32::rfrom(self.year_ranged());
        let week_start = t::NoUnits32::vary([days, year], |[days, year]| {
            let mut week_start =
                t::NoUnits32::rfrom(iso_week_start_from_year(year));
            if days < week_start {
                week_start =
                    t::NoUnits32::rfrom(iso_week_start_from_year(year - C(1)));
            } else {
                let next_year_week_start =
                    t::NoUnits32::rfrom(iso_week_start_from_year(year + C(1)));
                if days >= next_year_week_start {
                    week_start = next_year_week_start;
                }
            }
            week_start
        });

        let weekday = weekday_from_unix_epoch_days(days);
        let week = ((days - week_start) / C(7)) + C(1);
        let year = Date::from_unix_epoch_days(
            week_start
                + t::NoUnits32::rfrom(
                    Weekday::Thursday.since_ranged(Weekday::Monday),
                ),
        )
        .year_ranged();
        ISOWeekDate::new_ranged(year, week, weekday)
            .expect("all Dates infallibly convert to ISOWeekDates")
    }

    /// Given a [`Time`], this constructs a [`DateTime`] value with its time
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
    /// assert_eq!(DateTime::from_parts(date, time), date.to_datetime(time));
    /// ```
    #[inline]
    pub fn to_datetime(self, time: Time) -> DateTime {
        DateTime::from_parts(self, time)
    }

    /// Add the given span of time to this date. If the sum would overflow the
    /// minimum or maximum date values, then an error is returned.
    ///
    /// # Properties
    ///
    /// This routine is _not_ commutative because some additions may be
    /// ambiguous. For example, adding `1 month` to the date `2024-03-31` will
    /// produce `2024-04-30` since April has only 30 days in a month. Moreover,
    /// subtracting `1 month` from `2024-04-30` will produce `2024-03-30`,
    /// which is not the date we started with.
    ///
    /// If spans of time are limited to units of days (or less), then this
    /// routine _is_ commutative.
    ///
    /// # Errors
    ///
    /// If the span added to this date would result in a date that exceeds the
    /// range of a `Date`, then this will return an error.
    ///
    /// # Examples
    ///
    /// This shows a few examples of adding spans of time to various dates.
    /// We make use of the [`ToSpan`](crate::ToSpan) trait for convenient
    /// creation of spans.
    ///
    /// ```
    /// use jiff::{civil::Date, ToSpan};
    ///
    /// let d = Date::constant(2024, 3, 31);
    /// assert_eq!(d.checked_add(1.months())?, Date::constant(2024, 4, 30));
    /// // Adding two months gives us May 31, not May 30.
    /// let d = Date::constant(2024, 3, 31);
    /// assert_eq!(d.checked_add(2.months())?, Date::constant(2024, 5, 31));
    /// // Any time in the span that does not exceed a day is ignored.
    /// let d = Date::constant(2024, 3, 31);
    /// assert_eq!(d.checked_add(23.hours())?, Date::constant(2024, 3, 31));
    /// // But if the time exceeds a day, that is accounted for!
    /// let d = Date::constant(2024, 3, 31);
    /// assert_eq!(d.checked_add(28.hours())?, Date::constant(2024, 4, 1));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// Negative spans are also supported:
    ///
    /// ```
    /// use jiff::{civil::Date, ToSpan};
    ///
    /// let d = Date::constant(2024, 3, 31);
    /// assert_eq!(
    ///     d.checked_add(-1.months())?,
    ///     Date::constant(2024, 2, 29),
    /// );
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// Exceeding the bounds of `Date` in either direction results in an error:
    ///
    /// ```
    /// use jiff::{civil::Date, ToSpan};
    ///
    /// let d = Date::constant(2024, 3, 31);
    /// assert!(d.checked_add(9000.years()).is_err());
    /// assert!(d.checked_add(-19000.years()).is_err());
    /// ```
    #[inline]
    pub fn checked_add(self, span: Span) -> Result<Date, Error> {
        let (month, years) =
            month_add_overflowing(self.month, span.get_months_ranged());
        let year = self
            .year
            .try_checked_add("years", years)?
            .try_checked_add("years", span.get_years_ranged())?;
        let date = Date::constrain_ranged(year, month, self.day);
        let time_days = span
            .only_lower(Unit::Day)
            .to_invariant_nanoseconds()
            .div_ceil(t::NANOS_PER_CIVIL_DAY);
        let epoch_days = date.to_unix_epoch_days();
        let days = epoch_days
            .try_checked_add(
                "days",
                C(7) * UnixEpochDays::rfrom(span.get_weeks_ranged()),
            )?
            .try_checked_add(
                "days",
                UnixEpochDays::rfrom(span.get_days_ranged()),
            )?
            .try_checked_add("time", time_days)?;
        Ok(Date::from_unix_epoch_days(days))
    }

    /// Subtract the given span of time from this date. If the difference would
    /// overflow the minimum or maximum date values, then an error is returned.
    ///
    /// # Properties
    ///
    /// This routine is _not_ commutative because some additions may be
    /// ambiguous. For example, adding `1 month` to the date `2024-03-31` will
    /// produce `2024-04-30` since April has only 30 days in a month. Moreover,
    /// subtracting `1 month` from `2024-04-30` will produce `2024-03-30`,
    /// which is not the date we started with.
    ///
    /// If spans of time are limited to units of days (or less), then this
    /// routine _is_ commutative.
    ///
    /// # Errors
    ///
    /// If the span subtracted from this date would result in a date that
    /// exceeds the range of a `Date`, then this will return an error.
    ///
    /// # Examples
    ///
    /// This shows a few examples of subtracting spans of time to various
    /// dates. We make use of the [`ToSpan`](crate::ToSpan) trait for
    /// convenient creation of spans.
    ///
    /// ```
    /// use jiff::{civil::Date, ToSpan};
    ///
    /// let d = Date::constant(2024, 3, 31);
    /// assert_eq!(d.checked_sub(1.months())?, Date::constant(2024, 2, 29));
    /// // Adding subtracting two months gives us Jan 31, not Jan 30.
    /// let d = Date::constant(2024, 3, 31);
    /// assert_eq!(d.checked_sub(2.months())?, Date::constant(2024, 1, 31));
    /// // Any time in the span that does not exceed a day is ignored.
    /// let d = Date::constant(2024, 3, 31);
    /// assert_eq!(d.checked_sub(23.hours())?, Date::constant(2024, 3, 31));
    /// // But if the time exceeds a day, that is accounted for!
    /// let d = Date::constant(2024, 3, 31);
    /// assert_eq!(d.checked_sub(28.hours())?, Date::constant(2024, 3, 30));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// Negative spans are also supported:
    ///
    /// ```
    /// use jiff::{civil::Date, ToSpan};
    ///
    /// let d = Date::constant(2024, 3, 31);
    /// assert_eq!(
    ///     d.checked_sub(-1.months())?,
    ///     Date::constant(2024, 4, 30),
    /// );
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// Exceeding the bounds of `Date` in either direction results in an error:
    ///
    /// ```
    /// use jiff::{civil::Date, ToSpan};
    ///
    /// let d = Date::constant(2024, 3, 31);
    /// assert!(d.checked_sub(19000.years()).is_err());
    /// assert!(d.checked_sub(-9000.years()).is_err());
    /// ```
    #[inline]
    pub fn checked_sub(self, span: Span) -> Result<Date, Error> {
        self.checked_add(span.negate())
    }

    /// Add the given span of time to this date. If the sum would overflow the
    /// minimum or maximum date values, then the result saturates.
    ///
    /// # Properties
    ///
    /// This routine is _not_ commutative (even putting aside cases where
    /// saturation occurs) because some additions may be ambiguous. For
    /// example, adding `1 month` to the date `2024-03-31` will produce
    /// `2024-04-30` since April has only 30 days in a month. Moreover,
    /// subtracting `1 month` from `2024-04-30` will produce `2024-03-30`,
    /// which is not the date we started with.
    ///
    /// If spans of time are limited to units of days (or less), then this
    /// routine _is_ commutative.
    ///
    /// # Examples
    ///
    /// This shows a few examples of adding spans of time to various dates.
    /// We make use of the [`ToSpan`](crate::ToSpan) trait for convenient
    /// creation of spans.
    ///
    /// ```
    /// use jiff::{civil::Date, ToSpan};
    ///
    /// let d = Date::constant(2024, 3, 31);
    /// assert_eq!(d.saturating_add(1.months()), Date::constant(2024, 4, 30));
    /// // Adding two months gives us May 31, not May 30.
    /// let d = Date::constant(2024, 3, 31);
    /// assert_eq!(d.saturating_add(2.months()), Date::constant(2024, 5, 31));
    /// // Any time in the span that does not exceed a day is ignored.
    /// let d = Date::constant(2024, 3, 31);
    /// assert_eq!(d.saturating_add(23.hours()), Date::constant(2024, 3, 31));
    /// // But if the time exceeds a day, that is accounted for!
    /// let d = Date::constant(2024, 3, 31);
    /// assert_eq!(d.saturating_add(28.hours()), Date::constant(2024, 4, 1));
    /// ```
    ///
    /// Negative spans are also supported:
    ///
    /// ```
    /// use jiff::{civil::Date, ToSpan};
    ///
    /// let d = Date::constant(2024, 3, 31);
    /// assert_eq!(
    ///     d.saturating_add(-1.months()),
    ///     Date::constant(2024, 2, 29),
    /// );
    /// ```
    ///
    /// Exceeding the bounds of `Date` in either direction results in
    /// saturation:
    ///
    /// ```
    /// use jiff::{civil::Date, ToSpan};
    ///
    /// let d = Date::constant(2024, 3, 31);
    /// assert_eq!(Date::MAX, d.saturating_add(9000.years()));
    /// assert_eq!(Date::MIN, d.saturating_add(-19000.years()));
    /// ```
    #[inline]
    pub fn saturating_add(self, span: Span) -> Date {
        self.checked_add(span).unwrap_or_else(|_| {
            if span.is_negative() {
                Date::MIN
            } else {
                Date::MAX
            }
        })
    }

    /// Subtract the given span of time from this date. If the difference would
    /// overflow the minimum or maximum date values, then the result saturates.
    ///
    /// # Properties
    ///
    /// This routine is _not_ commutative (even putting aside cases where
    /// saturation occurs) because some additions may be ambiguous. For
    /// example, adding `1 month` to the date `2024-03-31` will produce
    /// `2024-04-30` since April has only 30 days in a month. Moreover,
    /// subtracting `1 month` from `2024-04-30` will produce `2024-03-30`,
    /// which is not the date we started with.
    ///
    /// If spans of time are limited to units of days (or less), then this
    /// routine _is_ commutative.
    ///
    /// # Examples
    ///
    /// This shows a few examples of subtracting spans of time to various
    /// dates. We make use of the [`ToSpan`](crate::ToSpan) trait for
    /// convenient creation of spans.
    ///
    /// ```
    /// use jiff::{civil::Date, ToSpan};
    ///
    /// let d = Date::constant(2024, 3, 31);
    /// assert_eq!(d.saturating_sub(1.months()), Date::constant(2024, 2, 29));
    /// // Adding subtracting two months gives us Jan 31, not Jan 30.
    /// let d = Date::constant(2024, 3, 31);
    /// assert_eq!(d.saturating_sub(2.months()), Date::constant(2024, 1, 31));
    /// // Any time in the span that does not exceed a day is ignored.
    /// let d = Date::constant(2024, 3, 31);
    /// assert_eq!(d.saturating_sub(23.hours()), Date::constant(2024, 3, 31));
    /// // But if the time exceeds a day, that is accounted for!
    /// let d = Date::constant(2024, 3, 31);
    /// assert_eq!(d.saturating_sub(28.hours()), Date::constant(2024, 3, 30));
    /// ```
    ///
    /// Negative spans are also supported:
    ///
    /// ```
    /// use jiff::{civil::Date, ToSpan};
    ///
    /// let d = Date::constant(2024, 3, 31);
    /// assert_eq!(
    ///     d.saturating_sub(-1.months()),
    ///     Date::constant(2024, 4, 30),
    /// );
    /// ```
    ///
    /// Exceeding the bounds of `Date` in either direction results in an error:
    ///
    /// ```
    /// use jiff::{civil::Date, ToSpan};
    ///
    /// let d = Date::constant(2024, 3, 31);
    /// assert_eq!(Date::MIN, d.saturating_sub(19000.years()));
    /// assert_eq!(Date::MAX, d.saturating_sub(-9000.years()));
    /// ```
    #[inline]
    pub fn saturating_sub(self, span: Span) -> Date {
        self.saturating_add(span.negate())
    }

    /// Returns a span representing the elapsed time from this date since
    /// the given `other` date.
    ///
    /// When `other` occurs after this date, then the span returned will be
    /// negative.
    ///
    /// # Properties
    ///
    /// It is guaranteed that if the returned span is added to `other`, then
    /// the original date will be returned.
    ///
    /// Note that this guarantee only applies to the span returned. If the
    /// span is rounded, then this property may not hold.
    ///
    /// This property is upheld by the fact that the span returned will always
    /// be in units of days. To represent the span in other units, round the
    /// span.
    ///
    /// TODO: Show an example of span rounding resulting in the aforementioned
    /// property failing.
    ///
    /// # Examples
    ///
    /// ```
    /// use jiff::{civil::Date, ToSpan};
    ///
    /// let earlier = Date::constant(2006, 8, 24);
    /// let later = Date::constant(2019, 1, 31);
    /// assert_eq!(later.since(earlier), 4543.days());
    ///
    /// // Flipping the dates is fine, but you'll get a negative span.
    /// let earlier = Date::constant(2006, 8, 24);
    /// let later = Date::constant(2019, 1, 31);
    /// assert_eq!(earlier.since(later), -4543.days());
    /// ```
    #[inline]
    pub fn since(self, other: Date) -> Span {
        -self.until(other)
    }

    #[inline]
    pub(crate) fn since_with_largest_unit(
        self,
        largest: Unit,
        other: Date,
    ) -> Span {
        -self.until_with_largest_unit(largest, other)
    }

    /// Returns a span representing the elapsed time from this date until
    /// the given `other` date.
    ///
    /// When `other` occurs before this date, then the span returned will be
    /// negative.
    ///
    /// # Properties
    ///
    /// It is guaranteed that if the returned span is subtracted from `other`,
    /// then the original date will be returned.
    ///
    /// Note that this guarantee only applies to the span returned. If the
    /// span is rounded, then this property may not hold.
    ///
    /// This property is upheld by the fact that the span returned will always
    /// be in units of days. To represent the span in other units, round the
    /// span.
    ///
    /// TODO: Show an example of span rounding resulting in the aforementioned
    /// property failing.
    ///
    /// # Examples
    ///
    /// ```
    /// use jiff::{civil::Date, ToSpan};
    ///
    /// let earlier = Date::constant(2006, 8, 24);
    /// let later = Date::constant(2019, 1, 31);
    /// assert_eq!(earlier.until(later), 4543.days());
    ///
    /// // Flipping the dates is fine, but you'll get a negative span.
    /// let earlier = Date::constant(2006, 8, 24);
    /// let later = Date::constant(2019, 1, 31);
    /// assert_eq!(later.until(earlier), -4543.days());
    /// ```
    #[inline]
    pub fn until(self, other: Date) -> Span {
        Span::new().days_ranged(self.until_days_ranged(other))
    }

    #[inline]
    pub(crate) fn until_with_largest_unit(
        self,
        largest: Unit,
        other: Date,
    ) -> Span {
        assert!(largest >= Unit::Day, "must use calendar units");
        if largest <= Unit::Week {
            let mut weeks = t::SpanWeeks::rfrom(C(0));
            let mut days = self.until_days_ranged(other);
            if largest == Unit::Week {
                weeks = days.div_ceil(C(7)).rinto();
                days = days.rem_ceil(C(7));
            }
            return Span::new().weeks_ranged(weeks).days_ranged(days);
        }

        let mut year0 = self.year_ranged();
        let mut month0 = self.month_ranged();
        let mut day0 = self.day_ranged();
        let mut year1 = other.year_ranged();
        let mut month1 = other.month_ranged();
        let mut day1 = other.day_ranged();

        let mut years =
            t::SpanYears::rfrom(year1) - t::SpanYears::rfrom(year0);
        let mut months =
            t::SpanMonths::rfrom(month1) - t::SpanMonths::rfrom(month0);
        let mut days = t::SpanDays::rfrom(day1) - t::SpanMonths::rfrom(day0);
        if years != 0 || months != 0 {
            let sign = if years != 0 {
                Sign::rfrom(years.signum())
            } else {
                Sign::rfrom(months.signum())
            };
            let mut days_in_month1 =
                t::SpanDays::rfrom(days_in_month(year1, month1));
            let mut day_correct = t::SpanDays::N::<0>();
            if days.signum() == -sign {
                let original_days_in_month1 = days_in_month1;
                let (y, m) = month_add_one(year1, month1, -sign).unwrap();
                year1 = y;
                month1 = m;

                years =
                    t::SpanYears::rfrom(year1) - t::SpanYears::rfrom(year0);
                months = t::SpanMonths::rfrom(month1)
                    - t::SpanMonths::rfrom(month0);
                days_in_month1 = days_in_month(year1, month1).rinto();
                day_correct = if sign < 0 {
                    -original_days_in_month1
                } else {
                    days_in_month1
                };
            }

            let day0_trunc = t::SpanDays::rfrom(day0.min(days_in_month1));
            days = t::SpanDays::rfrom(day1) - day0_trunc + day_correct;

            if years != 0 {
                months = t::SpanMonths::rfrom(month1)
                    - t::SpanMonths::rfrom(month0);
                if months.signum() == -sign {
                    let month_correct = if sign < 0 {
                        -t::MONTHS_PER_YEAR
                    } else {
                        t::MONTHS_PER_YEAR
                    };
                    year1 -= sign;
                    years = t::SpanYears::rfrom(year1)
                        - t::SpanYears::rfrom(year0);

                    months = t::SpanMonths::rfrom(month1)
                        - t::SpanMonths::rfrom(month0)
                        + month_correct;
                }
            }
        }
        if largest == Unit::Month && years != 0 {
            months += years * t::MONTHS_PER_YEAR;
            years = C(0).rinto();
        }
        Span::new().years_ranged(years).months_ranged(months).days_ranged(days)
    }

    /// Return an iterator of periodic dates determined by the given span.
    ///
    /// The given span may be negative, in which case, the iterator will move
    /// backwards through time. The iterator won't stop until either the span
    /// itself overflows, or it would otherwise exceed the minimum or maximum
    /// `Date` value.
    ///
    /// # Example: Halloween day of the week
    ///
    /// As a kid, I always hoped for Halloween to fall on a weekend. With this
    /// program, we can print the day of the week for all Halloweens in the
    /// 2020s.
    ///
    /// ```
    /// use jiff::{civil::{Date, Weekday}, ToSpan};
    ///
    /// let start = Date::constant(2020, 10, 31);
    /// let mut halloween_days_of_week = vec![];
    /// for halloween in start.series(1.years()).take(10) {
    ///     halloween_days_of_week.push(
    ///         (halloween.year(), halloween.weekday()),
    ///     );
    /// }
    /// assert_eq!(halloween_days_of_week, vec![
    ///     (2020, Weekday::Saturday),
    ///     (2021, Weekday::Sunday),
    ///     (2022, Weekday::Monday),
    ///     (2023, Weekday::Tuesday),
    ///     (2024, Weekday::Thursday),
    ///     (2025, Weekday::Friday),
    ///     (2026, Weekday::Saturday),
    ///     (2027, Weekday::Sunday),
    ///     (2028, Weekday::Tuesday),
    ///     (2029, Weekday::Wednesday),
    /// ]);
    /// ```
    ///
    /// # Example: how many times do I mow the lawn in a year?
    ///
    /// I mow the lawn about every week and a half from the beginning of May
    /// to the end of October. About how many times will I mow the lawn in
    /// 2024?
    ///
    /// ```
    /// use jiff::{civil::Date, ToSpan};
    ///
    /// let start = Date::constant(2024, 5, 1);
    /// let end = Date::constant(2024, 10, 31);
    /// let mows = start
    ///     .series(1.weeks().days(3).hours(12))
    ///     .take_while(|&d| d <= end)
    ///     .count();
    /// assert_eq!(mows, 18);
    /// ```
    ///
    /// # Example: a period less than a day
    ///
    /// Using a period less than a day works, but since this type exists at the
    /// granularity of a day, some dates may be repeated.
    ///
    /// ```
    /// use jiff::{civil::Date, ToSpan};
    ///
    /// let start = Date::constant(2024, 3, 11);
    /// let every_five_hours: Vec<Date> =
    ///     start.series(15.hours()).take(7).collect();
    /// assert_eq!(every_five_hours, vec![
    ///     Date::constant(2024, 3, 11),
    ///     Date::constant(2024, 3, 11),
    ///     Date::constant(2024, 3, 12),
    ///     Date::constant(2024, 3, 12),
    ///     Date::constant(2024, 3, 13),
    ///     Date::constant(2024, 3, 14),
    ///     Date::constant(2024, 3, 14),
    /// ]);
    /// ```
    ///
    /// # Example: finding the most recent Friday the 13th
    ///
    /// When did the most recent Friday the 13th occur?
    ///
    /// ```
    /// use jiff::{civil::{Date, Weekday}, ToSpan};
    ///
    /// let start = Date::constant(2024, 3, 13);
    /// let mut found = None;
    /// for date in start.series(-1.months()) {
    ///     if date.weekday() == Weekday::Friday {
    ///         found = Some(date);
    ///         break;
    ///     }
    /// }
    /// assert_eq!(found, Some(Date::constant(2023, 10, 13)));
    /// ```
    #[inline]
    pub fn series(self, period: Span) -> DateSeries {
        DateSeries { start: self, period, step: 0 }
    }
}

// Constants used for converting between Gregorian calendar dates and Unix
// epoch days.
//
// See: http://howardhinnant.github.io/date_algorithms.html
const DAYS_IN_ERA: Constant = Constant(146_097);
const DAYS_FROM_0000_01_01_TO_1970_01_01: Constant = Constant(719_468);

/// Internal APIs using ranged integers.
impl Date {
    #[inline]
    pub(crate) fn new_ranged(
        year: impl RInto<Year>,
        month: impl RInto<Month>,
        day: impl RInto<Day>,
    ) -> Result<Date, Error> {
        let (year, month, day) = (year.rinto(), month.rinto(), day.rinto());
        let max_day = days_in_month(year, month);
        if day > max_day {
            return Err(day.to_error_with_bounds("day", 1, max_day));
        }
        Ok(Date { year, month, day })
    }

    #[inline]
    fn constrain_ranged(
        year: impl RInto<Year>,
        month: impl RInto<Month>,
        day: impl RInto<Day>,
    ) -> Date {
        let (year, month, mut day) =
            (year.rinto(), month.rinto(), day.rinto());
        day = saturate_day_in_month(year, month, day);
        Date { year, month, day }
    }

    #[inline]
    pub(crate) fn with_year_ranged(
        mut self,
        year: impl RInto<Year>,
    ) -> Result<Date, Error> {
        Date::new_ranged(year, self.month_ranged(), self.day_ranged())
    }

    #[inline]
    pub(crate) fn with_month_ranged(
        mut self,
        month: impl RInto<Month>,
    ) -> Result<Date, Error> {
        Date::new_ranged(self.year_ranged(), month, self.day_ranged())
    }

    #[inline]
    pub(crate) fn with_day_ranged(
        mut self,
        day: impl RInto<Day>,
    ) -> Result<Date, Error> {
        Date::new_ranged(self.year_ranged(), self.month_ranged(), day)
    }

    #[inline]
    pub(crate) fn year_ranged(self) -> Year {
        self.year
    }

    #[inline]
    pub(crate) fn month_ranged(self) -> Month {
        self.month
    }

    #[inline]
    pub(crate) fn day_ranged(self) -> Day {
        self.day
    }

    #[inline]
    pub(crate) fn days_in_month_ranged(self) -> Day {
        days_in_month(self.year_ranged(), self.month_ranged())
    }

    #[inline]
    pub(crate) fn since_days_ranged(self, other: Date) -> t::SpanDays {
        -self.until_days_ranged(other)
    }

    #[inline]
    pub(crate) fn until_days_ranged(self, other: Date) -> t::SpanDays {
        if self == other {
            return C(0).rinto();
        }
        let start = self.to_unix_epoch_days();
        let end = other.to_unix_epoch_days();
        (end - start).rinto()
    }

    #[inline]
    pub(crate) fn to_unix_epoch_days(self) -> UnixEpochDays {
        // ref: http://howardhinnant.github.io/date_algorithms.html

        let year = UnixEpochDays::rfrom(self.year);
        let month = UnixEpochDays::rfrom(self.month);
        let day = UnixEpochDays::rfrom(self.day);

        let year = UnixEpochDays::vary([month, year], |[month, year]| {
            if month <= 2 {
                year - C(1)
            } else {
                year
            }
        });
        let month = UnixEpochDays::vary([month], |[month]| {
            if month > 2 {
                month - C(3)
            } else {
                month + C(9)
            }
        });
        let era = year / C(400);
        let year_of_era = year % C(400);
        let day_of_year = (C(153) * month + C(2)) / C(5) + day - C(1);
        let day_of_era = year_of_era * C(365) + year_of_era / C(4)
            - year_of_era / C(100)
            + day_of_year;
        let epoch_days = era * DAYS_IN_ERA + day_of_era
            - DAYS_FROM_0000_01_01_TO_1970_01_01;
        epoch_days
    }

    #[inline]
    pub(crate) fn from_unix_epoch_days(
        days: impl RInto<UnixEpochDays>,
    ) -> Date {
        // ref: http://howardhinnant.github.io/date_algorithms.html

        let days = days.rinto();
        let days = days + DAYS_FROM_0000_01_01_TO_1970_01_01;
        let era = days / DAYS_IN_ERA;
        let day_of_era = days % DAYS_IN_ERA;
        let year_of_era = (day_of_era - day_of_era / C(1_460)
            + day_of_era / C(36_524)
            - day_of_era / (DAYS_IN_ERA - C(1)))
            / C(365);
        let year = year_of_era + era * C(400);
        let day_of_year = day_of_era
            - (C(365) * year_of_era + year_of_era / C(4)
                - year_of_era / C(100));
        let month = (day_of_year * C(5) + C(2)) / C(153);
        let day = day_of_year - (C(153) * month + C(2)) / C(5) + C(1);
        let month = UnixEpochDays::vary([month], |[month]| {
            if month < 10 {
                month + C(3)
            } else {
                month - C(9)
            }
        });
        let year = UnixEpochDays::vary([month, year], |[month, year]| {
            if month <= 2 {
                year + C(1)
            } else {
                year
            }
        });

        Date { year: year.rinto(), month: month.rinto(), day: day.rinto() }
    }
}

impl Eq for Date {}

impl PartialEq for Date {
    #[inline]
    fn eq(&self, other: &Date) -> bool {
        // We roll our own PartialEq impl so that we call 'get' on the
        // underlying ranged integer. This forces bugs in boundary conditions
        // to result in panics when 'debug_assertions' is enabled.
        self.day.get() == other.day.get()
            && self.month.get() == other.month.get()
            && self.year.get() == other.year.get()
    }
}

impl Ord for Date {
    #[inline]
    fn cmp(&self, other: &Date) -> core::cmp::Ordering {
        (self.year.get(), self.month.get(), self.day.get()).cmp(&(
            other.year.get(),
            other.month.get(),
            other.day.get(),
        ))
    }
}

impl PartialOrd for Date {
    #[inline]
    fn partial_cmp(&self, other: &Date) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Default for Date {
    fn default() -> Date {
        Date::ZERO
    }
}

impl core::fmt::Display for Date {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        use crate::format::{temporal::DateTimePrinter, FmtWrite};

        static P: DateTimePrinter = DateTimePrinter::new();
        // Printing to `f` should never fail.
        Ok(P.print_date(self, FmtWrite(f)).unwrap())
    }
}

impl core::fmt::Debug for Date {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(
            f,
            "{:04}-{:02}-{:02}",
            self.year_ranged(),
            self.month_ranged(),
            self.day_ranged()
        )
    }
}

impl<S: TimeScale> From<Instant<S>> for Date {
    #[inline]
    fn from(time: Instant<S>) -> Date {
        Date::from_instant(time)
    }
}

impl From<ISOWeekDate> for Date {
    #[inline]
    fn from(weekdate: ISOWeekDate) -> Date {
        Date::from_iso_week_date(weekdate)
    }
}

/// Adds a span of time to a date.
///
/// This uses checked arithmetic and panics on overflow. To handle overflow
/// without panics, use [`Date::checked_add`].
impl core::ops::Add<Span> for Date {
    type Output = Date;

    #[inline]
    fn add(self, rhs: Span) -> Date {
        self.checked_add(rhs).expect("adding span to date overflowed")
    }
}

/// Adds a span of time to a date in place.
///
/// This uses checked arithmetic and panics on overflow. To handle overflow
/// without panics, use [`Date::checked_add`].
impl core::ops::AddAssign<Span> for Date {
    #[inline]
    fn add_assign(&mut self, rhs: Span) {
        *self = *self + rhs;
    }
}

/// Subtracts a span of time from a date.
///
/// This uses checked arithmetic and panics on overflow. To handle overflow
/// without panics, use [`Date::checked_sub`].
impl core::ops::Sub<Span> for Date {
    type Output = Date;

    #[inline]
    fn sub(self, rhs: Span) -> Date {
        self.checked_sub(rhs).expect("subing span to date overflowed")
    }
}

/// Subtracts a span of time from a date in place.
///
/// This uses checked arithmetic and panics on overflow. To handle overflow
/// without panics, use [`Date::checked_sub`].
impl core::ops::SubAssign<Span> for Date {
    #[inline]
    fn sub_assign(&mut self, rhs: Span) {
        *self = *self - rhs;
    }
}

/// Computes the span of time between two dates.
///
/// This will return a negative span when the date being subtracted is greater.
impl core::ops::Sub for Date {
    type Output = Span;

    #[inline]
    fn sub(self, rhs: Date) -> Span {
        self.since(rhs)
    }
}

#[cfg(test)]
impl quickcheck::Arbitrary for Date {
    fn arbitrary(g: &mut quickcheck::Gen) -> Date {
        let year = Year::arbitrary(g);
        let month = Month::arbitrary(g);
        let day = Day::arbitrary(g);
        Date::constrain_ranged(year, month, day)
    }

    fn shrink(&self) -> alloc::boxed::Box<dyn Iterator<Item = Date>> {
        alloc::boxed::Box::new(
            (self.year_ranged(), self.month_ranged(), self.day_ranged())
                .shrink()
                .map(|(year, month, day)| {
                    Date::constrain_ranged(year, month, day)
                }),
        )
    }
}

/// An iterator over periodic dates.
///
/// This iterator is created by [`Date::series`].
///
/// It is exhausted when the next value would exceed a [`Span`] or [`Date`]
/// value.
#[derive(Clone, Debug)]
pub struct DateSeries {
    start: Date,
    period: Span,
    step: i64,
}

impl Iterator for DateSeries {
    type Item = Date;

    fn next(&mut self) -> Option<Date> {
        let span = self.period.checked_mul(self.step).ok()?;
        self.step = self.step.checked_add(1)?;
        let date = self.start.checked_add(span).ok()?;
        Some(date)
    }
}

/// Returns the Unix epoch day corresponding to the first day in the ISO 8601
/// week year given.
///
/// Ref: http://howardhinnant.github.io/date_algorithms.html
fn iso_week_start_from_year(year: impl RInto<t::ISOYear>) -> UnixEpochDays {
    let year = year.rinto();
    // A week's year always corresponds to the Gregorian year in which the
    // Thursday of that week falls. Therefore, Jan 4 is *always* in the first
    // week of any ISO week year.
    let date_in_first_week = Date::new_ranged(year, C(1), C(4))
        .expect("Jan 4 is valid for all valid years");
    // The start of the first week is a Monday, so find the number of days
    // since Monday from a date that we know is in the first ISO week of
    // `year`.
    let diff_from_monday =
        date_in_first_week.weekday().since_ranged(Weekday::Monday);
    date_in_first_week.to_unix_epoch_days() - diff_from_monday
}

/// Returns the weekday for the given number of days since the Unix epoch.
fn weekday_from_unix_epoch_days(days: impl RInto<UnixEpochDays>) -> Weekday {
    // Based on Hinnant's approach here, although we use ISO weekday numbering
    // by default. Basically, this works by using the knowledge that 1970-01-01
    // was a Thursday.
    //
    // Ref: http://howardhinnant.github.io/date_algorithms.html
    let days = days.rinto();
    Weekday::from_monday_zero_offset_ranged((days + C(3)) % C(7))
}

/// Adds or subtracts `sign` from the given `year`/`month`.
///
/// If month overflows in either direction, then the `year` returned is
/// adjusted as appropriate.
fn month_add_one(
    year: impl RInto<Year>,
    month: impl RInto<Month>,
    sign: impl RInto<Sign>,
) -> Result<(Year, Month), Error> {
    let mut year = year.rinto();
    let mut month = month.rinto();
    let delta = sign.rinto();

    month += delta;
    if month < 1 {
        year -= C(1);
        month += t::MONTHS_PER_YEAR;
    } else if month > t::MONTHS_PER_YEAR {
        year += C(1);
        month -= t::MONTHS_PER_YEAR;
    }
    let year = Year::try_rfrom("year", year)?;
    let month = Month::try_rfrom("year", month)?;
    Ok((year, month))
}

/// Adds the given span of months to the `month` given.
///
/// If adding (or subtracting) would result in overflowing the `month` value,
/// then the amount by which it overflowed, in units of years, is returned. For
/// example, adding 14 months to the month `3` (March) will result in returning
/// the month `5` (May) with `1` year of overflow.
fn month_add_overflowing(
    month: impl RInto<t::Month>,
    span: impl RInto<t::SpanMonths>,
) -> (t::Month, t::SpanYears) {
    let month = t::SpanMonths::rfrom(month.rinto());
    let span = span.rinto();
    let total = month - C(1) + span;
    let years = total / C(12);
    let month = (total % C(12)) + C(1);
    (month.rinto(), years.rinto())
}

#[cfg(test)]
mod tests {
    use crate::ToSpan;

    use super::*;

    #[test]
    fn t_from_unix() {
        assert_eq!(
            Date::constant(1970, 1, 1),
            Date::from(Instant::from_unix(0, 0).unwrap()),
        );
        assert_eq!(
            Date::constant(1969, 12, 31),
            Date::from(Instant::from_unix(-1, 0).unwrap()),
        );
        assert_eq!(
            Date::constant(1969, 12, 31),
            Date::from(Instant::from_unix(-86_400, 0).unwrap()),
        );
        assert_eq!(
            Date::constant(1969, 12, 30),
            Date::from(Instant::from_unix(-86_401, 0).unwrap()),
        );
        assert_eq!(
            Date::constant(-9999, 1, 2),
            Date::from(
                Instant::from_unix(t::UnixSeconds::MIN_REPR, 0).unwrap()
            ),
        );
        assert_eq!(
            Date::constant(9999, 12, 30),
            Date::from(
                Instant::from_unix(t::UnixSeconds::MAX_REPR, 0).unwrap()
            ),
        );
    }

    #[test]
    fn all_days_to_date_roundtrip() {
        for rd in UnixEpochDays::MIN_REPR..=UnixEpochDays::MAX_REPR {
            let rd = UnixEpochDays::new(rd).unwrap();
            let date = Date::from_unix_epoch_days(rd);
            let got = date.to_unix_epoch_days();
            assert_eq!(rd, got, "for date {date:?}");
        }
    }

    #[test]
    fn all_date_to_days_roundtrip() {
        use crate::util::common::days_in_month;

        for year in Year::MIN_REPR..=Year::MAX_REPR {
            let year = Year::new(year).unwrap();
            for month in Month::MIN_REPR..=Month::MAX_REPR {
                let month = Month::new(month).unwrap();
                for day in 1..=days_in_month(year, month).get() {
                    let date = Date::constant(year.get(), month.get(), day);
                    let rd = date.to_unix_epoch_days();
                    let got = Date::from_unix_epoch_days(rd);
                    assert_eq!(date, got, "for date {date:?}");
                }
            }
        }
    }

    #[test]
    fn all_date_to_iso_week_date_roundtrip() {
        use crate::util::common::days_in_month;

        // This test is slow enough in debug mode to be worth tweaking a bit.
        // We still want to run it so that we benefit from ranged integer
        // checks, but we just do it for ~1000 years. We do it for at least 400
        // years to capture a single Gregorian cycle, and we also include the
        // upper boundary of years because there is some special cased logic
        // for dealing with that specific boundary condition.
        let year_range = if cfg!(debug_assertions) {
            9000..=9999
        } else {
            Year::MIN_REPR..=Year::MAX_REPR
        };
        for year in year_range {
            let year = Year::new(year).unwrap();
            for month in Month::MIN_REPR..=Month::MAX_REPR {
                let month = Month::new(month).unwrap();
                for day in 1..=days_in_month(year, month).get() {
                    let date = Date::constant(year.get(), month.get(), day);
                    let wd = date.to_iso_week_date();
                    let got = wd.to_date();
                    assert_eq!(
                        date, got,
                        "for date {date:?}, and ISO week date {wd:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn add_constrained() {
        use crate::ToSpan;

        let d1 = Date::constant(2023, 3, 31);
        let d2 = d1.checked_add(1.months().days(1)).unwrap();
        assert_eq!(d2, Date::constant(2023, 5, 1));
    }

    #[test]
    fn since_years() {
        let d1 = Date::constant(2023, 4, 15);
        let d2 = Date::constant(2019, 2, 22);
        let span = d1.since_with_largest_unit(Unit::Year, d2);
        assert_eq!(span, 4.years().months(1).days(21));
        let span = d2.since_with_largest_unit(Unit::Year, d1);
        assert_eq!(span, -4.years().months(1).days(24));

        let d1 = Date::constant(2023, 2, 22);
        let d2 = Date::constant(2019, 4, 15);
        let span = d1.since_with_largest_unit(Unit::Year, d2);
        assert_eq!(span, 3.years().months(10).days(7));
        let span = d2.since_with_largest_unit(Unit::Year, d1);
        assert_eq!(span, -3.years().months(10).days(7));

        let d1 = Date::constant(9999, 12, 31);
        let d2 = Date::constant(-9999, 1, 1);
        let span = d1.since_with_largest_unit(Unit::Year, d2);
        assert_eq!(span, 19998.years().months(11).days(30));
        let span = d2.since_with_largest_unit(Unit::Year, d1);
        assert_eq!(span, -19998.years().months(11).days(30));
    }

    #[test]
    fn since_months() {
        let d1 = Date::constant(2024, 7, 24);
        let d2 = Date::constant(2024, 2, 22);
        let span = d1.since_with_largest_unit(Unit::Month, d2);
        assert_eq!(span, 5.months().days(2));
        let span = d2.since_with_largest_unit(Unit::Month, d1);
        assert_eq!(span, -5.months().days(2));
        assert_eq!(d2, d1.checked_sub(5.months().days(2)).unwrap());
        assert_eq!(d1, d2.checked_sub(-5.months().days(2)).unwrap());

        let d1 = Date::constant(2024, 7, 15);
        let d2 = Date::constant(2024, 2, 22);
        let span = d1.since_with_largest_unit(Unit::Month, d2);
        assert_eq!(span, 4.months().days(22));
        let span = d2.since_with_largest_unit(Unit::Month, d1);
        assert_eq!(span, -4.months().days(23));
        assert_eq!(d2, d1.checked_sub(4.months().days(22)).unwrap());
        assert_eq!(d1, d2.checked_sub(-4.months().days(23)).unwrap());

        let d1 = Date::constant(2023, 4, 15);
        let d2 = Date::constant(2023, 2, 22);
        let span = d1.since_with_largest_unit(Unit::Month, d2);
        assert_eq!(span, 1.month().days(21));
        let span = d2.since_with_largest_unit(Unit::Month, d1);
        assert_eq!(span, -1.month().days(24));
        assert_eq!(d2, d1.checked_sub(1.month().days(21)).unwrap());
        assert_eq!(d1, d2.checked_sub(-1.month().days(24)).unwrap());

        let d1 = Date::constant(2023, 4, 15);
        let d2 = Date::constant(2019, 2, 22);
        let span = d1.since_with_largest_unit(Unit::Month, d2);
        assert_eq!(span, 49.months().days(21));
        let span = d2.since_with_largest_unit(Unit::Month, d1);
        assert_eq!(span, -49.months().days(24));
    }

    #[test]
    fn since_weeks() {
        let d1 = Date::constant(2024, 7, 15);
        let d2 = Date::constant(2024, 6, 22);
        let span = d1.since_with_largest_unit(Unit::Week, d2);
        assert_eq!(span, 3.weeks().days(2));
        let span = d2.since_with_largest_unit(Unit::Week, d1);
        assert_eq!(span, -3.weeks().days(2));
    }

    #[test]
    fn since_days() {
        let d1 = Date::constant(2024, 7, 15);
        let d2 = Date::constant(2024, 2, 22);
        let span = d1.since_with_largest_unit(Unit::Day, d2);
        assert_eq!(span, 144.days());
        let span = d2.since_with_largest_unit(Unit::Day, d1);
        assert_eq!(span, -144.days());
    }

    #[test]
    fn until_month_lengths() {
        let jan1 = Date::constant(2020, 1, 1);
        let feb1 = Date::constant(2020, 2, 1);
        let mar1 = Date::constant(2020, 3, 1);

        assert_eq!(jan1.until(feb1), 31.days());
        assert_eq!(jan1.until_with_largest_unit(Unit::Month, feb1), 1.month());
        assert_eq!(feb1.until(mar1), 29.days());
        assert_eq!(feb1.until_with_largest_unit(Unit::Month, mar1), 1.month());
        assert_eq!(jan1.until(mar1), 60.days());
        assert_eq!(
            jan1.until_with_largest_unit(Unit::Month, mar1),
            2.months()
        );
    }

    // Ref: https://github.com/tc39/proposal-temporal/issues/2845#issuecomment-2121057896
    #[test]
    fn since_until_not_commutative() {
        // Temporal.PlainDate.from("2020-04-30").since("2020-02-29", {largestUnit: "months"})
        // // => P2M
        // Temporal.PlainDate.from("2020-02-29").until("2020-04-30", {largestUnit: "months"})
        // // => P2M1D
        let d1 = Date::constant(2020, 4, 30);
        let d2 = Date::constant(2020, 2, 29);

        let since = d1.since_with_largest_unit(Unit::Month, d2);
        assert_eq!(since, 2.months());

        let until = d2.until_with_largest_unit(Unit::Month, d1);
        assert_eq!(until, 2.months().days(1));
    }

    #[test]
    fn test_month_add() {
        let add =
            |year: i16, month: i8, delta: i8| -> Result<(i16, i8), Error> {
                let year = Year::new(year).unwrap();
                let month = Month::new(month).unwrap();
                let delta = Sign::new(delta).unwrap();
                let (year, month) = month_add_one(year, month, delta)?;
                Ok((year.get(), month.get()))
            };

        assert_eq!(add(2024, 1, 1).unwrap(), (2024, 2));
        assert_eq!(add(2024, 1, -1).unwrap(), (2023, 12));
        assert_eq!(add(2024, 12, 1).unwrap(), (2025, 1));
        assert_eq!(add(9999, 12, -1).unwrap(), (9999, 11));
        assert_eq!(add(-9999, 1, 1).unwrap(), (-9999, 2));

        assert!(add(9999, 12, 1).is_err());
        assert!(add(-9999, 1, -1).is_err());
    }

    #[test]
    fn test_month_add_overflowing() {
        let month_add = |month, span| {
            let month = t::Month::new(month).unwrap();
            let span = t::SpanMonths::new(span).unwrap();
            let (month, years) = month_add_overflowing(month, span);
            (month.get(), years.get())
        };

        assert_eq!((1, 0), month_add(1, 0));
        assert_eq!((12, 0), month_add(1, 11));
        assert_eq!((1, 1), month_add(1, 12));
        assert_eq!((2, 1), month_add(1, 13));
        assert_eq!((9, 1), month_add(1, 20));
        assert_eq!((12, 19998), month_add(12, t::SpanMonths::MAX_REPR));

        assert_eq!((12, -1), month_add(1, -1));
        assert_eq!((11, -1), month_add(1, -2));
        assert_eq!((1, -1), month_add(1, -12));
        assert_eq!((12, -2), month_add(1, -13));
    }

    #[test]
    fn date_size() {
        #[cfg(debug_assertions)]
        {
            assert_eq!(12, core::mem::size_of::<Date>());
        }
        #[cfg(not(debug_assertions))]
        {
            assert_eq!(4, core::mem::size_of::<Date>());
        }
    }

    quickcheck::quickcheck! {
        fn prop_checked_add_then_sub(
            d1: Date,
            span: Span
        ) -> quickcheck::TestResult {
            let Ok(d2) = d1.checked_add(span) else {
                return quickcheck::TestResult::discard();
            };
            let got = d2.checked_sub(span).unwrap();
            quickcheck::TestResult::from_bool(d1 == got)
        }

        fn prop_checked_sub_then_add(
            d1: Date,
            span: Span
        ) -> quickcheck::TestResult {
            let Ok(d2) = d1.checked_sub(span) else {
                return quickcheck::TestResult::discard();
            };
            let got = d2.checked_add(span).unwrap();
            quickcheck::TestResult::from_bool(d1 == got)
        }

        fn prop_since_then_add(d1: Date, d2: Date) -> bool {
            let span = d1.since(d2);
            let got = d2.checked_add(span).unwrap();
            d1 == got
        }

        fn prop_until_then_sub(d1: Date, d2: Date) -> bool {
            let span = d1.until(d2);
            let got = d2.checked_sub(span).unwrap();
            d1 == got
        }
    }
}
