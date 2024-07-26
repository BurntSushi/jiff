use core::{cmp::Ordering, time::Duration};

use alloc::borrow::Cow;

use crate::{
    civil::{Date, DateTime, Time},
    error::{err, Error, ErrorContext},
    fmt::temporal::{DEFAULT_SPAN_PARSER, DEFAULT_SPAN_PRINTER},
    tz::TimeZone,
    util::{
        rangeint::{ri64, ri8, RFrom, RInto, TryRFrom, TryRInto},
        round::increment,
        t::{self, Constant, NoUnits, NoUnits128, Sign, C},
    },
    RoundMode, Timestamp, Zoned,
};

/// A span of time represented via a mixture of calendar and clock units.
///
/// A span represents a duration of time in units of years, months, weeks,
/// days, hours, minutes, seconds, milliseconds, microseconds and nanoseconds.
/// Spans are used to as inputs to routines like
/// [`Zoned::checked_add`] and [`Date::saturating_sub`],
/// and are also outputs from routines like
/// [`Timestamp::since`] and [`DateTime::until`].
///
/// # Range of spans
///
/// Except for nanoseconds, each unit can represent the full span of time
/// expressible via any combination of datetime supported by Jiff. For example:
///
/// ```
/// use jiff::{civil::{DateTime, DateTimeDifference}, ToSpan, Unit};
///
/// let options = DateTimeDifference::new(DateTime::MAX).largest(Unit::Year);
/// assert_eq!(DateTime::MIN.until(options)?.get_years(), 19_998);
///
/// let options = options.largest(Unit::Day);
/// assert_eq!(DateTime::MIN.until(options)?.get_days(), 7_304_483);
///
/// let options = options.largest(Unit::Microsecond);
/// assert_eq!(
///     DateTime::MIN.until(options)?.get_microseconds(),
///     631_107_417_599_999_999i64,
/// );
///
/// let options = options.largest(Unit::Nanosecond);
/// // Span is too big, overflow!
/// assert!(DateTime::MIN.until(options).is_err());
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Building spans
///
/// A default or empty span corresponds to a duration of zero time:
///
/// ```
/// use jiff::Span;
///
/// assert!(Span::new().is_zero());
/// assert!(Span::default().is_zero());
/// ```
///
/// Spans are `Copy` types that have mutator methods on them for creating new
/// spans:
///
/// ```
/// use jiff::Span;
///
/// let span = Span::new().days(5).hours(8).minutes(1);
/// assert_eq!(span.to_string(), "P5dT8h1m");
/// ```
///
/// But Jiff provides a [`ToSpan`] trait that defines extension methods on
/// primitive signed integers to make span creation terser:
///
/// ```
/// use jiff::ToSpan;
///
/// let span = 5.days().hours(8).minutes(1);
/// assert_eq!(span.to_string(), "P5dT8h1m");
/// // singular units on integers can be used too:
/// let span = 1.day().hours(8).minutes(1);
/// assert_eq!(span.to_string(), "P1dT8h1m");
/// ```
///
/// # Negative spans
///
/// A span may be negative. All of these are equivalent:
///
/// ```
/// use jiff::{Span, ToSpan};
///
/// let span = -Span::new().days(5);
/// assert_eq!(span.to_string(), "-P5d");
///
/// let span = Span::new().days(5).negate();
/// assert_eq!(span.to_string(), "-P5d");
///
/// let span = Span::new().days(-5);
/// assert_eq!(span.to_string(), "-P5d");
///
/// let span = -Span::new().days(-5).negate();
/// assert_eq!(span.to_string(), "-P5d");
///
/// let span = -5.days();
/// assert_eq!(span.to_string(), "-P5d");
///
/// let span = (-5).days();
/// assert_eq!(span.to_string(), "-P5d");
///
/// let span = -(5.days());
/// assert_eq!(span.to_string(), "-P5d");
/// ```
///
/// The sign of a span applies to the entire span. When a span is negative,
/// then all of its units are negative:
///
/// ```
/// use jiff::ToSpan;
///
/// let span = -5.days().hours(10).minutes(1);
/// assert_eq!(span.get_days(), -5);
/// assert_eq!(span.get_hours(), -10);
/// assert_eq!(span.get_minutes(), -1);
/// ```
///
/// And if any of a span's units are negative, then the entire span is regarded
/// as negative:
///
/// ```
/// use jiff::ToSpan;
///
/// // It's the same thing.
/// let span = (-5).days().hours(-10).minutes(-1);
/// assert_eq!(span.get_days(), -5);
/// assert_eq!(span.get_hours(), -10);
/// assert_eq!(span.get_minutes(), -1);
///
/// // Still the same. All negative.
/// let span = 5.days().hours(-10).minutes(1);
/// assert_eq!(span.get_days(), -5);
/// assert_eq!(span.get_hours(), -10);
/// assert_eq!(span.get_minutes(), -1);
///
/// // But this is not! The negation in front applies
/// // to the entire span, which was already negative
/// // by virtue of at least one of its units being
/// // negative. So the negation operator in front turns
/// // the span positive.
/// let span = -5.days().hours(-10).minutes(-1);
/// assert_eq!(span.get_days(), 5);
/// assert_eq!(span.get_hours(), 10);
/// assert_eq!(span.get_minutes(), 1);
/// ```
///
/// You can also ask for the absolute value of a span:
///
/// ```
/// use jiff::Span;
///
/// let span = Span::new().days(5).hours(10).minutes(1).negate().abs();
/// assert_eq!(span.get_days(), 5);
/// assert_eq!(span.get_hours(), 10);
/// assert_eq!(span.get_minutes(), 1);
/// ```
///
/// # Parsing and printing
///
/// The `Span` type provides convenient trait implementations of
/// [`std::str::FromStr`] and [`std::fmt::Display`]:
///
/// ```
/// use jiff::Span;
///
/// let span: Span = "P2M10DT2H30M".parse()?;
/// assert_eq!(span.to_string(), "P2m10dT2h30m");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// The format supported is a variation (nearly a subset) of the duration
/// format specified in [ISO 8601]. Here are more examples:
///
/// ```
/// use jiff::{Span, ToSpan};
///
/// let spans = [
///     ("P40D", 40.days()),
///     ("P1y1d", 1.year().days(1)),
///     ("P3dT4h59m", 3.days().hours(4).minutes(59)),
///     ("PT2H30M", 2.hours().minutes(30)),
///     ("P1m", 1.month()),
///     ("P1w", 1.week()),
///     ("P1w4d", 1.week().days(4)),
///     ("PT1m", 1.minute()),
///     ("PT0.0021s", 2.milliseconds().microseconds(100)),
///     ("PT0s", 0.seconds()),
///     ("P0d", 0.seconds()),
///     (
///         "P1y1m1dT1h1m1.1s",
///         1.year().months(1).days(1).hours(1).minutes(1).seconds(1).milliseconds(100),
///     ),
/// ];
/// for (string, span) in spans {
///     let parsed: Span = string.parse()?;
///     assert_eq!(span, parsed, "result of parsing {string:?}");
/// }
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// For more details, see the [`fmt::temporal`](crate::fmt::temporal) module.
///
/// [ISO 8601]: https://www.iso.org/iso-8601-date-and-time-format.html
///
/// # Comparisons
///
/// A `Span` implements the `PartialEq` and `Eq` traits, but not the
/// `PartialOrd` or `Ord` traits. In particular, its `Eq` trait implementation
/// compares for field-wise equality only. This means two spans can represent
/// identical durations while comparing inequal:
///
/// ```
/// use jiff::ToSpan;
///
/// assert_ne!(1.hour(), 60.minutes());
/// ```
///
/// This is because doing true comparisons is an operation that requires
/// arithmetic and a relative datetime in the general case, and which can fail
/// due to overflow. But this operation is provided via [`Span::compare`]:
///
/// ```
/// use jiff::ToSpan;
///
/// assert_eq!(1.hour().compare(60.minutes())?, std::cmp::Ordering::Equal);
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Arithmetic
///
/// Spans can be added or subtracted via [`Span::checked_add`] and
/// [`Span::checked_sub`]:
///
/// ```
/// use jiff::{Span, ToSpan};
///
/// let span1 = 2.hours().minutes(20);
/// let span2: Span = "PT89400s".parse()?;
/// assert_eq!(span1.checked_add(span2)?, 27.hours().minutes(10));
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// When your spans involve calendar units, a relative datetime must be
/// provided. (Because, for example, 1 month from March 1 is 31 days, but
/// 1 month from April 1 is 30 days.)
///
/// ```
/// use jiff::{civil::date, Span, ToSpan};
///
/// let span1 = 2.years().months(6).days(20);
/// let span2 = 400.days();
/// assert_eq!(
///     span1.checked_add((span2, date(2023, 1, 1)))?,
///     3.years().months(7).days(24),
/// );
/// // The span changes when a leap year isn't included!
/// assert_eq!(
///     span1.checked_add((span2, date(2025, 1, 1)))?,
///     3.years().months(7).days(23),
/// );
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Rounding and balancing
///
/// Unlike datetimes, multiple distinct `Span` values can actually correspond
/// to the same duration of time. For example, all of the following correspond
/// to the same duration:
///
/// * 2 hours, 30 minutes
/// * 150 minutes
/// * 1 hour, 90 minutes
///
/// The first is said to be balanced. That is, its biggest non-zero unit cannot
/// be expressed in an integer number of units bigger than hours. But the
/// second is unbalanced because 150 minutes can be split up into hours and
/// minutes. We call this sort of span a "top-heavy" unbalanced span. The third
/// span is also unbalanced, but it's "bottom-heavy" and rarely used. Jiff
/// will generally only produce spans of the first two types. In particular,
/// most `Span` producing APIs accept a "largest" [`Unit`] parameter, and the
/// result can be said to be a span "balanced up to the largest unit provided."
///
/// Balanced and unbalanced spans can be switched between as needed via
/// the [`Span::round`] API by providing a rounding configuration with
/// [`SpanRound::largest`]` set:
///
/// ```
/// use jiff::{SpanRound, ToSpan, Unit};
///
/// let span = 2.hours().minutes(30);
/// let unbalanced = span.round(SpanRound::new().largest(Unit::Minute))?;
/// assert_eq!(unbalanced, 150.minutes());
/// let balanced = unbalanced.round(SpanRound::new().largest(Unit::Hour))?;
/// assert_eq!(balanced, 2.hours().minutes(30));
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// Balancing can also be done as part of computing spans from two datetimes:
///
/// ```
/// use jiff::{civil::date, ToSpan, Unit};
///
/// let zdt1 = date(2024, 7, 7).at(15, 23, 0, 0).intz("America/New_York")?;
/// let zdt2 = date(2024, 11, 5).at(8, 0, 0, 0).intz("America/New_York")?;
///
/// // To make arithmetic reversible, the default largest unit for spans of
/// // time computed from zoned datetimes is hours:
/// assert_eq!(zdt1.until(&zdt2)?, 2_897.hour().minutes(37));
/// // But we can ask for the span to be balanced up to years:
/// assert_eq!(
///     zdt1.until((Unit::Year, &zdt2))?,
///     3.months().days(28).hours(16).minutes(37),
/// );
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// While the [`Span::round`] API does balancing, it also, of course, does
/// rounding as well. Rounding occurs when the smallest unit is set to
/// something bigger than [`Unit::Nanosecond`]:
///
/// ```
/// use jiff::{ToSpan, Unit};
///
/// let span = 2.hours().minutes(30);
/// assert_eq!(span.round(Unit::Hour)?, 3.hours());
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// When rounding spans with calendar units (years, months or weeks), then a
/// relative datetime is required:
///
/// ```
/// use jiff::{civil::date, SpanRound, ToSpan, Unit};
///
/// let span = 10.years().months(11);
/// let options = SpanRound::new()
///     .smallest(Unit::Year)
///     .relative(date(2024, 1, 1));
/// assert_eq!(span.round(options)?, 11.years());
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Days are not always 24 hours!
///
/// That is, a `Span` is made up of uniform and non-uniform units.
///
/// A uniform unit is a unit whose elapsed duration is always the same.
/// A non-uniform unit is a unit whose elapsed duration is not always the same.
/// There are two things that can impact the length of a non-uniform unit:
/// the calendar date and the time zone.
///
/// Years and months are always considered non-uniform units. For example,
/// 1 month from `2024-04-01` is 30 days, while 1 month from `2024-05-01` is
/// 31 days. Similarly for years because of leap years.
///
/// Hours, minutes, seconds, milliseconds, microseconds and nanoseconds are
/// always considered uniform units.
///
/// Days are only considered non-uniform when in the presence of a zone aware
/// datetime. A day can be more or less than 24 hours, and it can be balanced
/// up and down, but only when a relative zoned datetime is given. This
/// typically happens because of DST (daylight saving time), but can also occur
/// because of other time zone transitions too.
///
/// ```
/// use jiff::{civil::date, SpanRound, ToSpan, Unit};
///
/// // 2024-03-10 in New York was 23 hours long,
/// // because of a jump to DST at 2am.
/// let zdt = date(2024, 3, 9).at(21, 0, 0, 0).intz("America/New_York")?;
/// // Goes from days to hours:
/// assert_eq!(
///     1.day().round(SpanRound::new().largest(Unit::Hour).relative(&zdt))?,
///     23.hours(),
/// );
/// // Goes from hours to days:
/// assert_eq!(
///     23.hours().round(SpanRound::new().largest(Unit::Day).relative(&zdt))?,
///     1.day(),
/// );
/// // 24 hours is more than 1 day starting at this time:
/// assert_eq!(
///     24.hours().round(SpanRound::new().largest(Unit::Day).relative(&zdt))?,
///     1.day().hours(1),
/// );
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// And similarly, days can be longer than 24 hours:
///
/// ```
/// use jiff::{civil::date, SpanRound, ToSpan, Unit};
///
/// // 2024-11-03 in New York was 25 hours long,
/// // because of a repetition of the 1 o'clock AM hour.
/// let zdt = date(2024, 11, 2).at(21, 0, 0, 0).intz("America/New_York")?;
/// // Goes from days to hours:
/// assert_eq!(
///     1.day().round(SpanRound::new().largest(Unit::Hour).relative(&zdt))?,
///     25.hours(),
/// );
/// // Goes from hours to days:
/// assert_eq!(
///     25.hours().round(SpanRound::new().largest(Unit::Day).relative(&zdt))?,
///     1.day(),
/// );
/// // 24 hours is less than 1 day starting at this time,
/// // so it stays in units of hours even though we ask
/// // for days (because 24 isn't enough hours to make
/// // 1 day):
/// assert_eq!(
///     24.hours().round(SpanRound::new().largest(Unit::Day).relative(&zdt))?,
///     24.hours(),
/// );
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// For simplicity, weeks are always considered non-uniform. And generally
/// speaking, weeks only appear in a `Span` if they were explicitly put there
/// by the caller or if they were explicitly requested by the caller in an API.
/// For example:
///
/// ```
/// use jiff::{civil::date, ToSpan, Unit};
///
/// let dt1 = date(2024, 1, 1).at(0, 0, 0, 0);
/// let dt2 = date(2024, 7, 16).at(0, 0, 0, 0);
/// // Default units go up to days.
/// assert_eq!(dt1.until(dt2)?, 197.days());
/// // No weeks, even though we requested up to year.
/// assert_eq!(dt1.until((Unit::Year, dt2))?, 6.months().days(15));
/// // We get weeks only when we ask for them.
/// assert_eq!(dt1.until((Unit::Week, dt2))?, 28.weeks().days(1));
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Integration with [`std::time::Duration`]
///
/// While Jiff primarily uses a `Span` for doing arithmetic on datetimes, one
/// can convert between a `Span` and a [`Duration`](std::time::Duration) from
/// the standard library. The main difference between them is that a `Span`
/// always keeps tracks of its individual units, and a `Span` can represent
/// non-uniform units like months. In contrast, a `Duration` is always an
/// exact elapsed amount of time. It doesn't distinguish between `120 seconds`
/// and `2 minutes`. And it can't represent the concept of "months" because a
/// month doesn't have a single fixed amount of time.
///
/// However, a `Duration` is still useful in certain contexts. Beyond that,
/// it serves as an interoperability point due to its presence in the standard
/// library. Because of that, Jiff provides `TryFrom` trait implementations
/// for converting to and from a `Duration`. For example, to convert from
/// a `Duration` to a `Span`:
///
/// ```
/// use std::time::Duration;
///
/// use jiff::{Span, ToSpan};
///
/// let duration = Duration::new(86_400, 123_456_789);
/// let span = Span::try_from(duration)?;
/// // A duration-to-span conversion always results in a span with
/// // non-zero units no bigger than seconds.
/// assert_eq!(
///     span,
///     86_400.seconds().milliseconds(123).microseconds(456).nanoseconds(789),
/// );
///
/// // Note that the conversion is fallible! For example:
/// assert!(Span::try_from(Duration::from_secs(u64::MAX)).is_err());
/// // At present, a Jiff `Span` can only represent a range of time equal to
/// // the range of time expressible via minimum and maximum Jiff timestamps.
/// // Which is roughly -9999-01-01 to 9999-12-31, or ~20,000 years.
/// assert!(Span::try_from(Duration::from_secs(999_999_999_999)).is_err());
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// And to convert from a `Span` to a `Duration`:
///
/// ```
/// use std::time::Duration;
///
/// use jiff::{Span, ToSpan};
///
/// let span = 86_400.seconds()
///     .milliseconds(123)
///     .microseconds(456)
///     .nanoseconds(789);
/// let duration = Duration::try_from(span)?;
/// assert_eq!(duration, Duration::new(86_400, 123_456_789));
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// Note that an error will occur when converting a `Span` to a `Duration`
/// using the `TryFrom` trait implementation with units bigger than days:
///
/// ```
/// use std::time::Duration;
///
/// use jiff::{Span, ToSpan};
///
/// let span = 2.months().hours(10);
/// assert_eq!(
///     Duration::try_from(span).unwrap_err().to_string(),
///     "cannot convert span with non-zero months, must use Span::to_duration with a relative date instead",
/// );
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// If you need to convert such spans, then as the error suggests, you'll need
/// to use [`Span::to_duration`] with a relative date.
///
/// And note that since a `Span` is signed and a `Duration` is unsigned,
/// converting a negative `Span` to `Duration` will always fail. One can use
/// [`Span::signum`] to get the sign of the span and [`Span::abs`] to make the
/// span positive before converting it to a `Duration`:
///
/// ```
/// use std::time::Duration;
///
/// use jiff::{Span, ToSpan};
///
/// let span = -86_400.seconds().nanoseconds(1);
/// let (sign, duration) = (span.signum(), Duration::try_from(span.abs())?);
/// assert_eq!((sign, duration), (-1, Duration::new(86_400, 1)));
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Clone, Copy, Eq, PartialEq)]
pub struct Span {
    sign: Sign,
    years: t::SpanYears,
    months: t::SpanMonths,
    weeks: t::SpanWeeks,
    days: t::SpanDays,
    hours: t::SpanHours,
    minutes: t::SpanMinutes,
    seconds: t::SpanSeconds,
    milliseconds: t::SpanMilliseconds,
    microseconds: t::SpanMicroseconds,
    nanoseconds: t::SpanNanoseconds,
}

/// Infallible routines for setting units on a `Span`.
///
/// These are useful when the units are determined by the programmer or when
/// they have been validated elsewhere. In general, use these routines when
/// constructing an invalid `Span` should be considered a bug in the program.
impl Span {
    /// Creates a new span representing a zero duration. That is, a duration
    /// in which no time has passed.
    pub fn new() -> Span {
        Span::default()
    }

    /// Set the number of years on this span. The value may be negative.
    ///
    /// The fallible version of this method is [`Span::try_years`].
    ///
    /// # Panics
    ///
    /// This panics when the number of years is too small or too big.
    /// The minimum value is `-19,998`.
    /// The maximum value is `19,998`.
    #[inline]
    pub fn years<I: Into<i64>>(self, years: I) -> Span {
        self.try_years(years).expect("value for years is out of bounds")
    }

    /// Set the number of months on this span. The value may be negative.
    ///
    /// The fallible version of this method is [`Span::try_months`].
    ///
    /// # Panics
    ///
    /// This panics when the number of months is too small or too big.
    /// The minimum value is `-239,976`.
    /// The maximum value is `239,976`.
    #[inline]
    pub fn months<I: Into<i64>>(self, months: I) -> Span {
        self.try_months(months).expect("value for months is out of bounds")
    }

    /// Set the number of weeks on this span. The value may be negative.
    ///
    /// The fallible version of this method is [`Span::try_weeks`].
    ///
    /// # Panics
    ///
    /// This panics when the number of weeks is too small or too big.
    /// The minimum value is `-1,043,497`.
    /// The maximum value is `1_043_497`.
    #[inline]
    pub fn weeks<I: Into<i64>>(self, weeks: I) -> Span {
        self.try_weeks(weeks).expect("value for weeks is out of bounds")
    }

    /// Set the number of days on this span. The value may be negative.
    ///
    /// The fallible version of this method is [`Span::try_days`].
    ///
    /// # Panics
    ///
    /// This panics when the number of days is too small or too big.
    /// The minimum value is `-7,304,484`.
    /// The maximum value is `7,304,484`.
    #[inline]
    pub fn days<I: Into<i64>>(self, days: I) -> Span {
        self.try_days(days).expect("value for days is out of bounds")
    }

    /// Set the number of hours on this span. The value may be negative.
    ///
    /// The fallible version of this method is [`Span::try_hours`].
    ///
    /// # Panics
    ///
    /// This panics when the number of hours is too small or too big.
    /// The minimum value is `-175,307,616`.
    /// The maximum value is `175,307,616`.
    #[inline]
    pub fn hours<I: Into<i64>>(self, hours: I) -> Span {
        self.try_hours(hours).expect("value for hours is out of bounds")
    }

    /// Set the number of minutes on this span. The value may be negative.
    ///
    /// The fallible version of this method is [`Span::try_minutes`].
    ///
    /// # Panics
    ///
    /// This panics when the number of minutes is too small or too big.
    /// The minimum value is `-10,518,456,960`.
    /// The maximum value is `10,518,456,960`.
    #[inline]
    pub fn minutes<I: Into<i64>>(self, minutes: I) -> Span {
        self.try_minutes(minutes).expect("value for minutes is out of bounds")
    }

    /// Set the number of seconds on this span. The value may be negative.
    ///
    /// The fallible version of this method is [`Span::try_seconds`].
    ///
    /// # Panics
    ///
    /// This panics when the number of seconds is too small or too big.
    /// The minimum value is `-631,107,417,600`.
    /// The maximum value is `631,107,417,600`.
    #[inline]
    pub fn seconds<I: Into<i64>>(self, seconds: I) -> Span {
        self.try_seconds(seconds).expect("value for seconds is out of bounds")
    }

    /// Set the number of milliseconds on this span. The value may be negative.
    ///
    /// The fallible version of this method is [`Span::try_milliseconds`].
    ///
    /// # Panics
    ///
    /// This panics when the number of milliseconds is too small or too big.
    /// The minimum value is `-631,107,417,600,000`.
    /// The maximum value is `631,107,417,600,000`.
    #[inline]
    pub fn milliseconds<I: Into<i64>>(self, milliseconds: I) -> Span {
        self.try_milliseconds(milliseconds)
            .expect("value for milliseconds is out of bounds")
    }

    /// Set the number of microseconds on this span. The value may be negative.
    ///
    /// The fallible version of this method is [`Span::try_microseconds`].
    ///
    /// # Panics
    ///
    /// This panics when the number of microseconds is too small or too big.
    /// The minimum value is `-631,107,417,600,000,000`.
    /// The maximum value is `631,107,417,600,000,000`.
    #[inline]
    pub fn microseconds<I: Into<i64>>(self, microseconds: I) -> Span {
        self.try_microseconds(microseconds)
            .expect("value for microseconds is out of bounds")
    }

    /// Set the number of nanoseconds on this span. The value may be negative.
    ///
    /// Note that unlike all other units, a 64-bit integer number of
    /// nanoseconds is not big enough to represent all possible spans between
    /// all possible datetimes supported by Jiff. This means, for example, that
    /// computing a span between two datetimes that are far enough apart _and_
    /// requesting a largest unit of [`Unit::Nanosecond`], might return an
    /// error due to lack of precision.
    ///
    /// The fallible version of this method is [`Span::try_nanoseconds`].
    ///
    /// # Panics
    ///
    /// This panics when the number of nanoseconds is too small or too big.
    /// The minimum value is `-9,223,372,036,854,775,807`.
    /// The maximum value is `9,223,372,036,854,775,807`.
    #[inline]
    pub fn nanoseconds<I: Into<i64>>(self, nanoseconds: I) -> Span {
        self.try_nanoseconds(nanoseconds)
            .expect("value for nanoseconds is out of bounds")
    }
}

/// Fallible methods for setting units on a `Span`.
///
/// These methods are useful when the span is made up of user provided values
/// that may not be in range.
impl Span {
    /// Set the number of years on this span. The value may be negative.
    ///
    /// The panicking version of this method is [`Span::years`].
    ///
    /// # Errors
    ///
    /// This returns an error when the number of years is too small or too big.
    /// The minimum value is `-19,998`.
    /// The maximum value is `19,998`.
    #[inline]
    pub fn try_years<I: Into<i64>>(self, years: I) -> Result<Span, Error> {
        let years = t::SpanYears::try_new("years", years)?;
        Ok(self.years_ranged(years))
    }

    /// Set the number of months on this span. The value may be negative.
    ///
    /// The panicking version of this method is [`Span::months`].
    ///
    /// # Errors
    ///
    /// This returns an error when the number of months is too small or too big.
    /// The minimum value is `-239,976`.
    /// The maximum value is `239,976`.
    #[inline]
    pub fn try_months<I: Into<i64>>(self, months: I) -> Result<Span, Error> {
        type Range = ri64<{ t::SpanMonths::MIN }, { t::SpanMonths::MAX }>;
        let months = Range::try_new("months", months)?;
        Ok(self.months_ranged(months))
    }

    /// Set the number of weeks on this span. The value may be negative.
    ///
    /// The panicking version of this method is [`Span::weeks`].
    ///
    /// # Errors
    ///
    /// This returns an error when the number of weeks is too small or too big.
    /// The minimum value is `-1,043,497`.
    /// The maximum value is `1_043_497`.
    #[inline]
    pub fn try_weeks<I: Into<i64>>(self, weeks: I) -> Result<Span, Error> {
        type Range = ri64<{ t::SpanWeeks::MIN }, { t::SpanWeeks::MAX }>;
        let weeks = Range::try_new("weeks", weeks)?;
        Ok(self.weeks_ranged(weeks))
    }

    /// Set the number of days on this span. The value may be negative.
    ///
    /// The panicking version of this method is [`Span::days`].
    ///
    /// # Errors
    ///
    /// This returns an error when the number of days is too small or too big.
    /// The minimum value is `-7,304,484`.
    /// The maximum value is `7,304,484`.
    #[inline]
    pub fn try_days<I: Into<i64>>(self, days: I) -> Result<Span, Error> {
        type Range = ri64<{ t::SpanDays::MIN }, { t::SpanDays::MAX }>;
        let days = Range::try_new("days", days)?;
        Ok(self.days_ranged(days))
    }

    /// Set the number of hours on this span. The value may be negative.
    ///
    /// The panicking version of this method is [`Span::hours`].
    ///
    /// # Errors
    ///
    /// This returns an error when the number of hours is too small or too big.
    /// The minimum value is `-175,307,616`.
    /// The maximum value is `175,307,616`.
    #[inline]
    pub fn try_hours<I: Into<i64>>(self, hours: I) -> Result<Span, Error> {
        type Range = ri64<{ t::SpanHours::MIN }, { t::SpanHours::MAX }>;
        let hours = Range::try_new("hours", hours)?;
        Ok(self.hours_ranged(hours))
    }

    /// Set the number of minutes on this span. The value may be negative.
    ///
    /// The panicking version of this method is [`Span::minutes`].
    ///
    /// # Errors
    ///
    /// This returns an error when the number of minutes is too small or too big.
    /// The minimum value is `-10,518,456,960`.
    /// The maximum value is `10,518,456,960`.
    #[inline]
    pub fn try_minutes<I: Into<i64>>(self, minutes: I) -> Result<Span, Error> {
        type Range = ri64<{ t::SpanMinutes::MIN }, { t::SpanMinutes::MAX }>;
        let minutes = Range::try_new("minutes", minutes.into())?;
        Ok(self.minutes_ranged(minutes))
    }

    /// Set the number of seconds on this span. The value may be negative.
    ///
    /// The panicking version of this method is [`Span::seconds`].
    ///
    /// # Errors
    ///
    /// This returns an error when the number of seconds is too small or too big.
    /// The minimum value is `-631,107,417,600`.
    /// The maximum value is `631,107,417,600`.
    #[inline]
    pub fn try_seconds<I: Into<i64>>(self, seconds: I) -> Result<Span, Error> {
        type Range = ri64<{ t::SpanSeconds::MIN }, { t::SpanSeconds::MAX }>;
        let seconds = Range::try_new("seconds", seconds.into())?;
        Ok(self.seconds_ranged(seconds))
    }

    /// Set the number of milliseconds on this span. The value may be negative.
    ///
    /// The panicking version of this method is [`Span::milliseconds`].
    ///
    /// # Errors
    ///
    /// This returns an error when the number of milliseconds is too small or
    /// too big.
    /// The minimum value is `-631,107,417,600,000`.
    /// The maximum value is `631,107,417,600,000`.
    #[inline]
    pub fn try_milliseconds<I: Into<i64>>(
        self,
        milliseconds: I,
    ) -> Result<Span, Error> {
        type Range =
            ri64<{ t::SpanMilliseconds::MIN }, { t::SpanMilliseconds::MAX }>;
        let milliseconds =
            Range::try_new("milliseconds", milliseconds.into())?;
        Ok(self.milliseconds_ranged(milliseconds))
    }

    /// Set the number of microseconds on this span. The value may be negative.
    ///
    /// The panicking version of this method is [`Span::microseconds`].
    ///
    /// # Errors
    ///
    /// This returns an error when the number of microseconds is too small or
    /// too big.
    /// The minimum value is `-631,107,417,600,000,000`.
    /// The maximum value is `631,107,417,600,000,000`.
    #[inline]
    pub fn try_microseconds<I: Into<i64>>(
        self,
        microseconds: I,
    ) -> Result<Span, Error> {
        type Range =
            ri64<{ t::SpanMicroseconds::MIN }, { t::SpanMicroseconds::MAX }>;
        let microseconds =
            Range::try_new("microseconds", microseconds.into())?;
        Ok(self.microseconds_ranged(microseconds))
    }

    /// Set the number of nanoseconds on this span. The value may be negative.
    ///
    /// Note that unlike all other units, a 64-bit integer number of
    /// nanoseconds is not big enough to represent all possible spans between
    /// all possible datetimes supported by Jiff. This means, for example, that
    /// computing a span between two datetimes that are far enough apart _and_
    /// requesting a largest unit of [`Unit::Nanosecond`], might return an
    /// error due to lack of precision.
    ///
    /// The panicking version of this method is [`Span::nanoseconds`].
    ///
    /// # Errors
    ///
    /// This returns an error when the number of nanoseconds is too small or
    /// too big.
    /// The minimum value is `-9,223,372,036,854,775,807`.
    /// The maximum value is `9,223,372,036,854,775,807`.
    #[inline]
    pub fn try_nanoseconds<I: Into<i64>>(
        self,
        nanoseconds: I,
    ) -> Result<Span, Error> {
        type Range =
            ri64<{ t::SpanNanoseconds::MIN }, { t::SpanNanoseconds::MAX }>;
        let nanoseconds = Range::try_new("nanoseconds", nanoseconds.into())?;
        Ok(self.nanoseconds_ranged(nanoseconds))
    }
}

/// Routines for accessing the individual units in a `Span`.
impl Span {
    /// Returns the number of years in this span.
    #[inline]
    pub fn get_years(&self) -> i16 {
        self.get_years_ranged().get()
    }

    /// Returns the number of months in this span.
    #[inline]
    pub fn get_months(&self) -> i32 {
        self.get_months_ranged().get()
    }

    /// Returns the number of weeks in this span.
    #[inline]
    pub fn get_weeks(&self) -> i32 {
        self.get_weeks_ranged().get()
    }

    /// Returns the number of days in this span.
    #[inline]
    pub fn get_days(&self) -> i32 {
        self.get_days_ranged().get()
    }

    /// Returns the number of hours in this span.
    #[inline]
    pub fn get_hours(&self) -> i32 {
        self.get_hours_ranged().get()
    }

    /// Returns the number of minutes in this span.
    #[inline]
    pub fn get_minutes(&self) -> i64 {
        self.get_minutes_ranged().get()
    }

    /// Returns the number of seconds in this span.
    #[inline]
    pub fn get_seconds(&self) -> i64 {
        self.get_seconds_ranged().get()
    }

    /// Returns the number of milliseconds in this span.
    #[inline]
    pub fn get_milliseconds(&self) -> i64 {
        self.get_milliseconds_ranged().get()
    }

    /// Returns the number of microseconds in this span.
    #[inline]
    pub fn get_microseconds(&self) -> i64 {
        self.get_microseconds_ranged().get()
    }

    /// Returns the number of nanoseconds in this span.
    #[inline]
    pub fn get_nanoseconds(&self) -> i64 {
        self.get_nanoseconds_ranged().get()
    }
}

/// Routines for manipulating, comparing and inspecting `Span` values.
impl Span {
    /// Returns a new span that is the absolute value of this span.
    ///
    /// If this span is zero or positive, then this is a no-op.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::ToSpan;
    ///
    /// let span = -100.seconds();
    /// assert_eq!(span.to_string(), "-PT100s");
    /// let span = span.abs();
    /// assert_eq!(span.to_string(), "PT100s");
    /// ```
    #[inline]
    pub fn abs(self) -> Span {
        if self.is_zero() {
            return self;
        }
        Span { sign: ri8::N::<1>(), ..self }
    }

    /// Returns a new span that negates this span.
    ///
    /// If this span is zero, then this is a no-op. If this span is negative,
    /// then the returned span is positive. If this span is positive, then
    /// the returned span is negative.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::ToSpan;
    ///
    /// let span = 100.days();
    /// assert_eq!(span.to_string(), "P100d");
    /// let span = span.negate();
    /// assert_eq!(span.to_string(), "-P100d");
    /// ```
    ///
    /// # Example: available via the negation operator
    ///
    /// This routine can also be used via `-`:
    ///
    /// ```
    /// use jiff::ToSpan;
    ///
    /// let span = 100.days();
    /// assert_eq!(span.to_string(), "P100d");
    /// let span = -span;
    /// assert_eq!(span.to_string(), "-P100d");
    /// ```
    #[inline]
    pub fn negate(self) -> Span {
        Span { sign: -self.sign, ..self }
    }

    /// Returns the "sign number" or "signum" of this span.
    ///
    /// The number returned is `-1` when this span is negative,
    /// `0` when this span is zero and `1` when this span is positive.
    #[inline]
    pub fn signum(self) -> i8 {
        self.sign.signum().get()
    }

    /// Returns true if and only if this span is positive.
    ///
    /// This returns false when the span is zero or negative.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::ToSpan;
    ///
    /// assert!(!2.months().is_negative());
    /// assert!((-2.months()).is_negative());
    /// ```
    #[inline]
    pub fn is_positive(self) -> bool {
        self.get_sign_ranged() > 0
    }

    /// Returns true if and only if this span is negative.
    ///
    /// This returns false when the span is zero or positive.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::ToSpan;
    ///
    /// assert!(!2.months().is_negative());
    /// assert!((-2.months()).is_negative());
    /// ```
    #[inline]
    pub fn is_negative(self) -> bool {
        self.get_sign_ranged() < 0
    }

    /// Returns true if and only if every field in this span is set to `0`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::{Span, ToSpan};
    ///
    /// assert!(Span::new().is_zero());
    /// assert!(Span::default().is_zero());
    /// assert!(0.seconds().is_zero());
    /// assert!(!0.seconds().seconds(1).is_zero());
    /// assert!(0.seconds().seconds(1).seconds(0).is_zero());
    /// ```
    #[inline]
    pub fn is_zero(self) -> bool {
        self.sign == 0
    }

    /// Multiplies each field in this span by a given integer.
    ///
    /// If this would cause any individual field in this span to overflow, then
    /// this returns an error.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::ToSpan;
    ///
    /// let span = 4.days().seconds(8);
    /// assert_eq!(span.checked_mul(2)?, 8.days().seconds(16));
    /// assert_eq!(span.checked_mul(-3)?, -12.days().seconds(24));
    /// // Notice that no re-balancing is done. It's "just" multiplication.
    /// assert_eq!(span.checked_mul(10)?, 40.days().seconds(80));
    ///
    /// let span = 10_000.years();
    /// // too big!
    /// assert!(span.checked_mul(3).is_err());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: available via the multiplication operator
    ///
    /// This method can be used via the `*` operator. Note though that a panic
    /// happens on overflow.
    ///
    /// ```
    /// use jiff::ToSpan;
    ///
    /// let span = 4.days().seconds(8);
    /// assert_eq!(span * 2, 8.days().seconds(16));
    /// assert_eq!(2 * span, 8.days().seconds(16));
    /// assert_eq!(span * -3, -12.days().seconds(24));
    /// assert_eq!(-3 * span, -12.days().seconds(24));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn checked_mul(mut self, rhs: i64) -> Result<Span, Error> {
        if rhs == 0 {
            return Ok(Span::default());
        } else if rhs == 1 {
            return Ok(self);
        }
        self.sign *= t::Sign::try_new("span factor", rhs.signum())
            .expect("signum fits in ri8");
        // This is all somewhat odd, but since each of our span fields uses
        // a different primitive representation and range of allowed values,
        // we only seek to perform multiplications when they will actually
        // do something. Otherwise, we risk multiplying the mins/maxs of a
        // ranged integer and causing a spurious panic. Basically, the idea
        // here is the allowable values for our multiple depend on what we're
        // actually going to multiply with it. If our span has non-zero years,
        // then our multiple can't exceed the bounds of `SpanYears`, otherwise
        // it is guaranteed to overflow.
        if self.years != 0 {
            let rhs = t::SpanYears::try_new("years multiple", rhs)?;
            self.years = self.years.try_checked_mul("years", rhs.abs())?;
        }
        if self.months != 0 {
            let rhs = t::SpanMonths::try_new("months multiple", rhs)?;
            self.months = self.months.try_checked_mul("months", rhs.abs())?;
        }
        if self.weeks != 0 {
            let rhs = t::SpanWeeks::try_new("weeks multiple", rhs)?;
            self.weeks = self.weeks.try_checked_mul("weeks", rhs.abs())?;
        }
        if self.days != 0 {
            let rhs = t::SpanDays::try_new("days multiple", rhs)?;
            self.days = self.days.try_checked_mul("days", rhs.abs())?;
        }
        if self.hours != 0 {
            let rhs = t::SpanHours::try_new("hours multiple", rhs)?;
            self.hours = self.hours.try_checked_mul("hours", rhs.abs())?;
        }
        if self.minutes != 0 {
            let rhs = t::SpanMinutes::try_new("minutes multiple", rhs)?;
            self.minutes =
                self.minutes.try_checked_mul("minutes", rhs.abs())?;
        }
        if self.seconds != 0 {
            let rhs = t::SpanSeconds::try_new("seconds multiple", rhs)?;
            self.seconds =
                self.seconds.try_checked_mul("seconds", rhs.abs())?;
        }
        if self.milliseconds != 0 {
            let rhs =
                t::SpanMilliseconds::try_new("milliseconds multiple", rhs)?;
            self.milliseconds = self
                .milliseconds
                .try_checked_mul("milliseconds", rhs.abs())?;
        }
        if self.microseconds != 0 {
            let rhs =
                t::SpanMicroseconds::try_new("microseconds multiple", rhs)?;
            self.microseconds = self
                .microseconds
                .try_checked_mul("microseconds", rhs.abs())?;
        }
        if self.nanoseconds != 0 {
            let rhs =
                t::SpanNanoseconds::try_new("nanoseconds multiple", rhs)?;
            self.nanoseconds =
                self.nanoseconds.try_checked_mul("nanoseconds", rhs.abs())?;
        }
        Ok(self)
    }

    /// Adds a span to this one and returns the sum as a new span.
    ///
    /// When adding a span with units greater than days, callers must provide
    /// a relative datetime to anchor the spans.
    ///
    /// Arithmetic proceeds as specified in [RFC 5545]. Bigger units are
    /// added together before smaller units.
    ///
    /// This routine accepts anything that implements `Into<SpanArithmetic>`.
    /// There are some trait implementations that make using this routine
    /// ergonomic:
    ///
    /// * `From<Span> for SpanArithmetic` adds the given span to this one.
    /// * `From<(Span, civil::Date)> for SpanArithmetic` adds the given
    /// span to this one relative to the given date. There are also `From`
    /// implementations for `civil::DateTime` and `Zoned`.
    ///
    /// Adding a negative span is equivalent to subtracting its absolute value.
    ///
    /// The largest non-zero unit in the span returned is at most the largest
    /// non-zero unit among the two spans being added.
    ///
    /// The sum returned is automatically re-balanced so that the span is not
    /// "bottom heavy."
    ///
    /// [RFC 5545]: https://datatracker.ietf.org/doc/html/rfc5545
    ///
    /// # Errors
    ///
    /// This returns an error when adding the two spans would overflow any
    /// individual field of a span.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::ToSpan;
    ///
    /// assert_eq!(1.hour().checked_add(30.minutes())?, 1.hour().minutes(30));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: re-balancing
    ///
    /// This example shows how units are automatically rebalanced into bigger
    /// units when appropriate.
    ///
    /// ```
    /// use jiff::ToSpan;
    ///
    /// let span1 = 2.days().hours(23);
    /// let span2 = 2.hours();
    /// // When no relative datetime is given, days are always 24 hours long.
    /// assert_eq!(span1.checked_add(span2)?, 3.days().hours(1));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: adding spans with calendar units
    ///
    /// If you try to add two spans with calendar units without specifying a
    /// relative datetime, you'll get an error:
    ///
    /// ```
    /// use jiff::ToSpan;
    ///
    /// let span1 = 1.month().days(15);
    /// let span2 = 15.days();
    /// assert!(span1.checked_add(span2).is_err());
    /// ```
    ///
    /// A relative datetime is needed because calendar spans may correspond to
    /// different actual durations depending on where the span begins:
    ///
    /// ```
    /// use jiff::{civil::date, ToSpan};
    ///
    /// let span1 = 1.month().days(15);
    /// let span2 = 15.days();
    /// // 1 month from March 1 is 31 days...
    /// assert_eq!(
    ///     span1.checked_add((span2, date(2008, 3, 1)))?,
    ///     2.months(),
    /// );
    /// // ... but 1 month from April 1 is 30 days!
    /// assert_eq!(
    ///     span1.checked_add((span2, date(2008, 4, 1)))?,
    ///     1.month().days(30),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: error on overflow
    ///
    /// Adding two spans can overflow, and this will result in an error:
    ///
    /// ```
    /// use jiff::ToSpan;
    ///
    /// assert!(19_998.years().checked_add(1.year()).is_err());
    /// ```
    #[inline]
    pub fn checked_add<'a>(
        &self,
        options: impl Into<SpanArithmetic<'a>>,
    ) -> Result<Span, Error> {
        let options: SpanArithmetic<'_> = options.into();
        options.checked_add(*self)
    }

    /// Like `checked_add`, but only applies for invariant units. That is,
    /// when *both* spans whose non-zero units are all days or smaller.
    #[inline]
    fn checked_add_invariant(
        &self,
        unit: Unit,
        span: &Span,
    ) -> Result<Span, Error> {
        assert!(unit <= Unit::Day);
        let nanos1 = self.to_invariant_nanoseconds();
        let nanos2 = span.to_invariant_nanoseconds();
        let sum = nanos1 + nanos2;
        Span::from_invariant_nanoseconds(unit, sum)
    }

    /// Subtracts a span from this one and returns the difference as a new
    /// span.
    ///
    /// When subtracting a span with units greater than days, callers must
    /// provide a relative datetime to anchor the spans.
    ///
    /// Arithmetic proceeds as specified in [RFC 5545]. Bigger units are
    /// added together before smaller units.
    ///
    /// This routine accepts anything that implements `Into<SpanArithmetic>`.
    /// There are some trait implementations that make using this routine
    /// ergonomic:
    ///
    /// * `From<Span> for SpanArithmetic` adds the given span to this one.
    /// * `From<(Span, civil::Date)> for SpanArithmetic` adds the given
    /// span to this one relative to the given date. There are also `From`
    /// implementations for `civil::DateTime` and `Zoned`.
    ///
    /// Subtracting a negative span is equivalent to adding its absolute value.
    ///
    /// The largest non-zero unit in the span returned is at most the largest
    /// non-zero unit among the two spans being subtracted.
    ///
    /// The difference returned is automatically re-balanced so that the span
    /// is not "bottom heavy."
    ///
    /// [RFC 5545]: https://datatracker.ietf.org/doc/html/rfc5545
    ///
    /// # Errors
    ///
    /// This returns an error when subtracting the two spans would overflow any
    /// individual field of a span.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::ToSpan;
    ///
    /// assert_eq!(1.hour().checked_sub(30.minutes())?, 30.minutes());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: re-balancing
    ///
    /// This example shows how units are automatically rebalanced into bigger
    /// units when appropriate.
    ///
    /// ```
    /// use jiff::ToSpan;
    ///
    /// let span1 = 2.days().hours(23);
    /// let span2 = 25.hours();
    /// // When no relative datetime is given, days are always 24 hours long.
    /// assert_eq!(span1.checked_sub(span2)?, 1.day().hours(22));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: subtracting spans with calendar units
    ///
    /// If you try to subtract two spans with calendar units without specifying
    /// a relative datetime, you'll get an error:
    ///
    /// ```
    /// use jiff::ToSpan;
    ///
    /// let span1 = 1.month().days(15);
    /// let span2 = 15.days();
    /// assert!(span1.checked_add(span2).is_err());
    /// ```
    ///
    /// A relative datetime is needed because calendar spans may correspond to
    /// different actual durations depending on where the span begins:
    ///
    /// ```
    /// use jiff::{civil::date, ToSpan};
    ///
    /// let span1 = 3.months();
    /// let span2 = 1.month().days(15);
    /// assert_eq!(
    ///     span1.checked_sub((span2, date(2008, 4, 1)))?,
    ///     1.month().days(16),
    /// );
    /// assert_eq!(
    ///     span1.checked_sub((span2, date(2008, 5, 1)))?,
    ///     1.month().days(15),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: error on overflow
    ///
    /// Subtracting two spans can overflow, and this will result in an error:
    ///
    /// ```
    /// use jiff::ToSpan;
    ///
    /// assert!((-19_998).years().checked_sub(1.year()).is_err());
    /// ```
    #[inline]
    pub fn checked_sub<'a>(
        &self,
        options: impl Into<SpanArithmetic<'a>>,
    ) -> Result<Span, Error> {
        let mut options: SpanArithmetic<'_> = options.into();
        options.span = -options.span;
        options.checked_add(*self)
    }

    /// Compares two spans in terms of how long they are. Negative spans are
    /// considered shorter than the zero span.
    ///
    /// Two spans compare equal when they correspond to the same duration
    /// of time, even if their individual fields are different. This is in
    /// contrast to the `Eq` trait implementation of `Span`, which performs
    /// exact field-wise comparisons. This split exists because the comparison
    /// provided by this routine is "heavy" in that it may need to do
    /// datetime arithmetic to return an answer. In contrast, the `Eq` trait
    /// implementation is "cheap."
    ///
    /// This routine accepts anything that implements `Into<SpanCompare>`.
    /// There are some trait implementations that make using this routine
    /// ergonomic:
    ///
    /// * `From<Span> for SpanCompare` compares the given span to this one.
    /// * `From<(Span, civil::Date)> for SpanArithmetic` compares the given
    /// span to this one relative to the given date. There are also `From`
    /// implementations for `civil::DateTime` and `Zoned`.
    ///
    /// # Errors
    ///
    /// If either of the spans being compared have a non-zero calendar unit
    /// (units bigger than days), then this routine requires a relative
    /// datetime. If one is not provided, then an error is returned.
    ///
    /// An error can also occur when adding either span to the relative
    /// datetime given results in overflow.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::ToSpan;
    ///
    /// let span1 = 3.hours();
    /// let span2 = 180.minutes();
    /// assert_eq!(span1.compare(span2)?, std::cmp::Ordering::Equal);
    /// // But notice that the two spans are not equal via `Eq`:
    /// assert_ne!(span1, span2);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: negative spans are less than zero
    ///
    /// ```
    /// use jiff::ToSpan;
    ///
    /// let span1 = -1.second();
    /// let span2 = 0.seconds();
    /// assert_eq!(span1.compare(span2)?, std::cmp::Ordering::Less);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: comparisons take DST into account
    ///
    /// When a relative datetime is time zone aware, then DST is taken into
    /// account when comparing spans:
    ///
    /// ```
    /// use jiff::{ToSpan, Zoned};
    ///
    /// let span1 = 79.hours().minutes(10);
    /// let span2 = 3.days().hours(7).seconds(630);
    /// let span3 = 3.days().hours(6).minutes(50);
    ///
    /// let relative: Zoned = "2020-11-01T00-07[America/Los_Angeles]".parse()?;
    /// let mut spans = [span1, span2, span3];
    /// spans.sort_by(|s1, s2| s1.compare((s2, &relative)).unwrap());
    /// assert_eq!(spans, [span1, span3, span2]);
    ///
    /// // Compare with the result of sorting without taking DST into account.
    /// // We can do that here since days are considered 24 hours long in all
    /// // cases when no relative datetime is provided:
    /// spans.sort_by(|s1, s2| s1.compare(s2).unwrap());
    /// assert_eq!(spans, [span3, span1, span2]);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// See the examples for [`Span::total`] if you want to sort spans without
    /// an `unwrap()` call.
    #[inline]
    pub fn compare<'a>(
        &self,
        options: impl Into<SpanCompare<'a>>,
    ) -> Result<Ordering, Error> {
        let options: SpanCompare<'_> = options.into();
        options.compare(*self)
    }

    /// Returns a floating point number representing the total number of a
    /// specific unit (as given) in this span. If the span is not evenly
    /// divisible by the requested units, then the number returned may have a
    /// fractional component.
    ///
    /// This routine accepts anything that implements `Into<SpanTotal>`. There
    /// are some trait implementations that make using this routine ergonomic:
    ///
    /// * `From<Unit> for SpanTotal` computes a total for the given unit in
    /// this span.
    /// * `From<(Unit, civil::Date)> for SpanTotal` computes a total for the
    /// given unit in this span, relative to the given date. There are also
    /// `From` implementations for `civil::DateTime` and `Zoned`.
    ///
    /// # Errors
    ///
    /// If this span has any non-zero calendar unit (units bigger than days),
    /// then this routine requires a relative datetime. If one is not provided,
    /// then an error is returned.
    ///
    /// An error can also occur when adding the span to the relative
    /// datetime given results in overflow.
    ///
    /// # Example
    ///
    /// This example shows how to find the number of seconds in a particular
    /// span:
    ///
    /// ```
    /// use jiff::{ToSpan, Unit};
    ///
    /// let span = 3.hours().minutes(10);
    /// assert_eq!(span.total(Unit::Second)?, 11_400.0);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: 24 hour days
    ///
    /// This shows how to find the total number of 24 hour days in
    /// `123,456,789` seconds.
    ///
    /// ```
    /// use jiff::{ToSpan, Unit};
    ///
    /// let span = 123_456_789.seconds();
    /// assert_eq!(span.total(Unit::Day)?, 1428.8980208333332);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: DST is taken into account
    ///
    /// The month of March 2024 in `America/New_York` had 31 days, but one of
    /// those days was 23 hours long due a transition into daylight saving
    /// time:
    ///
    /// ```
    /// use jiff::{civil::date, ToSpan, Unit};
    ///
    /// let span = 744.hours();
    /// let relative = date(2024, 3, 1).intz("America/New_York")?;
    /// // Because of the short day, 744 hours is actually a little *more* than
    /// // 1 month starting from 2024-03-01.
    /// assert_eq!(span.total((Unit::Month, &relative))?, 1.0013888888888889);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// Now compare what happens when the relative datetime is civil and not
    /// time zone aware:
    ///
    /// ```
    /// use jiff::{civil::date, ToSpan, Unit};
    ///
    /// let span = 744.hours();
    /// let relative = date(2024, 3, 1);
    /// assert_eq!(span.total((Unit::Month, relative))?, 1.0);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: infallible sorting
    ///
    /// The sorting example in [`Span::compare`] has to use `unwrap()` in
    /// its `sort_by(..)` call because `Span::compare` may fail and there
    /// is no "fallible" sorting routine in Rust's standard library (as of
    /// 2024-07-07). While the ways in which `Span::compare` can fail for
    /// a valid configuration limited to overflow for "extreme" values, it
    /// is possible to sort spans infallibly by computing floating point
    /// representations for each span up-front:
    ///
    /// ```
    /// use jiff::{ToSpan, Unit, Zoned};
    ///
    /// let span1 = 79.hours().minutes(10);
    /// let span2 = 3.days().hours(7).seconds(630);
    /// let span3 = 3.days().hours(6).minutes(50);
    ///
    /// let relative: Zoned = "2020-11-01T00-07[America/Los_Angeles]".parse()?;
    /// let mut spans = [
    ///     (span1, span1.total((Unit::Day, &relative))?),
    ///     (span2, span2.total((Unit::Day, &relative))?),
    ///     (span3, span3.total((Unit::Day, &relative))?),
    /// ];
    /// spans.sort_by(|&(_, total1), &(_, total2)| total1.total_cmp(&total2));
    /// assert_eq!(spans.map(|(sp, _)| sp), [span1, span3, span2]);
    ///
    /// // Compare with the result of sorting without taking DST into account.
    /// // We can do that here since days are considered 24 hours long in all
    /// // cases when no relative datetime is provided:
    /// let mut spans = [
    ///     (span1, span1.total(Unit::Day)?),
    ///     (span2, span2.total(Unit::Day)?),
    ///     (span3, span3.total(Unit::Day)?),
    /// ];
    /// spans.sort_by(|&(_, total1), &(_, total2)| total1.total_cmp(&total2));
    /// assert_eq!(spans.map(|(sp, _)| sp), [span3, span1, span2]);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn total<'a>(
        &self,
        options: impl Into<SpanTotal<'a>>,
    ) -> Result<f64, Error> {
        let options: SpanTotal<'_> = options.into();
        options.total(*self)
    }

    /// Returns a new span that is balanced and rounded.
    ///
    /// Rounding a span has a number of parameters, all of which are optional.
    /// When no parameters are given, then no rounding or balancing is done,
    /// and the span as given is returned. That is, it's a no-op.
    ///
    /// The parameters are, in brief:
    ///
    /// * [`SpanRound::largest`] sets the largest [`Unit`] that is allowed to
    /// be non-zero in the span returned. When _only_ the largest unit is set,
    /// rounding itself doesn't occur and instead the span is merely balanced.
    /// * [`SpanRound::smallest`] sets the smallest [`Unit`] that is allowed to
    /// be non-zero in the span returned. By default, it is set to
    /// [`Unit::Nanosecond`], i.e., no rounding occurs. When the smallest unit
    /// is set to something bigger than nanoseconds, then the non-zero units
    /// in the span smaller than the smallest unit are used to determine how
    /// the span should be rounded. For example, rounding `1 hour 59 minutes`
    /// to the nearest hour using the default rounding mode would produce
    /// `2 hours`.
    /// * [`SpanRound::mode`] determines how to handle the remainder when
    /// rounding. The default is [`RoundMode::HalfExpand`], which corresponds
    /// to how you were taught to round in school. Alternative modes, like
    /// [`RoundMode::Trunc`], exist too. For example, a truncating rounding of
    /// `1 hour 59 minutes` to the nearest hour would produce `1 hour`.
    /// * [`SpanRound::increment`] sets the rounding granularity to use for
    /// the configured smallest unit. For example, if the smallest unit is
    /// minutes and the increment is 5, then the span returned will always have
    /// its minute units set to a multiple of `5`.
    /// * [`SpanRound::relative`] sets the datetime from which to interpret the
    /// span. This is required when rounding spans with calendar units (years,
    /// months or weeks). When a relative datetime is time zone aware, then
    /// rounding accounts for the fact that not all days are 24 hours long.
    /// When a relative datetime is omitted or is civil (not time zone aware),
    /// then days are always 24 hours long.
    ///
    /// # Constructing a [`SpanRound`]
    ///
    /// This routine accepts anything that implements `Into<SpanRound>`. There
    /// are a few key trait implementations that make this convenient:
    ///
    /// * `From<Unit> for SpanRound` will construct a rounding configuration
    /// where the smallest unit is set to the one given.
    /// * `From<(Unit, i64)> for SpanRound` will construct a rounding
    /// configuration where the smallest unit and the rounding increment are
    /// set to the ones given.
    ///
    /// To set other options (like the largest unit, the rounding mode and the
    /// relative datetime), one must explicitly create a `SpanRound` and pass
    /// it to this routine.
    ///
    /// # Errors
    ///
    /// In general, there are two main ways for rounding to fail: an improper
    /// configuration like trying to round a span with calendar units but
    /// without a relative datetime, or when overflow occurs. Overflow can
    /// occur when the span, added to the relative datetime if given, would
    /// exceed the minimum or maximum datetime values. Overflow can also occur
    /// if the span is too big to fit into the request unit configuration. For
    /// example, a span like `19_998.years()` cannot be represented with a
    /// 64-bit integer number of nanoseconds.
    ///
    /// # Example: balancing
    ///
    /// This example demonstrates balancing, not rounding. And in particular,
    /// this example shows how to balance a span as much as possible without
    /// needing to specify a relative datetime:
    ///
    /// ```
    /// use jiff::{SpanRound, ToSpan, Unit};
    ///
    /// let span = 123_456_789_123_456_789i64.nanoseconds();
    /// assert_eq!(
    ///     span.round(SpanRound::new().largest(Unit::Day))?,
    ///     1_428.days()
    ///         .hours(21).minutes(33).seconds(9)
    ///         .milliseconds(123).microseconds(456).nanoseconds(789),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: balancing and rounding
    ///
    /// This example is like the one before it, but where we round to the
    /// nearest second:
    ///
    /// ```
    /// use jiff::{SpanRound, ToSpan, Unit};
    ///
    /// let span = 123_456_789_123_456_789i64.nanoseconds();
    /// assert_eq!(
    ///     span.round(SpanRound::new().largest(Unit::Day).smallest(Unit::Second))?,
    ///     1_428.days().hours(21).minutes(33).seconds(9),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// Or, just rounding to the nearest day can make use of the
    /// `From<Unit> for SpanRound` trait implementation:
    ///
    /// ```
    /// use jiff::{SpanRound, ToSpan, Unit};
    ///
    /// let span = 123_456_789_123_456_789i64.nanoseconds();
    /// assert_eq!(span.round(Unit::Day)?, 1_429.days());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: balancing with a relative datetime
    ///
    /// Even with calendar units, so long as a relative datetime is provided,
    /// it's easy to turn days into bigger units:
    ///
    /// ```
    /// use jiff::{civil::date, SpanRound, ToSpan, Unit};
    ///
    /// let span = 1_000.days();
    /// let relative = date(2000, 1, 1);
    /// let options = SpanRound::new().largest(Unit::Year).relative(relative);
    /// assert_eq!(span.round(options)?, 2.years().months(8).days(26));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: round to the nearest half-hour
    ///
    /// ```
    /// use jiff::{Span, ToSpan, Unit};
    ///
    /// let span: Span = "PT23h50m3.123s".parse()?;
    /// assert_eq!(span.round((Unit::Minute, 30))?, 24.hours());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: yearly quarters in a span
    ///
    /// This example shows how to find how many full 3 month quarters are in a
    /// particular span of time.
    ///
    /// ```
    /// use jiff::{civil::date, RoundMode, SpanRound, ToSpan, Unit};
    ///
    /// let span1 = 10.months().days(15);
    /// let round = SpanRound::new()
    ///     .smallest(Unit::Month)
    ///     .increment(3)
    ///     .mode(RoundMode::Trunc)
    ///     // A relative datetime must be provided when
    ///     // rounding involves calendar units.
    ///     .relative(date(2024, 1, 1));
    /// let span2 = span1.round(round)?;
    /// assert_eq!(span2.get_months() / 3, 3);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn round<'a>(
        self,
        options: impl Into<SpanRound<'a>>,
    ) -> Result<Span, Error> {
        let options: SpanRound<'a> = options.into();
        options.round(self)
    }

    /// Converts a non-negative `Span` to an unsigned [`std::time::Duration`]
    /// relative to the date given.
    ///
    /// In most cases, it is unlikely that you'll need to use this routine to
    /// convert a `Span` to a `Duration`. Namely, every Jiff routine for
    /// computing a `Span` between datetimes ([`Zoned`], [`Timestamp`],
    /// [`DateTime`], etc.) will return spans with uniform units by default.
    /// That is, _by default_:
    ///
    /// * [`Zoned::until`] guarantees that the biggest non-zero unit is hours.
    /// * [`Timestamp::until`] guarantees that the biggest non-zero unit is
    /// seconds.
    /// * [`DateTime::until`] guarantees that the biggest non-zero unit is
    /// days.
    /// * [`Date::until`] guarantees that the biggest non-zero unit is days.
    /// * [`Time::until`] guarantees that the biggest non-zero unit is hours.
    ///
    /// Of course, this can be changed by asking, for example, `Zoned::until`
    /// to return units up to years. But by default, in every case above,
    /// converting the resulting `Span` to a `std::time::Duration` can be done
    /// _correctly_ without providing a relative date. This conversion is done
    /// with the `TryFrom<Span> for Duration` trait implementation. (Which will
    /// error when given a span with non-zero units bigger than days.)
    ///
    /// # Errors
    ///
    /// This returns an error if this span is negative or if adding this span
    /// to the date given results in overflow.
    ///
    /// # Example: converting a span with calendar units to a `Duration`
    ///
    /// This compares the number of seconds in a non-leap year with a leap
    /// year:
    ///
    /// ```
    /// use std::time::Duration;
    ///
    /// use jiff::{civil::date, Span, ToSpan};
    ///
    /// let span = 1.year();
    ///
    /// let duration = span.to_duration(date(2024, 1, 1))?;
    /// assert_eq!(duration, Duration::from_secs(31_622_400));
    /// let duration = span.to_duration(date(2023, 1, 1))?;
    /// assert_eq!(duration, Duration::from_secs(31_536_000));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: converting a negative span
    ///
    /// Since a `Span` is signed and a `Duration` is unsigned, converting
    /// a negative `Span` to `Duration` will always fail. One can use
    /// [`Span::signum`] to get the sign of the span and [`Span::abs`] to make
    /// the span positive before converting it to a `Duration`:
    ///
    /// ```
    /// use std::time::Duration;
    ///
    /// use jiff::{civil::date, Span, ToSpan};
    ///
    /// let span = -1.year();
    /// let (sign, duration) = (
    ///     span.signum(),
    ///     span.abs().to_duration(date(2024, 1, 1))?,
    /// );
    /// assert_eq!((sign, duration), (-1, Duration::from_secs(31_622_400)));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn to_duration<'a>(
        &self,
        relative: impl Into<SpanRelativeTo<'a>>,
    ) -> Result<Duration, Error> {
        if self.is_negative() {
            return Err(err!(
                "cannot convert negative span {self:?} \
                 to unsigned std::time::Duration",
            ));
        }
        let max_unit = self.largest_unit();
        let relative: SpanRelativeTo<'a> = relative.into();
        if !relative.is_variable(max_unit) {
            return Ok(self.to_duration_invariant());
        }
        let relspan = relative
            .to_relative()
            .and_then(|r| r.into_relative_span(Unit::Second, *self))
            .with_context(|| {
                err!(
                    "could not compute normalized relative span \
                     from datetime {relative} and span {self}",
                    relative = relative.kind,
                )
            })?;
        debug_assert!(relspan.span.largest_unit() <= Unit::Second);
        Ok(relspan.span.to_duration_invariant())
    }

    /// Converts a positive and entirely invariant span to a std Duration.
    ///
    /// Callers must ensure that this span is positive and that it has no units
    /// greater than days. If it does have non-zero units of days, then every
    /// day is considered 24 hours.
    #[inline]
    fn to_duration_invariant(&self) -> Duration {
        // This guarantees, at compile time, that a maximal invariant Span
        // (that is, all units are days or lower and all units are set to their
        // maximum values) will still balance out to a number of seconds that
        // fits into a `u64`. This in turn implies that a `Duration` can
        // represent all possible invariant positive spans.
        const _FITS_IN_U64: () = {
            debug_assert!(
                u64::MAX as u128
                    > ((t::SpanDays::MAX * t::SECONDS_PER_CIVIL_DAY.bound())
                        + (t::SpanHours::MAX * t::SECONDS_PER_HOUR.bound())
                        + (t::SpanMinutes::MAX
                            * t::SECONDS_PER_MINUTE.bound())
                        + t::SpanSeconds::MAX
                        + (t::SpanMilliseconds::MAX
                            / t::MILLIS_PER_SECOND.bound())
                        + (t::SpanMicroseconds::MAX
                            / t::MICROS_PER_SECOND.bound())
                        + (t::SpanNanoseconds::MAX
                            / t::NANOS_PER_SECOND.bound()))
                        as u128,
            );
            ()
        };

        let nanos = self.to_invariant_nanoseconds();
        debug_assert!(nanos >= 0, "span must be positive");
        debug_assert!(
            self.largest_unit() <= Unit::Day,
            "units must be days or lower"
        );

        let seconds = nanos / t::NANOS_PER_SECOND;
        // These are OK because even if we have maximal units for days, hours,
        // minutes, seconds, milliseconds, microseconds and nanoseconds, it
        // still doesn't combine to more than u64::MAX seconds.
        let seconds = i64::from(seconds);
        let seconds = u64::try_from(seconds).unwrap();

        let subsec_nanos = nanos % t::NANOS_PER_SECOND;
        // These are okay because we assume nanos is positive and
        // because % 1_000_000_000 above guarantees that the result
        // fits into a 32-bit integer, signed or unsigned.
        let subsec_nanos = i32::try_from(subsec_nanos).unwrap();
        let subsec_nanos = u32::try_from(subsec_nanos).unwrap();

        // Duration::new can panic if subsec_nanos >= 1_000_000_000 and seconds
        // == u64::MAX. But this can never happen because we guaranteed by
        // construction above that subsec_nanos < 1_000_000_000.
        Duration::new(seconds, subsec_nanos)
    }
}

/// Crate internal APIs that operate on ranged integer types.
impl Span {
    #[inline]
    pub(crate) fn years_ranged(self, years: impl RInto<t::SpanYears>) -> Span {
        let years = years.rinto();
        let mut span = Span { years: years.abs(), ..self };
        span.sign = self.resign(years, &span);
        span
    }

    #[inline]
    pub(crate) fn months_ranged(
        self,
        months: impl RInto<t::SpanMonths>,
    ) -> Span {
        let months = months.rinto();
        let mut span = Span { months: months.abs(), ..self };
        span.sign = self.resign(months, &span);
        span
    }

    #[inline]
    pub(crate) fn weeks_ranged(self, weeks: impl RInto<t::SpanWeeks>) -> Span {
        let weeks = weeks.rinto();
        let mut span = Span { weeks: weeks.abs(), ..self };
        span.sign = self.resign(weeks, &span);
        span
    }

    #[inline]
    pub(crate) fn days_ranged(self, days: impl RInto<t::SpanDays>) -> Span {
        let days = days.rinto();
        let mut span = Span { days: days.abs(), ..self };
        span.sign = self.resign(days, &span);
        span
    }

    #[inline]
    pub(crate) fn hours_ranged(self, hours: impl RInto<t::SpanHours>) -> Span {
        let hours = hours.rinto();
        let mut span = Span { hours: hours.abs(), ..self };
        span.sign = self.resign(hours, &span);
        span
    }

    #[inline]
    pub(crate) fn minutes_ranged(
        self,
        minutes: impl RInto<t::SpanMinutes>,
    ) -> Span {
        let minutes = minutes.rinto();
        let mut span = Span { minutes: minutes.abs(), ..self };
        span.sign = self.resign(minutes, &span);
        span
    }

    #[inline]
    pub(crate) fn seconds_ranged(
        self,
        seconds: impl RInto<t::SpanSeconds>,
    ) -> Span {
        let seconds = seconds.rinto();
        let mut span = Span { seconds: seconds.abs(), ..self };
        span.sign = self.resign(seconds, &span);
        span
    }

    #[inline]
    fn milliseconds_ranged(
        self,
        milliseconds: impl RInto<t::SpanMilliseconds>,
    ) -> Span {
        let milliseconds = milliseconds.rinto();
        let mut span = Span { milliseconds: milliseconds.abs(), ..self };
        span.sign = self.resign(milliseconds, &span);
        span
    }

    #[inline]
    fn microseconds_ranged(
        self,
        microseconds: impl RInto<t::SpanMicroseconds>,
    ) -> Span {
        let microseconds = microseconds.rinto();
        let mut span = Span { microseconds: microseconds.abs(), ..self };
        span.sign = self.resign(microseconds, &span);
        span
    }

    #[inline]
    pub(crate) fn nanoseconds_ranged(
        self,
        nanoseconds: impl RInto<t::SpanNanoseconds>,
    ) -> Span {
        let nanoseconds = nanoseconds.rinto();
        let mut span = Span { nanoseconds: nanoseconds.abs(), ..self };
        span.sign = self.resign(nanoseconds, &span);
        span
    }

    #[inline]
    fn try_years_ranged(
        self,
        years: impl TryRInto<t::SpanYears>,
    ) -> Result<Span, Error> {
        let years = years.try_rinto("years")?;
        Ok(self.years_ranged(years))
    }

    #[inline]
    fn try_months_ranged(
        self,
        months: impl TryRInto<t::SpanMonths>,
    ) -> Result<Span, Error> {
        let months = months.try_rinto("months")?;
        Ok(self.months_ranged(months))
    }

    #[inline]
    fn try_weeks_ranged(
        self,
        weeks: impl TryRInto<t::SpanWeeks>,
    ) -> Result<Span, Error> {
        let weeks = weeks.try_rinto("weeks")?;
        Ok(self.weeks_ranged(weeks))
    }

    #[inline]
    fn try_days_ranged(
        self,
        days: impl TryRInto<t::SpanDays>,
    ) -> Result<Span, Error> {
        let days = days.try_rinto("days")?;
        Ok(self.days_ranged(days))
    }

    #[inline]
    pub(crate) fn try_hours_ranged(
        self,
        hours: impl TryRInto<t::SpanHours>,
    ) -> Result<Span, Error> {
        let hours = hours.try_rinto("hours")?;
        Ok(self.hours_ranged(hours))
    }

    #[inline]
    pub(crate) fn try_minutes_ranged(
        self,
        minutes: impl TryRInto<t::SpanMinutes>,
    ) -> Result<Span, Error> {
        let minutes = minutes.try_rinto("minutes")?;
        Ok(self.minutes_ranged(minutes))
    }

    #[inline]
    pub(crate) fn try_seconds_ranged(
        self,
        seconds: impl TryRInto<t::SpanSeconds>,
    ) -> Result<Span, Error> {
        let seconds = seconds.try_rinto("seconds")?;
        Ok(self.seconds_ranged(seconds))
    }

    #[inline]
    pub(crate) fn try_milliseconds_ranged(
        self,
        milliseconds: impl TryRInto<t::SpanMilliseconds>,
    ) -> Result<Span, Error> {
        let milliseconds = milliseconds.try_rinto("milliseconds")?;
        Ok(self.milliseconds_ranged(milliseconds))
    }

    #[inline]
    pub(crate) fn try_microseconds_ranged(
        self,
        microseconds: impl TryRInto<t::SpanMicroseconds>,
    ) -> Result<Span, Error> {
        let microseconds = microseconds.try_rinto("microseconds")?;
        Ok(self.microseconds_ranged(microseconds))
    }

    #[inline]
    pub(crate) fn try_nanoseconds_ranged(
        self,
        nanoseconds: impl TryRInto<t::SpanNanoseconds>,
    ) -> Result<Span, Error> {
        let nanoseconds = nanoseconds.try_rinto("nanoseconds")?;
        Ok(self.nanoseconds_ranged(nanoseconds))
    }

    #[inline]
    pub(crate) fn try_units_ranged(
        self,
        unit: Unit,
        value: impl RInto<NoUnits>,
    ) -> Result<Span, Error> {
        let value = value.rinto();
        match unit {
            Unit::Year => self.try_years_ranged(value),
            Unit::Month => self.try_months_ranged(value),
            Unit::Week => self.try_weeks_ranged(value),
            Unit::Day => self.try_days_ranged(value),
            Unit::Hour => self.try_hours_ranged(value),
            Unit::Minute => self.try_minutes_ranged(value),
            Unit::Second => self.try_seconds_ranged(value),
            Unit::Millisecond => self.try_milliseconds_ranged(value),
            Unit::Microsecond => self.try_microseconds_ranged(value),
            Unit::Nanosecond => self.try_nanoseconds_ranged(value),
        }
    }

    #[inline]
    pub(crate) fn get_years_ranged(&self) -> t::SpanYears {
        self.years * self.sign
    }

    #[inline]
    pub(crate) fn get_months_ranged(&self) -> t::SpanMonths {
        self.months * self.sign
    }

    #[inline]
    pub(crate) fn get_weeks_ranged(&self) -> t::SpanWeeks {
        self.weeks * self.sign
    }

    #[inline]
    pub(crate) fn get_days_ranged(&self) -> t::SpanDays {
        self.days * self.sign
    }

    #[inline]
    pub(crate) fn get_hours_ranged(&self) -> t::SpanHours {
        self.hours * self.sign
    }

    #[inline]
    pub(crate) fn get_minutes_ranged(&self) -> t::SpanMinutes {
        self.minutes * self.sign
    }

    #[inline]
    pub(crate) fn get_seconds_ranged(&self) -> t::SpanSeconds {
        self.seconds * self.sign
    }

    #[inline]
    pub(crate) fn get_milliseconds_ranged(&self) -> t::SpanMilliseconds {
        self.milliseconds * self.sign
    }

    #[inline]
    pub(crate) fn get_microseconds_ranged(&self) -> t::SpanMicroseconds {
        self.microseconds * self.sign
    }

    #[inline]
    pub(crate) fn get_nanoseconds_ranged(&self) -> t::SpanNanoseconds {
        self.nanoseconds * self.sign
    }

    #[inline]
    fn get_sign_ranged(&self) -> ri8<-1, 1> {
        self.sign
    }

    #[inline]
    fn get_units_ranged(&self, unit: Unit) -> NoUnits {
        match unit {
            Unit::Year => self.get_years_ranged().rinto(),
            Unit::Month => self.get_months_ranged().rinto(),
            Unit::Week => self.get_weeks_ranged().rinto(),
            Unit::Day => self.get_days_ranged().rinto(),
            Unit::Hour => self.get_hours_ranged().rinto(),
            Unit::Minute => self.get_minutes_ranged().rinto(),
            Unit::Second => self.get_seconds_ranged().rinto(),
            Unit::Millisecond => self.get_milliseconds_ranged().rinto(),
            Unit::Microsecond => self.get_microseconds_ranged().rinto(),
            Unit::Nanosecond => self.get_nanoseconds_ranged().rinto(),
        }
    }
}

/// Crate internal helper routines.
impl Span {
    /// Converts the given number of nanoseconds to a `Span` whose units do not
    /// exceed `largest`.
    ///
    /// Note that `largest` is capped at `Unit::Day`. That is, if any unit
    /// greater than `Unit::Day` is given, then it is treated as `Unit::Day`.
    /// And also note that days in this context are civil days. That is, they
    /// are always 24 hours long. Callers needing to deal with variable length
    /// days should do so outside of this routine and should not provide a
    /// `largest` unit bigger than `Unit::Hour`.
    pub(crate) fn from_invariant_nanoseconds(
        largest: Unit,
        nanos: impl RInto<NoUnits128>,
    ) -> Result<Span, Error> {
        let nanos = nanos.rinto();
        let mut span = Span::new();
        match largest {
            Unit::Year | Unit::Month | Unit::Week | Unit::Day => {
                let micros = nanos.div_ceil(t::NANOS_PER_MICRO);
                span = span.try_nanoseconds_ranged(
                    nanos.rem_ceil(t::NANOS_PER_MICRO),
                )?;
                let millis = micros.div_ceil(t::MICROS_PER_MILLI);
                span = span.try_microseconds_ranged(
                    micros.rem_ceil(t::MICROS_PER_MILLI),
                )?;
                let secs = millis.div_ceil(t::MILLIS_PER_SECOND);
                span = span.try_milliseconds_ranged(
                    millis.rem_ceil(t::MILLIS_PER_SECOND),
                )?;
                let mins = secs.div_ceil(t::SECONDS_PER_MINUTE);
                span = span.try_seconds_ranged(
                    secs.rem_ceil(t::SECONDS_PER_MINUTE),
                )?;
                let hours = mins.div_ceil(t::MINUTES_PER_HOUR);
                span = span
                    .try_minutes_ranged(mins.rem_ceil(t::MINUTES_PER_HOUR))?;
                let days = hours.div_ceil(t::HOURS_PER_CIVIL_DAY);
                span = span.try_hours_ranged(
                    hours.rem_ceil(t::HOURS_PER_CIVIL_DAY),
                )?;
                span = span.try_days_ranged(days)?;
                Ok(span)
            }
            Unit::Hour => {
                let micros = nanos.div_ceil(t::NANOS_PER_MICRO);
                span = span.try_nanoseconds_ranged(
                    nanos.rem_ceil(t::NANOS_PER_MICRO),
                )?;
                let millis = micros.div_ceil(t::MICROS_PER_MILLI);
                span = span.try_microseconds_ranged(
                    micros.rem_ceil(t::MICROS_PER_MILLI),
                )?;
                let secs = millis.div_ceil(t::MILLIS_PER_SECOND);
                span = span.try_milliseconds_ranged(
                    millis.rem_ceil(t::MILLIS_PER_SECOND),
                )?;
                let mins = secs.div_ceil(t::SECONDS_PER_MINUTE);
                span = span.try_seconds_ranged(
                    secs.rem_ceil(t::SECONDS_PER_MINUTE),
                )?;
                let hours = mins.div_ceil(t::MINUTES_PER_HOUR);
                span = span
                    .try_minutes_ranged(mins.rem_ceil(t::MINUTES_PER_HOUR))?;
                span = span.try_hours_ranged(hours)?;
                Ok(span)
            }
            Unit::Minute => {
                let micros = nanos.div_ceil(t::NANOS_PER_MICRO);
                span = span.try_nanoseconds_ranged(
                    nanos.rem_ceil(t::NANOS_PER_MICRO),
                )?;
                let millis = micros.div_ceil(t::MICROS_PER_MILLI);
                span = span.try_microseconds_ranged(
                    micros.rem_ceil(t::MICROS_PER_MILLI),
                )?;
                let secs = millis.div_ceil(t::MILLIS_PER_SECOND);
                span = span.try_milliseconds_ranged(
                    millis.rem_ceil(t::MILLIS_PER_SECOND),
                )?;
                let mins = secs.div_ceil(t::SECONDS_PER_MINUTE);
                span =
                    span.try_seconds(secs.rem_ceil(t::SECONDS_PER_MINUTE))?;
                span = span.try_minutes_ranged(mins)?;
                Ok(span)
            }
            Unit::Second => {
                let micros = nanos.div_ceil(t::NANOS_PER_MICRO);
                span = span.try_nanoseconds_ranged(
                    nanos.rem_ceil(t::NANOS_PER_MICRO),
                )?;
                let millis = micros.div_ceil(t::MICROS_PER_MILLI);
                span = span.try_microseconds_ranged(
                    micros.rem_ceil(t::MICROS_PER_MILLI),
                )?;
                let secs = millis.div_ceil(t::MILLIS_PER_SECOND);
                span = span.try_milliseconds_ranged(
                    millis.rem_ceil(t::MILLIS_PER_SECOND),
                )?;
                span = span.try_seconds_ranged(secs)?;
                Ok(span)
            }
            Unit::Millisecond => {
                let micros = nanos.div_ceil(t::NANOS_PER_MICRO);
                span = span.try_nanoseconds_ranged(
                    nanos.rem_ceil(t::NANOS_PER_MICRO),
                )?;
                let millis = micros.div_ceil(t::MICROS_PER_MILLI);
                span = span.try_microseconds_ranged(
                    micros.rem_ceil(t::MICROS_PER_MILLI),
                )?;
                span = span.try_milliseconds_ranged(millis)?;
                Ok(span)
            }
            Unit::Microsecond => {
                let micros = nanos.div_ceil(t::NANOS_PER_MICRO);
                span = span.try_nanoseconds_ranged(
                    nanos.rem_ceil(t::NANOS_PER_MICRO),
                )?;
                span = span.try_microseconds_ranged(micros)?;
                Ok(span)
            }
            Unit::Nanosecond => {
                span = span.try_nanoseconds_ranged(nanos)?;
                Ok(span)
            }
        }
    }

    /// Converts the non-variable units of this `Span` to a total number of
    /// nanoseconds.
    ///
    /// This includes days, even though they can be of irregular length during
    /// time zone transitions. If this applies, then callers should set the
    /// days to `0` before calling this routine.
    ///
    /// All units above days are always ignored.
    #[inline]
    pub(crate) fn to_invariant_nanoseconds(&self) -> NoUnits128 {
        let mut nanos = NoUnits128::rfrom(self.get_nanoseconds_ranged());
        nanos += NoUnits128::rfrom(self.get_microseconds_ranged())
            * t::NANOS_PER_MICRO;
        nanos += NoUnits128::rfrom(self.get_milliseconds_ranged())
            * t::NANOS_PER_MILLI;
        nanos +=
            NoUnits128::rfrom(self.get_seconds_ranged()) * t::NANOS_PER_SECOND;
        nanos +=
            NoUnits128::rfrom(self.get_minutes_ranged()) * t::NANOS_PER_MINUTE;
        nanos +=
            NoUnits128::rfrom(self.get_hours_ranged()) * t::NANOS_PER_HOUR;
        nanos +=
            NoUnits128::rfrom(self.get_days_ranged()) * t::NANOS_PER_CIVIL_DAY;
        nanos
    }

    /// Rebalances the invariant units (days or lower) on this span so that
    /// the largest possible non-zero unit is the one given.
    ///
    /// Units above day are ignored and dropped.
    ///
    /// If the given unit is greater than days, then it is treated as-if it
    /// were days.
    ///
    /// # Errors
    ///
    /// This can return an error in the case of lop-sided units. For example,
    /// if this span has maximal values for all units, then rebalancing is
    /// not possible because the number of days after balancing would exceed
    /// the limit.
    #[allow(dead_code)] // REMOVE ME
    #[inline]
    pub(crate) fn rebalance(self, unit: Unit) -> Result<Span, Error> {
        Span::from_invariant_nanoseconds(unit, self.to_invariant_nanoseconds())
    }

    /// Returns an equivalent span, but with all units greater than or equal to
    /// the one given set to zero.
    #[inline(always)]
    pub(crate) fn only_lower(self, unit: Unit) -> Span {
        let mut span = self;
        // Unit::Nanosecond is the minimum, so nothing can be smaller than it.
        if unit <= Unit::Microsecond {
            span = span.microseconds_ranged(C(0));
        }
        if unit <= Unit::Millisecond {
            span = span.milliseconds_ranged(C(0));
        }
        if unit <= Unit::Second {
            span = span.seconds_ranged(C(0));
        }
        if unit <= Unit::Minute {
            span = span.minutes_ranged(C(0));
        }
        if unit <= Unit::Hour {
            span = span.hours_ranged(C(0));
        }
        if unit <= Unit::Day {
            span = span.days_ranged(C(0));
        }
        if unit <= Unit::Week {
            span = span.weeks_ranged(C(0));
        }
        if unit <= Unit::Month {
            span = span.months_ranged(C(0));
        }
        if unit <= Unit::Year {
            span = span.years_ranged(C(0));
        }
        span
    }

    /// Returns an equivalent span, but with all units less than the one given
    /// set to zero.
    #[inline(always)]
    pub(crate) fn without_lower(self, unit: Unit) -> Span {
        let mut span = self;
        if unit > Unit::Nanosecond {
            span = span.nanoseconds_ranged(C(0));
        }
        if unit > Unit::Microsecond {
            span = span.microseconds_ranged(C(0));
        }
        if unit > Unit::Millisecond {
            span = span.milliseconds_ranged(C(0));
        }
        if unit > Unit::Second {
            span = span.seconds_ranged(C(0));
        }
        if unit > Unit::Minute {
            span = span.minutes_ranged(C(0));
        }
        if unit > Unit::Hour {
            span = span.hours_ranged(C(0));
        }
        if unit > Unit::Day {
            span = span.days_ranged(C(0));
        }
        if unit > Unit::Week {
            span = span.weeks_ranged(C(0));
        }
        if unit > Unit::Month {
            span = span.months_ranged(C(0));
        }
        // Unit::Year is the max, so nothing can be bigger than it.
        span
    }

    /// Returns an error corresponding to the smallest non-time non-zero unit.
    ///
    /// If all non-time units are zero, then this returns `None`.
    #[inline(always)]
    pub(crate) fn smallest_non_time_non_zero_unit_error(
        &self,
    ) -> Option<Error> {
        if self.days != 0 {
            Some(t::SpanDays::error("days", self.days.get()))
        } else if self.weeks != 0 {
            Some(t::SpanWeeks::error("weeks", self.weeks.get()))
        } else if self.months != 0 {
            Some(t::SpanMonths::error("months", self.months.get()))
        } else if self.years != 0 {
            Some(t::SpanYears::error("years", self.years.get()))
        } else {
            None
        }
    }

    /// Returns the largest non-zero unit in this span.
    ///
    /// If all components of this span are zero, then `Unit::Nanosecond` is
    /// returned.
    #[inline]
    pub(crate) fn largest_unit(&self) -> Unit {
        if self.years != 0 {
            Unit::Year
        } else if self.months != 0 {
            Unit::Month
        } else if self.weeks != 0 {
            Unit::Week
        } else if self.days != 0 {
            Unit::Day
        } else if self.hours != 0 {
            Unit::Hour
        } else if self.minutes != 0 {
            Unit::Minute
        } else if self.seconds != 0 {
            Unit::Second
        } else if self.milliseconds != 0 {
            Unit::Millisecond
        } else if self.microseconds != 0 {
            Unit::Microsecond
        } else {
            Unit::Nanosecond
        }
    }

    /// Returns a string containing the value of all non-zero fields.
    ///
    /// This is useful for debugging. Normally, this would be the "alternate"
    /// debug impl (perhaps), but that's what insta uses and I preferred having
    /// the standard serialization used there.
    #[allow(dead_code)]
    fn debug(&self) -> alloc::string::String {
        use core::fmt::Write;

        let mut buf = alloc::string::String::new();
        write!(buf, "Span {{ sign: {:?}", self.sign).unwrap();
        if self.years != 0 {
            write!(buf, ", years: {:?}", self.years).unwrap();
        }
        if self.months != 0 {
            write!(buf, ", months: {:?}", self.months).unwrap();
        }
        if self.weeks != 0 {
            write!(buf, ", weeks: {:?}", self.weeks).unwrap();
        }
        if self.days != 0 {
            write!(buf, ", days: {:?}", self.days).unwrap();
        }
        if self.hours != 0 {
            write!(buf, ", hours: {:?}", self.hours).unwrap();
        }
        if self.minutes != 0 {
            write!(buf, ", minutes: {:?}", self.minutes).unwrap();
        }
        if self.seconds != 0 {
            write!(buf, ", seconds: {:?}", self.seconds).unwrap();
        }
        if self.milliseconds != 0 {
            write!(buf, ", milliseconds: {:?}", self.milliseconds).unwrap();
        }
        if self.microseconds != 0 {
            write!(buf, ", microseconds: {:?}", self.microseconds).unwrap();
        }
        if self.nanoseconds != 0 {
            write!(buf, ", nanoseconds: {:?}", self.nanoseconds).unwrap();
        }
        write!(buf, " }}").unwrap();
        buf
    }

    /// Given some new units to set on this span and the span updates with the
    /// new units, this determines the what the sign of `new` should be.
    #[inline]
    fn resign(&self, units: impl RInto<NoUnits>, new: &Span) -> Sign {
        let units = units.rinto();
        // Negative units anywhere always makes the entire span negative.
        if units < 0 {
            return Sign::N::<-1>();
        }
        let mut new_is_zero = new.sign == 0 && units == 0;
        // When `units == 0` and it was previously non-zero, then `new.sign`
        // won't be `0` and thus `new_is_zero` will be false when it should
        // be true. So in this case, we need to re-check all the units to set
        // the sign correctly.
        if units == 0 {
            new_is_zero = new.years == 0
                && new.months == 0
                && new.weeks == 0
                && new.days == 0
                && new.hours == 0
                && new.minutes == 0
                && new.seconds == 0
                && new.milliseconds == 0
                && new.microseconds == 0
                && new.nanoseconds == 0;
        }
        match (self.is_zero(), new_is_zero) {
            (_, true) => Sign::N::<0>(),
            (true, false) => units.signum().rinto(),
            // If the old and new span are both non-zero, and we know our new
            // units are not negative, then the sign remains unchanged.
            (false, false) => new.sign,
        }
    }
}

impl Default for Span {
    #[inline]
    fn default() -> Span {
        Span {
            sign: ri8::N::<0>(),
            years: C(0).rinto(),
            months: C(0).rinto(),
            weeks: C(0).rinto(),
            days: C(0).rinto(),
            hours: C(0).rinto(),
            minutes: C(0).rinto(),
            seconds: C(0).rinto(),
            milliseconds: C(0).rinto(),
            microseconds: C(0).rinto(),
            nanoseconds: C(0).rinto(),
        }
    }
}

impl core::fmt::Debug for Span {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        core::fmt::Display::fmt(self, f)
    }
}

impl core::fmt::Display for Span {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        use crate::fmt::StdFmtWrite;

        DEFAULT_SPAN_PRINTER
            .print_span(self, StdFmtWrite(f))
            .map_err(|_| core::fmt::Error)
    }
}

impl core::str::FromStr for Span {
    type Err = Error;

    #[inline]
    fn from_str(string: &str) -> Result<Span, Error> {
        DEFAULT_SPAN_PARSER.parse_span(string)
    }
}

impl core::ops::Neg for Span {
    type Output = Span;

    #[inline]
    fn neg(self) -> Span {
        self.negate()
    }
}

/// This multiplies each unit in a span by an integer.
///
/// This panics on overflow. For checked arithmetic, use [`Span::checked_mul`].
impl core::ops::Mul<i64> for Span {
    type Output = Span;

    #[inline]
    fn mul(self, rhs: i64) -> Span {
        self.checked_mul(rhs)
            .expect("multiplying `Span` by a scalar overflowed")
    }
}

/// This multiplies each unit in a span by an integer.
///
/// This panics on overflow. For checked arithmetic, use [`Span::checked_mul`].
impl core::ops::Mul<Span> for i64 {
    type Output = Span;

    #[inline]
    fn mul(self, rhs: Span) -> Span {
        rhs.checked_mul(self)
            .expect("multiplying `Span` by a scalar overflowed")
    }
}

/// Converts a `Span` to a [`std::time::Duration`].
///
/// Note that this assumes that days are always 24 hours long.
///
/// # Errors
///
/// This can fail for only two reasons:
///
/// * The span is negative. This is an error because a `std::time::Duration` is
///   unsigned.)
/// * The span has any non-zero units greater than days. This is an error
///   because it's impossible to determine the length of, e.g., a month without
///   a reference date.
///
/// This can never result in overflow because a `Duration` can represent a
/// bigger span of time than `Span` limits to units of days or lower.
///
/// If you need to convert a `Span` to a `Duration` that has non-zero units
/// bigger than days (or a `Span` with days of non-uniform length), then please
/// use [`Span::to_duration`] with a corresponding relative date.
///
/// # Example: maximal span
///
/// This example shows the maximum possible span using units of days or
/// smaller, and the corresponding `Duration` value:
///
/// ```
/// use std::time::Duration;
///
/// use jiff::Span;
///
/// let sp = Span::new()
///     .days(7_304_484)
///     .hours(175_307_616)
///     .minutes(10_518_456_960i64)
///     .seconds(631_107_417_600i64)
///     .milliseconds(631_107_417_600_000i64)
///     .microseconds(631_107_417_600_000_000i64)
///     .nanoseconds(9_223_372_036_854_775_807i64);
/// let duration = Duration::try_from(sp)?;
/// assert_eq!(duration, Duration::new(3_795_867_877_636, 854_775_807));
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Example: converting a negative span
///
/// Since a `Span` is signed and a `Duration` is unsigned, converting
/// a negative `Span` to `Duration` will always fail. One can use
/// [`Span::signum`] to get the sign of the span and [`Span::abs`] to make the
/// span positive before converting it to a `Duration`:
///
/// ```
/// use std::time::Duration;
///
/// use jiff::{Span, ToSpan};
///
/// let span = -86_400.seconds().nanoseconds(1);
/// let (sign, duration) = (span.signum(), Duration::try_from(span.abs())?);
/// assert_eq!((sign, duration), (-1, Duration::new(86_400, 1)));
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
impl TryFrom<Span> for Duration {
    type Error = Error;

    #[inline]
    fn try_from(sp: Span) -> Result<Duration, Error> {
        if sp.is_negative() {
            return Err(err!(
                "cannot convert negative span {sp:?} \
                 to unsigned std::time::Duration",
            ));
        }
        if sp.largest_unit() > Unit::Day {
            return Err(err!(
                "cannot convert span with non-zero {unit}, \
                 must use Span::to_duration with a relative date \
                 instead",
                unit = sp.largest_unit().plural(),
            ));
        }
        Ok(sp.to_duration_invariant())
    }
}

/// Converts a [`std::time::Duration`] to a `Span`.
///
/// The span returned from this conversion will only ever have non-zero units
/// of seconds or smaller.
///
/// # Errors
///
/// This only fails when the given `Duration` overflows the maximum number of
/// seconds representable by a `Span`.
///
/// # Example
///
/// This shows a basic conversion:
///
/// ```
/// use std::time::Duration;
///
/// use jiff::{Span, ToSpan};
///
/// let duration = Duration::new(86_400, 123_456_789);
/// let span = Span::try_from(duration)?;
/// // A duration-to-span conversion always results in a span with
/// // non-zero units no bigger than seconds.
/// assert_eq!(
///     span,
///     86_400.seconds().milliseconds(123).microseconds(456).nanoseconds(789),
/// );
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Example: rounding
///
/// This example shows how to convert a `Duration` to a `Span`, and then round
/// it up to bigger units given a relative date:
///
/// ```
/// use std::time::Duration;
///
/// use jiff::{civil::date, Span, SpanRound, ToSpan, Unit};
///
/// let duration = Duration::new(450 * 86_401, 0);
/// let span = Span::try_from(duration)?;
/// // We get back a simple span of just seconds:
/// assert_eq!(span, Span::new().seconds(450 * 86_401));
/// // But we can balance it up to bigger units:
/// let options = SpanRound::new()
///     .largest(Unit::Year)
///     .relative(date(2024, 1, 1));
/// assert_eq!(
///     span.round(options)?,
///     1.year().months(2).days(25).minutes(7).seconds(30),
/// );
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
impl TryFrom<Duration> for Span {
    type Error = Error;

    #[inline]
    fn try_from(d: Duration) -> Result<Span, Error> {
        let seconds = i64::try_from(d.as_secs()).map_err(|_| {
            err!("seconds from {d:?} overflows a 64-bit signed integer")
        })?;
        let nanoseconds = i64::from(d.subsec_nanos());
        let milliseconds = nanoseconds / t::NANOS_PER_MILLI.value();
        let microseconds = (nanoseconds % t::NANOS_PER_MILLI.value())
            / t::NANOS_PER_MICRO.value();
        let nanoseconds = nanoseconds % t::NANOS_PER_MICRO.value();

        let span = Span::new().try_seconds(seconds).with_context(|| {
            err!("duration {d:?} overflows limits of a Jiff `Span`")
        })?;
        // These are all OK because `Duration::subsec_nanos` is guaranteed to
        // return less than 1_000_000_000 nanoseconds. And splitting that up
        // into millis, micros and nano components is guaranteed to fit into
        // the limits of a `Span`.
        Ok(span
            .milliseconds(milliseconds)
            .microseconds(microseconds)
            .nanoseconds(nanoseconds))
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for Span {
    #[inline]
    fn serialize<S: serde::Serializer>(
        &self,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        serializer.collect_str(self)
    }
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for Span {
    #[inline]
    fn deserialize<D: serde::Deserializer<'de>>(
        deserializer: D,
    ) -> Result<Span, D::Error> {
        use serde::de;

        struct SpanVisitor;

        impl<'de> de::Visitor<'de> for SpanVisitor {
            type Value = Span;

            fn expecting(
                &self,
                f: &mut core::fmt::Formatter,
            ) -> core::fmt::Result {
                f.write_str("a span duration string")
            }

            #[inline]
            fn visit_bytes<E: de::Error>(
                self,
                value: &[u8],
            ) -> Result<Span, E> {
                DEFAULT_SPAN_PARSER
                    .parse_span(value)
                    .map_err(de::Error::custom)
            }

            #[inline]
            fn visit_str<E: de::Error>(self, value: &str) -> Result<Span, E> {
                self.visit_bytes(value.as_bytes())
            }
        }

        deserializer.deserialize_bytes(SpanVisitor)
    }
}

#[cfg(test)]
impl quickcheck::Arbitrary for Span {
    fn arbitrary(g: &mut quickcheck::Gen) -> Span {
        // In order to sample from the full space of possible spans, we need
        // to provide a relative datetime. But if we do that, then it's
        // possible the span plus the datetime overflows. So we pick one
        // datetime and shrink the size of the span we can produce.
        type Nanos = ri64<-631_107_417_600_000_000, 631_107_417_600_000_000>;
        let nanos = Nanos::arbitrary(g).get();
        let relative =
            SpanRelativeTo::from(DateTime::constant(0, 1, 1, 0, 0, 0, 0));
        let round =
            SpanRound::new().largest(Unit::arbitrary(g)).relative(relative);
        Span::new().nanoseconds(nanos).round(round).unwrap()
    }

    fn shrink(&self) -> alloc::boxed::Box<dyn Iterator<Item = Self>> {
        alloc::boxed::Box::new(
            (
                (
                    self.get_years_ranged(),
                    self.get_months_ranged(),
                    self.get_weeks_ranged(),
                    self.get_days_ranged(),
                ),
                (
                    self.get_hours_ranged(),
                    self.get_minutes_ranged(),
                    self.get_seconds_ranged(),
                    self.get_milliseconds_ranged(),
                ),
                (
                    self.get_microseconds_ranged(),
                    self.get_nanoseconds_ranged(),
                ),
            )
                .shrink()
                .filter_map(
                    |(
                        (years, months, weeks, days),
                        (hours, minutes, seconds, milliseconds),
                        (microseconds, nanoseconds),
                    )| {
                        let span = Span::new()
                            .years_ranged(years)
                            .months_ranged(months)
                            .weeks_ranged(weeks)
                            .days_ranged(days)
                            .hours_ranged(hours)
                            .minutes_ranged(minutes)
                            .seconds_ranged(seconds)
                            .milliseconds_ranged(milliseconds)
                            .microseconds_ranged(microseconds)
                            .nanoseconds_ranged(nanoseconds);
                        Some(span)
                    },
                ),
        )
    }
}

/// A trait for enabling concise literals for creating [`Span`] values.
///
/// In short, this trait lets you write something like `5.seconds()` or
/// `1.day()` to create a [`Span`]. Once a `Span` has been created, you can
/// use its mutator methods to add more fields. For example,
/// `1.day().hours(10)` is equivalent to `Span::new().days(1).hours(10)`.
///
/// This trait is implemented for the following integer types: `i8`, `i16`,
/// `i32` and `i64`.
///
/// Note that this trait is provided as a convenience and should generally
/// only be used for literals in your source code. You should not use this
/// trait on numbers provided by end users. Namely, if the number provided
/// is not within Jiff's span limits, then these trait methods will panic.
/// Instead, use fallible mutator constructors like [`Span::try_days`]
/// or [`Span::try_seconds`].
///
/// # Example
///
/// ```
/// use jiff::ToSpan;
///
/// assert_eq!(5.days().to_string(), "P5d");
/// assert_eq!(5.days().hours(10).to_string(), "P5dT10h");
///
/// // Negation works and it doesn't matter where the sign goes. It can be
/// // applied to the span itself or to the integer.
/// assert_eq!((-5.days()).to_string(), "-P5d");
/// assert_eq!((-5).days().to_string(), "-P5d");
/// ```
///
/// # Example: alternative via span parsing
///
/// Another way of tersely building a `Span` value is by parsing a ISO 8601
/// duration string:
///
/// ```
/// use jiff::Span;
///
/// let span = "P5y2m15dT23h30m10s".parse::<Span>()?;
/// assert_eq!(
///     span,
///     Span::new().years(5).months(2).days(15).hours(23).minutes(30).seconds(10),
/// );
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
pub trait ToSpan: Sized {
    /// Create a new span from this integer in units of years.
    ///
    /// # Panics
    ///
    /// When `Span::new().years(self)` would panic.
    fn years(self) -> Span;

    /// Create a new span from this integer in units of months.
    ///
    /// # Panics
    ///
    /// When `Span::new().months(self)` would panic.
    fn months(self) -> Span;

    /// Create a new span from this integer in units of weeks.
    ///
    /// # Panics
    ///
    /// When `Span::new().weeks(self)` would panic.
    fn weeks(self) -> Span;

    /// Create a new span from this integer in units of days.
    ///
    /// # Panics
    ///
    /// When `Span::new().days(self)` would panic.
    fn days(self) -> Span;

    /// Create a new span from this integer in units of hours.
    ///
    /// # Panics
    ///
    /// When `Span::new().hours(self)` would panic.
    fn hours(self) -> Span;

    /// Create a new span from this integer in units of minutes.
    ///
    /// # Panics
    ///
    /// When `Span::new().minutes(self)` would panic.
    fn minutes(self) -> Span;

    /// Create a new span from this integer in units of seconds.
    ///
    /// # Panics
    ///
    /// When `Span::new().seconds(self)` would panic.
    fn seconds(self) -> Span;

    /// Create a new span from this integer in units of milliseconds.
    ///
    /// # Panics
    ///
    /// When `Span::new().milliseconds(self)` would panic.
    fn milliseconds(self) -> Span;

    /// Create a new span from this integer in units of microseconds.
    ///
    /// # Panics
    ///
    /// When `Span::new().microseconds(self)` would panic.
    fn microseconds(self) -> Span;

    /// Create a new span from this integer in units of nanoseconds.
    ///
    /// # Panics
    ///
    /// When `Span::new().nanoseconds(self)` would panic.
    fn nanoseconds(self) -> Span;

    /// Equivalent to `years()`, but reads better for singular units.
    #[inline]
    fn year(self) -> Span {
        self.years()
    }

    /// Equivalent to `months()`, but reads better for singular units.
    #[inline]
    fn month(self) -> Span {
        self.months()
    }

    /// Equivalent to `weeks()`, but reads better for singular units.
    #[inline]
    fn week(self) -> Span {
        self.weeks()
    }

    /// Equivalent to `days()`, but reads better for singular units.
    #[inline]
    fn day(self) -> Span {
        self.days()
    }

    /// Equivalent to `hours()`, but reads better for singular units.
    #[inline]
    fn hour(self) -> Span {
        self.hours()
    }

    /// Equivalent to `minutes()`, but reads better for singular units.
    #[inline]
    fn minute(self) -> Span {
        self.minutes()
    }

    /// Equivalent to `seconds()`, but reads better for singular units.
    #[inline]
    fn second(self) -> Span {
        self.seconds()
    }

    /// Equivalent to `milliseconds()`, but reads better for singular units.
    #[inline]
    fn millisecond(self) -> Span {
        self.milliseconds()
    }

    /// Equivalent to `microseconds()`, but reads better for singular units.
    #[inline]
    fn microsecond(self) -> Span {
        self.microseconds()
    }

    /// Equivalent to `nanoseconds()`, but reads better for singular units.
    #[inline]
    fn nanosecond(self) -> Span {
        self.nanoseconds()
    }
}

macro_rules! impl_to_span {
    ($ty:ty) => {
        impl ToSpan for $ty {
            #[inline]
            fn years(self) -> Span {
                Span::new().years(self)
            }
            #[inline]
            fn months(self) -> Span {
                Span::new().months(self)
            }
            #[inline]
            fn weeks(self) -> Span {
                Span::new().weeks(self)
            }
            #[inline]
            fn days(self) -> Span {
                Span::new().days(self)
            }
            #[inline]
            fn hours(self) -> Span {
                Span::new().hours(self)
            }
            #[inline]
            fn minutes(self) -> Span {
                Span::new().minutes(self)
            }
            #[inline]
            fn seconds(self) -> Span {
                Span::new().seconds(self)
            }
            #[inline]
            fn milliseconds(self) -> Span {
                Span::new().milliseconds(self)
            }
            #[inline]
            fn microseconds(self) -> Span {
                Span::new().microseconds(self)
            }
            #[inline]
            fn nanoseconds(self) -> Span {
                Span::new().nanoseconds(self)
            }
        }
    };
}

impl_to_span!(i8);
impl_to_span!(i16);
impl_to_span!(i32);
impl_to_span!(i64);

/// A way to refer to a single calendar or clock unit.
///
/// This type is principally used in APIs involving a [`Span`], which is a
/// duration of time. For example, routines like [`Zoned::until`] permit
/// specifying the largest unit of the span returned:
///
/// ```
/// use jiff::{Unit, Zoned};
///
/// let zdt1: Zoned = "2024-07-06 17:40-04[America/New_York]".parse()?;
/// let zdt2: Zoned = "2024-11-05 08:00-05[America/New_York]".parse()?;
/// let span = zdt1.until((Unit::Year, &zdt2))?;
/// assert_eq!(span.to_string(), "P3m29dT14h20m");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// But a `Unit` is also used in APIs for rounding datetimes themselves:
///
/// ```
/// use jiff::{Unit, Zoned};
///
/// let zdt: Zoned = "2024-07-06 17:44:22.158-04[America/New_York]".parse()?;
/// let nearest_minute = zdt.round(Unit::Minute)?;
/// assert_eq!(
///     nearest_minute.to_string(),
///     "2024-07-06T17:44:00-04:00[America/New_York]",
/// );
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Example: ordering
///
/// This example demonstrates that `Unit` has an ordering defined such that
/// bigger units compare greater than smaller units.
///
/// ```
/// use jiff::Unit;
///
/// assert!(Unit::Year > Unit::Nanosecond);
/// assert!(Unit::Day > Unit::Hour);
/// assert!(Unit::Hour > Unit::Minute);
/// assert!(Unit::Hour > Unit::Minute);
/// assert_eq!(Unit::Hour, Unit::Hour);
/// ```
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub enum Unit {
    /// A Gregorian calendar year. It usually has 365 days for non-leap years,
    /// and 366 days for leap years.
    Year = 9,
    /// A Gregorian calendar month. It usually has one of 28, 29, 30 or 31
    /// days.
    Month = 8,
    /// A week is 7 days that either begins on Sunday or Monday.
    Week = 7,
    /// A day is usually 24 hours, but some days may have different lengths
    /// due to time zone transitions.
    Day = 6,
    /// An hour is always 60 minutes.
    Hour = 5,
    /// A minute is always 60 seconds. (Jiff behaves as if leap seconds do not
    /// exist.)
    Minute = 4,
    /// A second is always 1,000 milliseconds.
    Second = 3,
    /// A millisecond is always 1,000 microseconds.
    Millisecond = 2,
    /// A microsecond is always 1,000 nanoseconds.
    Microsecond = 1,
    /// A nanosecond is the smallest granularity of time supported by Jiff.
    Nanosecond = 0,
}

impl Unit {
    /// Returns the next biggest unit, if one exists.
    pub(crate) fn next(&self) -> Option<Unit> {
        match *self {
            Unit::Year => None,
            Unit::Month => Some(Unit::Year),
            Unit::Week => Some(Unit::Month),
            Unit::Day => Some(Unit::Week),
            Unit::Hour => Some(Unit::Day),
            Unit::Minute => Some(Unit::Hour),
            Unit::Second => Some(Unit::Minute),
            Unit::Millisecond => Some(Unit::Second),
            Unit::Microsecond => Some(Unit::Millisecond),
            Unit::Nanosecond => Some(Unit::Microsecond),
        }
    }

    /// Returns the number of nanoseconds in this unit as a 128-bit integer.
    ///
    /// # Panics
    ///
    /// When this unit is definitively variable. That is, years, months or
    /// weeks.
    pub(crate) fn nanoseconds(self) -> NoUnits128 {
        match self {
            Unit::Nanosecond => Constant(1),
            Unit::Microsecond => t::NANOS_PER_MICRO,
            Unit::Millisecond => t::NANOS_PER_MILLI,
            Unit::Second => t::NANOS_PER_SECOND,
            Unit::Minute => t::NANOS_PER_MINUTE,
            Unit::Hour => t::NANOS_PER_HOUR,
            Unit::Day => t::NANOS_PER_CIVIL_DAY,
            unit => unreachable!("{unit:?} has no definitive time interval"),
        }
        .rinto()
    }

    /// Returns true when this unit is definitively variable.
    ///
    /// In effect, this is any unit bigger than 'day', because any such unit
    /// can vary in time depending on its reference point. A 'day' can as well,
    /// but we sorta special case 'day' to mean '24 hours' for cases where
    /// the user is dealing with civil time.
    pub(crate) fn is_definitively_variable(self) -> bool {
        matches!(self, Unit::Year | Unit::Month | Unit::Week)
    }

    /// A human readable singular description of this unit of time.
    pub(crate) fn singular(&self) -> &'static str {
        match *self {
            Unit::Year => "year",
            Unit::Month => "month",
            Unit::Week => "week",
            Unit::Day => "day",
            Unit::Hour => "hour",
            Unit::Minute => "minute",
            Unit::Second => "second",
            Unit::Millisecond => "millisecond",
            Unit::Microsecond => "microsecond",
            Unit::Nanosecond => "nanosecond",
        }
    }

    /// A human readable plural description of this unit of time.
    pub(crate) fn plural(&self) -> &'static str {
        match *self {
            Unit::Year => "years",
            Unit::Month => "months",
            Unit::Week => "weeks",
            Unit::Day => "days",
            Unit::Hour => "hours",
            Unit::Minute => "minutes",
            Unit::Second => "seconds",
            Unit::Millisecond => "milliseconds",
            Unit::Microsecond => "microseconds",
            Unit::Nanosecond => "nanoseconds",
        }
    }
}

#[cfg(test)]
impl Unit {
    fn from_usize(n: usize) -> Option<Unit> {
        match n {
            0 => Some(Unit::Nanosecond),
            1 => Some(Unit::Microsecond),
            2 => Some(Unit::Millisecond),
            3 => Some(Unit::Second),
            4 => Some(Unit::Minute),
            5 => Some(Unit::Hour),
            6 => Some(Unit::Day),
            7 => Some(Unit::Week),
            8 => Some(Unit::Month),
            9 => Some(Unit::Year),
            _ => None,
        }
    }
}

#[cfg(test)]
impl quickcheck::Arbitrary for Unit {
    fn arbitrary(g: &mut quickcheck::Gen) -> Unit {
        Unit::from_usize(usize::arbitrary(g) % 10).unwrap()
    }

    fn shrink(&self) -> alloc::boxed::Box<dyn Iterator<Item = Self>> {
        alloc::boxed::Box::new(
            (*self as usize)
                .shrink()
                .map(|n| Unit::from_usize(n % 10).unwrap()),
        )
    }
}

/// Options for [`Span::checked_add`] and [`Span::checked_sub`].
///
/// This type provides a way to ergonomically add two spans with an optional
/// relative datetime. Namely, a relative datetime is only needed when at least
/// one of the two spans being added (or subtracted) has a non-zero calendar
/// unit (years, months or weeks). Otherwise, an error will be returned.
///
/// When no relative datetime is provided, days are always 24 hours long.
///
/// The main way to construct values of this type is with its `From` trait
/// implementations:
///
/// * `From<Span> for SpanArithmetic` adds (or subtracts) the given span to the
/// receiver in [`Span::checked_add`] (or [`Span::checked_sub`]).
/// * `From<(Span, civil::Date)> for SpanArithmetic` adds (or subtracts)
/// the given span to the receiver in [`Span::checked_add`] (or
/// [`Span::checked_sub`]), relative to the given date. There are also `From`
/// implementations for `civil::DateTime` and `Zoned`.
///
/// # Example
///
/// ```
/// use jiff::ToSpan;
///
/// assert_eq!(1.hour().checked_add(30.minutes())?, 1.hour().minutes(30));
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Clone, Copy, Debug)]
pub struct SpanArithmetic<'a> {
    span: Span,
    relative: Option<SpanRelativeTo<'a>>,
}

impl<'a> SpanArithmetic<'a> {
    #[inline]
    fn new(span: Span) -> SpanArithmetic<'static> {
        SpanArithmetic { span, relative: None }
    }

    #[inline]
    fn relative<R: Into<SpanRelativeTo<'a>>>(
        self,
        relative: R,
    ) -> SpanArithmetic<'a> {
        SpanArithmetic { relative: Some(relative.into()), ..self }
    }

    #[inline]
    fn checked_add(self, span: Span) -> Result<Span, Error> {
        let (span1, span2) = (span, self.span);
        let unit = span1.largest_unit().max(span2.largest_unit());
        let start = match self.relative {
            Some(r) => {
                if !r.is_variable(unit) {
                    return span1.checked_add_invariant(unit, &span2);
                }
                r.to_relative()?
            }
            None => {
                if unit.is_definitively_variable() {
                    return Err(err!(
                        "using largest unit (which is '{unit}') in given span \
                         requires that a relative reference time be given, \
                         but none was provided",
                        unit = unit.singular(),
                    ));
                }
                return span1.checked_add_invariant(unit, &span2);
            }
        };
        let mid = start.checked_add(span1)?;
        let end = mid.checked_add(span2)?;
        start.until(unit, &end)
    }
}

impl From<Span> for SpanArithmetic<'static> {
    fn from(span: Span) -> SpanArithmetic<'static> {
        SpanArithmetic::new(span)
    }
}

impl<'a> From<&'a Span> for SpanArithmetic<'static> {
    fn from(span: &'a Span) -> SpanArithmetic<'static> {
        SpanArithmetic::new(*span)
    }
}

impl From<(Span, Date)> for SpanArithmetic<'static> {
    #[inline]
    fn from((span, date): (Span, Date)) -> SpanArithmetic<'static> {
        SpanArithmetic::from(span).relative(date)
    }
}

impl From<(Span, DateTime)> for SpanArithmetic<'static> {
    #[inline]
    fn from((span, datetime): (Span, DateTime)) -> SpanArithmetic<'static> {
        SpanArithmetic::from(span).relative(datetime)
    }
}

impl<'a> From<(Span, &'a Zoned)> for SpanArithmetic<'a> {
    #[inline]
    fn from((span, zoned): (Span, &'a Zoned)) -> SpanArithmetic<'a> {
        SpanArithmetic::from(span).relative(zoned)
    }
}

impl<'a> From<(&'a Span, Date)> for SpanArithmetic<'static> {
    #[inline]
    fn from((span, date): (&'a Span, Date)) -> SpanArithmetic<'static> {
        SpanArithmetic::from(span).relative(date)
    }
}

impl<'a> From<(&'a Span, DateTime)> for SpanArithmetic<'static> {
    #[inline]
    fn from(
        (span, datetime): (&'a Span, DateTime),
    ) -> SpanArithmetic<'static> {
        SpanArithmetic::from(span).relative(datetime)
    }
}

impl<'a, 'b> From<(&'a Span, &'b Zoned)> for SpanArithmetic<'b> {
    #[inline]
    fn from((span, zoned): (&'a Span, &'b Zoned)) -> SpanArithmetic<'b> {
        SpanArithmetic::from(span).relative(zoned)
    }
}

/// Options for [`Span::compare`].
///
/// This type provides a way to ergonomically compare two spans with an
/// optional relative datetime. Namely, a relative datetime is only needed when
/// at least one of the two spans being compared has a non-zero calendar unit
/// (years, months or weeks). Otherwise, an error will be returned.
///
/// When no relative datetime is provided, days are always 24 hours long.
///
/// The main way to construct values of this type is with its `From` trait
/// implementations:
///
/// * `From<Span> for SpanCompare` compares the given span to the receiver
/// in [`Span::compare`].
/// * `From<(Span, civil::Date)> for SpanCompare` compares the given span to
/// the receiver in [`Span::compare`], relative to the given date. There are
/// also `From` implementations for `civil::DateTime` and `Zoned`.
///
/// # Example
///
/// ```
/// use jiff::ToSpan;
///
/// let span1 = 3.hours();
/// let span2 = 180.minutes();
/// assert_eq!(span1.compare(span2)?, std::cmp::Ordering::Equal);
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Clone, Copy, Debug)]
pub struct SpanCompare<'a> {
    span: Span,
    relative: Option<SpanRelativeTo<'a>>,
}

impl<'a> SpanCompare<'a> {
    #[inline]
    fn new(span: Span) -> SpanCompare<'static> {
        SpanCompare { span, relative: None }
    }

    #[inline]
    fn relative<R: Into<SpanRelativeTo<'a>>>(
        self,
        relative: R,
    ) -> SpanCompare<'a> {
        SpanCompare { relative: Some(relative.into()), ..self }
    }

    fn compare(self, span: Span) -> Result<Ordering, Error> {
        let (span1, span2) = (span, self.span);
        let unit = span1.largest_unit().max(span2.largest_unit());
        let start = match self.relative {
            Some(r) => {
                if !r.is_variable(unit) {
                    let nanos1 = span1.to_invariant_nanoseconds();
                    let nanos2 = span2.to_invariant_nanoseconds();
                    return Ok(nanos1.cmp(&nanos2));
                }
                r.to_relative()?
            }
            None => {
                if unit.is_definitively_variable() {
                    return Err(err!(
                        "using largest unit (which is '{unit}') in given span \
                         requires that a relative reference time be given, \
                         but none was provided",
                        unit = unit.singular(),
                    ));
                }
                let nanos1 = span1.to_invariant_nanoseconds();
                let nanos2 = span2.to_invariant_nanoseconds();
                return Ok(nanos1.cmp(&nanos2));
            }
        };
        let end1 = start.checked_add(span1)?.to_nanosecond();
        let end2 = start.checked_add(span2)?.to_nanosecond();
        Ok(end1.cmp(&end2))
    }
}

impl From<Span> for SpanCompare<'static> {
    fn from(span: Span) -> SpanCompare<'static> {
        SpanCompare::new(span)
    }
}

impl<'a> From<&'a Span> for SpanCompare<'static> {
    fn from(span: &'a Span) -> SpanCompare<'static> {
        SpanCompare::new(*span)
    }
}

impl From<(Span, Date)> for SpanCompare<'static> {
    #[inline]
    fn from((span, date): (Span, Date)) -> SpanCompare<'static> {
        SpanCompare::from(span).relative(date)
    }
}

impl From<(Span, DateTime)> for SpanCompare<'static> {
    #[inline]
    fn from((span, datetime): (Span, DateTime)) -> SpanCompare<'static> {
        SpanCompare::from(span).relative(datetime)
    }
}

impl<'a> From<(Span, &'a Zoned)> for SpanCompare<'a> {
    #[inline]
    fn from((span, zoned): (Span, &'a Zoned)) -> SpanCompare<'a> {
        SpanCompare::from(span).relative(zoned)
    }
}

impl<'a> From<(&'a Span, Date)> for SpanCompare<'static> {
    #[inline]
    fn from((span, date): (&'a Span, Date)) -> SpanCompare<'static> {
        SpanCompare::from(span).relative(date)
    }
}

impl<'a> From<(&'a Span, DateTime)> for SpanCompare<'static> {
    #[inline]
    fn from((span, datetime): (&'a Span, DateTime)) -> SpanCompare<'static> {
        SpanCompare::from(span).relative(datetime)
    }
}

impl<'a, 'b> From<(&'a Span, &'b Zoned)> for SpanCompare<'b> {
    #[inline]
    fn from((span, zoned): (&'a Span, &'b Zoned)) -> SpanCompare<'b> {
        SpanCompare::from(span).relative(zoned)
    }
}

/// Options for [`Span::total`].
///
/// This type provides a way to ergonomically determine the number of a
/// particular unit in a span, with a potentially fractional component, with an
/// optional relative datetime. Namely, a relative datetime is only needed when
/// the span has a non-zero calendar unit (years, months or weeks). Otherwise,
/// an error will be returned.
///
/// When no relative datetime is provided, days are always 24 hours long.
///
/// The main way to construct values of this type is with its `From` trait
/// implementations:
///
/// * `From<Unit> for SpanTotal` computes a total for the given unit in the
/// receiver span for [`Span::total`].
/// * `From<(Unit, civil::Date)> for SpanTotal` computes a total for the given
/// unit in the receiver span for [`Span::total`], relative to the given date.
/// There are also `From` implementations for `civil::DateTime` and `Zoned`.
///
/// # Example
///
/// This example shows how to find the number of seconds in a particular span:
///
/// ```
/// use jiff::{ToSpan, Unit};
///
/// let span = 3.hours().minutes(10);
/// assert_eq!(span.total(Unit::Second)?, 11_400.0);
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Example: 24 hour days
///
/// This shows how to find the total number of 24 hour days in `123,456,789`
/// seconds.
///
/// ```
/// use jiff::{ToSpan, Unit};
///
/// let span = 123_456_789.seconds();
/// assert_eq!(span.total(Unit::Day)?, 1428.8980208333332);
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Example: DST is taken into account
///
/// The month of March 2024 in `America/New_York` had 31 days, but one of those
/// days was 23 hours long due a transition into daylight saving time:
///
/// ```
/// use jiff::{civil::date, ToSpan, Unit};
///
/// let span = 744.hours();
/// let relative = date(2024, 3, 1).intz("America/New_York")?;
/// // Because of the short day, 744 hours is actually a little *more* than
/// // 1 month starting from 2024-03-01.
/// assert_eq!(span.total((Unit::Month, &relative))?, 1.0013888888888889);
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// Now compare what happens when the relative datetime is civil and not
/// time zone aware:
///
/// ```
/// use jiff::{civil::date, ToSpan, Unit};
///
/// let span = 744.hours();
/// let relative = date(2024, 3, 1);
/// assert_eq!(span.total((Unit::Month, relative))?, 1.0);
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Clone, Copy, Debug)]
pub struct SpanTotal<'a> {
    unit: Unit,
    relative: Option<SpanRelativeTo<'a>>,
}

impl<'a> SpanTotal<'a> {
    #[inline]
    fn new(unit: Unit) -> SpanTotal<'static> {
        SpanTotal { unit, relative: None }
    }

    #[inline]
    fn relative<R: Into<SpanRelativeTo<'a>>>(
        self,
        relative: R,
    ) -> SpanTotal<'a> {
        SpanTotal { relative: Some(relative.into()), ..self }
    }

    fn total(self, span: Span) -> Result<f64, Error> {
        let max_unit = self.unit.max(span.largest_unit());
        let relative = match self.relative {
            Some(r) => {
                if !r.is_variable(max_unit) {
                    return Ok(self.total_invariant(span));
                }
                r.to_relative()?
            }
            None => {
                if max_unit.is_definitively_variable() {
                    return Err(err!(
                        "using unit '{unit}' requires that a relative \
                         reference time be given, but none was provided",
                        unit = max_unit.singular(),
                    ));
                }
                return Ok(self.total_invariant(span));
            }
        };
        let relspan = relative.into_relative_span(self.unit, span)?;
        if !relspan.kind.is_variable(self.unit) {
            return Ok(self.total_invariant(relspan.span));
        }

        assert!(self.unit >= Unit::Day);
        let sign = relspan.span.get_sign_ranged();
        let (relative_start, relative_end) = match relspan.kind {
            RelativeSpanKind::Civil { start, end } => {
                let start = Relative::Civil(start);
                let end = Relative::Civil(end);
                (start, end)
            }
            RelativeSpanKind::Zoned { start, end } => {
                let start = Relative::Zoned(start);
                let end = Relative::Zoned(end);
                (start, end)
            }
        };
        let (relative0, relative1) = clamp_relative_span(
            &relative_start,
            relspan.span.without_lower(self.unit),
            self.unit,
            sign.rinto(),
        )?;
        let denom = (relative1 - relative0).get() as f64;
        let numer = (relative_end.to_nanosecond() - relative0).get() as f64;
        let unit_val = relspan.span.get_units_ranged(self.unit).get() as f64;
        Ok(unit_val + (numer / denom) * (sign.get() as f64))
    }

    #[inline]
    fn total_invariant(&self, span: Span) -> f64 {
        assert!(self.unit <= Unit::Day);
        let nanos = span.to_invariant_nanoseconds();
        (nanos.get() as f64) / (self.unit.nanoseconds().get() as f64)
    }
}

impl From<Unit> for SpanTotal<'static> {
    #[inline]
    fn from(unit: Unit) -> SpanTotal<'static> {
        SpanTotal::new(unit)
    }
}

impl From<(Unit, Date)> for SpanTotal<'static> {
    #[inline]
    fn from((unit, date): (Unit, Date)) -> SpanTotal<'static> {
        SpanTotal::from(unit).relative(date)
    }
}

impl From<(Unit, DateTime)> for SpanTotal<'static> {
    #[inline]
    fn from((unit, datetime): (Unit, DateTime)) -> SpanTotal<'static> {
        SpanTotal::from(unit).relative(datetime)
    }
}

impl<'a> From<(Unit, &'a Zoned)> for SpanTotal<'a> {
    #[inline]
    fn from((unit, zoned): (Unit, &'a Zoned)) -> SpanTotal<'a> {
        SpanTotal::from(unit).relative(zoned)
    }
}

/// Options for [`Span::round`].
///
/// This type provides a way to configure the rounding of a span. This
/// includes setting the smallest unit (i.e., the unit to round), the
/// largest unit, the rounding increment, the rounding mode (e.g., "ceil" or
/// "truncate") and the datetime that the span is relative to.
///
/// `Span::round` accepts anything that implements `Into<SpanRound>`. There are
/// a few key trait implementations that make this convenient:
///
/// * `From<Unit> for SpanRound` will construct a rounding configuration where
/// the smallest unit is set to the one given.
/// * `From<(Unit, i64)> for SpanRound` will construct a rounding configuration
/// where the smallest unit and the rounding increment are set to the ones
/// given.
///
/// In order to set other options (like the largest unit, the rounding mode
/// and the relative datetime), one must explicitly create a `SpanRound` and
/// pass it to `Span::round`.
///
/// # Example
///
/// This example shows how to find how many full 3 month quarters are in a
/// particular span of time.
///
/// ```
/// use jiff::{civil::date, RoundMode, SpanRound, ToSpan, Unit};
///
/// let span1 = 10.months().days(15);
/// let round = SpanRound::new()
///     .smallest(Unit::Month)
///     .increment(3)
///     .mode(RoundMode::Trunc)
///     // A relative datetime must be provided when
///     // rounding involves calendar units.
///     .relative(date(2024, 1, 1));
/// let span2 = span1.round(round)?;
/// assert_eq!(span2.get_months() / 3, 3);
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Clone, Copy, Debug)]
pub struct SpanRound<'a> {
    largest: Option<Unit>,
    smallest: Unit,
    mode: RoundMode,
    increment: i64,
    relative: Option<SpanRelativeTo<'a>>,
}

impl<'a> SpanRound<'a> {
    /// Create a new default configuration for rounding a span via
    /// [`Span::round`].
    ///
    /// The default configuration does no rounding.
    #[inline]
    pub fn new() -> SpanRound<'static> {
        SpanRound {
            largest: None,
            smallest: Unit::Nanosecond,
            mode: RoundMode::HalfExpand,
            increment: 1,
            relative: None,
        }
    }

    /// Set the smallest units allowed in the span returned. These are the
    /// units that the span is rounded to.
    ///
    /// # Errors
    ///
    /// The smallest units must be no greater than the largest units. If this
    /// is violated, then rounding a span with this configuration will result
    /// in an error.
    ///
    /// If a smallest unit bigger than days is selected without a relative
    /// datetime reference point, then an error is returned when using this
    /// configuration with [`Span::round`].
    ///
    /// # Example
    ///
    /// A basic example that rounds to the nearest minute:
    ///
    /// ```
    /// use jiff::{ToSpan, Unit};
    ///
    /// let span = 15.minutes().seconds(46);
    /// assert_eq!(span.round(Unit::Minute)?, 16.minutes());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn smallest(self, unit: Unit) -> SpanRound<'a> {
        SpanRound { smallest: unit, ..self }
    }

    /// Set the largest units allowed in the span returned.
    ///
    /// When a largest unit is not specified, then it defaults to the largest
    /// non-zero unit that is at least as big as the configured smallest
    /// unit. For example, given a span of 2 months 17 hours, the default
    /// largest unit would be `Unit::Month`. The default implies that a span's
    /// units do not get "bigger" than what was given.
    ///
    /// Once a largest unit is set, there is no way to change this rounding
    /// configuration back to using the "automatic" default. Instead, callers
    /// must create a new configuration.
    ///
    /// If a largest unit is set and no other options are set, then the rounding
    /// operation can be said to be a "re-balancing." That is, the span won't
    /// lose precision, but the way in which it is expressed may change.
    ///
    /// # Errors
    ///
    /// The largest units, when set, must be at least as big as the smallest
    /// units (which defaults to [`Unit::Nanosecond`]). If this is violated,
    /// then rounding a span with this configuration will result in an error.
    ///
    /// If a largest unit bigger than days is selected without a relative
    /// datetime reference point, then an error is returned when using this
    /// configuration with [`Span::round`].
    ///
    /// # Example: re-balancing
    ///
    /// This shows how a span can be re-balanced without losing precision:
    ///
    /// ```
    /// use jiff::{SpanRound, ToSpan, Unit};
    ///
    /// let span = 86_401_123_456_789i64.nanoseconds();
    /// assert_eq!(
    ///     span.round(SpanRound::new().largest(Unit::Day))?,
    ///     1.day().seconds(1).milliseconds(123).microseconds(456).nanoseconds(789),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// If you need to use a largest unit bigger than days, then you must
    /// provide a relative datetime as a reference point (otherwise an error
    /// will occur):
    ///
    /// ```
    /// use jiff::{civil::date, SpanRound, ToSpan, Unit};
    ///
    /// let span = 3_968_000.seconds();
    /// let round = SpanRound::new()
    ///     .largest(Unit::Day)
    ///     .relative(date(2024, 7, 1));
    /// assert_eq!(
    ///     span.round(round)?,
    ///     45.days().hours(22).minutes(13).seconds(20),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: re-balancing while taking DST into account
    ///
    /// When given a zone aware relative datetime, rounding will even take
    /// DST into account:
    ///
    /// ```
    /// use jiff::{SpanRound, ToSpan, Unit, Zoned};
    ///
    /// let span = 2756.hours();
    /// let zdt = "2020-01-01T00:00+01:00[Europe/Rome]".parse::<Zoned>()?;
    /// let round = SpanRound::new().largest(Unit::Year).relative(&zdt);
    /// assert_eq!(span.round(round)?, 3.months().days(23).hours(21));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// Now compare with the same operation, but on a civil datetime (which is
    /// not aware of time zone):
    ///
    /// ```
    /// use jiff::{civil::DateTime, SpanRound, ToSpan, Unit};
    ///
    /// let span = 2756.hours();
    /// let dt = "2020-01-01T00:00".parse::<DateTime>()?;
    /// let round = SpanRound::new().largest(Unit::Year).relative(dt);
    /// assert_eq!(span.round(round)?, 3.months().days(23).hours(20));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// The result is 1 hour shorter. This is because, in the zone
    /// aware re-balancing, it accounts for the transition into DST at
    /// `2020-03-29T01:00Z`, which skips an hour. This makes the span one hour
    /// longer because one of the days in the span is actually only 23 hours
    /// long instead of 24 hours.
    #[inline]
    pub fn largest(self, unit: Unit) -> SpanRound<'a> {
        SpanRound { largest: Some(unit), ..self }
    }

    /// Set the rounding mode.
    ///
    /// This defaults to [`RoundMode::HalfExpand`], which makes rounding work
    /// like how you were taught in school.
    ///
    /// # Example
    ///
    /// A basic example that rounds to the nearest minute, but changing its
    /// rounding mode to truncation:
    ///
    /// ```
    /// use jiff::{RoundMode, SpanRound, ToSpan, Unit};
    ///
    /// let span = 15.minutes().seconds(46);
    /// assert_eq!(
    ///     span.round(SpanRound::new()
    ///         .smallest(Unit::Minute)
    ///         .mode(RoundMode::Trunc),
    ///     )?,
    ///     // The default round mode does rounding like
    ///     // how you probably learned in school, and would
    ///     // result in rounding up to 16 minutes. But we
    ///     // change it to truncation here, which makes it
    ///     // round down.
    ///     15.minutes(),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn mode(self, mode: RoundMode) -> SpanRound<'a> {
        SpanRound { mode, ..self }
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
    /// This shows how to round a span to the nearest 5 minute increment:
    ///
    /// ```
    /// use jiff::{ToSpan, Unit};
    ///
    /// let span = 4.hours().minutes(2).seconds(30);
    /// assert_eq!(span.round((Unit::Minute, 5))?, 4.hours().minutes(5));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn increment(self, increment: i64) -> SpanRound<'a> {
        SpanRound { increment, ..self }
    }

    /// Set the relative datetime to use when rounding a span.
    ///
    /// A relative datetime is only required when calendar units (units greater
    /// than days) are involved. This includes having calendar units in the
    /// original span, or calendar units in the configured smallest or largest
    /// unit. A relative datetime is required when calendar units are used
    /// because the duration of a particular calendar unit (like 1 month or 1
    /// year) is variable and depends on the date. For example, 1 month from
    /// 2024-01-01 is 31 days, but 1 month from 2024-02-01 is 29 days.
    ///
    /// A relative datetime is provided by anything that implements
    /// `Into<SpanRelativeTo>`. There are a few convenience trait
    /// implementations provided:
    ///
    /// * `From<&Zoned> for SpanRelativeTo` uses a zone aware datetime to do
    /// rounding. In this case, rounding will take time zone transitions into
    /// account. In particular, when using a zoned relative datetime, not all
    /// days are necessarily 24 hours.
    /// * `From<civil::DateTime> for SpanRelativeTo` uses a civil datetime. In
    /// this case, all days will be considered 24 hours long.
    /// * `From<civil::Date> for SpanRelativeTo` uses a civil date. In this
    /// case, all days will be considered 24 hours long.
    ///
    /// # Errors
    ///
    /// If rounding involves a calendar unit (units bigger than days) and no
    /// relative datetime is provided, then this configuration will lead to
    /// an error when used with [`Span::round`].
    ///
    /// # Example
    ///
    /// This example shows very precisely how a DST transition can impact
    /// rounding and re-balancing. For example, consider the day `2024-11-03`
    /// in `America/New_York`. On this day, the 1 o'clock hour was repeated,
    /// making the day 24 hours long. This will be taken into account when
    /// rounding if a zoned datetime is provided as a reference point:
    ///
    /// ```
    /// use jiff::{SpanRound, ToSpan, Unit, Zoned};
    ///
    /// let zdt = "2024-11-03T00-04[America/New_York]".parse::<Zoned>()?;
    /// let round = SpanRound::new().largest(Unit::Hour).relative(&zdt);
    /// assert_eq!(1.day().round(round)?, 25.hours());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// And similarly for `2024-03-10`, where the 2 o'clock hour was skipped
    /// entirely:
    ///
    /// ```
    /// use jiff::{SpanRound, ToSpan, Unit, Zoned};
    ///
    /// let zdt = "2024-03-10T00-05[America/New_York]".parse::<Zoned>()?;
    /// let round = SpanRound::new().largest(Unit::Hour).relative(&zdt);
    /// assert_eq!(1.day().round(round)?, 23.hours());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn relative<R: Into<SpanRelativeTo<'a>>>(
        self,
        relative: R,
    ) -> SpanRound<'a> {
        SpanRound { relative: Some(relative.into()), ..self }
    }

    /// Returns the configured smallest unit on this round configuration.
    #[inline]
    pub(crate) fn get_smallest(&self) -> Unit {
        self.smallest
    }

    /// Returns the configured largest unit on this round configuration.
    #[inline]
    pub(crate) fn get_largest(&self) -> Option<Unit> {
        self.largest
    }

    /// Returns true only when rounding a span *may* change it. When it
    /// returns false, and if the span is already balanced according to
    /// the largest unit in this round configuration, then it is guaranteed
    /// that rounding is a no-op.
    ///
    /// This is useful to avoid rounding calls after doing span arithmetic
    /// on datetime types. This works because the "largest" unit is used to
    /// construct a balanced span for the difference between two datetimes.
    /// So we already know the span has been balanced. If this weren't the
    /// case, then the largest unit being different from the one in the span
    /// could result in rounding making a change. (And indeed, in the general
    /// case of span rounding below, we do a more involved check for this.)
    #[inline]
    pub(crate) fn rounding_may_change_span_ignore_largest(&self) -> bool {
        self.smallest > Unit::Nanosecond || self.increment > 1
    }

    /// Does the actual span rounding.
    fn round(&self, span: Span) -> Result<Span, Error> {
        let existing_largest = span.largest_unit();
        let mode = self.mode;
        let smallest = self.smallest;
        let largest =
            self.largest.unwrap_or_else(|| smallest.max(existing_largest));
        let max = existing_largest.max(largest);
        let increment = increment::for_span(smallest, self.increment)?;
        if largest < smallest {
            return Err(err!(
                "largest unit ('{largest}') cannot be smaller than \
                 smallest unit ('{smallest}')",
                largest = largest.singular(),
                smallest = smallest.singular(),
            ));
        }
        // Now that we've got our configuration, we can actually short circuit
        // if we know rounding will never change our span.
        // if self.smallest == Unit::Nanosecond
        // && largest == existing_largest
        // && self.increment == 1
        // {
        // return Ok(span);
        // }
        let relative = match self.relative {
            Some(ref r) => {
                // If our reference point is civil time, then its units are
                // invariant as long as we are using day-or-lower everywhere.
                // That is, the length of the duration is independent of the
                // reference point. In which case, rounding is a simple matter
                // of converting the span to a number of nanoseconds and then
                // rounding that.
                if !r.is_variable(max) {
                    return Ok(round_span_invariant(
                        span, smallest, largest, increment, mode,
                    )?);
                }
                r.to_relative()?
            }
            None => {
                // This is only okay if none of our units are above 'day'.
                // That is, a reference point is only necessary when there is
                // no reasonable invariant interpretation of the span. And this
                // is only true when everything is less than 'day'.
                if smallest.is_definitively_variable() {
                    return Err(err!(
                        "using unit '{unit}' in round option 'smallest' \
                         requires that a relative reference time be given, \
                         but none was provided",
                        unit = smallest.singular(),
                    ));
                }
                if let Some(largest) = self.largest {
                    if largest.is_definitively_variable() {
                        return Err(err!(
                            "using unit '{unit}' in round option 'largest' \
                             requires that a relative reference time be \
                             given, but none was provided",
                            unit = largest.singular(),
                        ));
                    }
                }
                if existing_largest.is_definitively_variable() {
                    return Err(err!(
                        "using largest unit (which is '{unit}') in given span \
                         requires that a relative reference time be given, \
                         but none was provided",
                        unit = existing_largest.singular(),
                    ));
                }
                assert!(max <= Unit::Day);
                return Ok(round_span_invariant(
                    span, smallest, largest, increment, mode,
                )?);
            }
        };
        relative.round(span, smallest, largest, increment, mode)
    }
}

impl Default for SpanRound<'static> {
    fn default() -> SpanRound<'static> {
        SpanRound::new()
    }
}

impl From<Unit> for SpanRound<'static> {
    fn from(unit: Unit) -> SpanRound<'static> {
        SpanRound::default().smallest(unit)
    }
}

impl From<(Unit, i64)> for SpanRound<'static> {
    fn from((unit, increment): (Unit, i64)) -> SpanRound<'static> {
        SpanRound::default().smallest(unit).increment(increment)
    }
}

/// A relative datetime for use with [`Span`] APIs.
///
/// A relative datetime can be one of the following: [`civil::Date`](Date),
/// [`civil::DateTime`](DateTime) or [`Zoned`]. It can be constructed from any
/// of the preceding types via `From` trait implementations.
///
/// A relative datetime is used to indicate how the calendar units of a `Span`
/// should be interpreted. For example, the span "1 month" does not have a
/// fixed meaning. One month from `2024-03-01` is 31 days, but one month from
/// `2024-04-01` is 30 days. Similar for years.
///
/// When a relative datetime in time zone aware (i.e., it is a `Zoned`), then
/// a `Span` will also consider its day units to be variable in length. For
/// example, `2024-03-10` in `America/New_York` was only 23 hours long, where
/// as `2024-11-03` in `America/New_York` was 25 hours long. When a relative
/// datetime is civil, then days are considered to always be of a fixed 24
/// hour length.
///
/// This type is principally used as an input to one of several different
/// [`Span`] APIs:
///
/// * [`Span::round`] rounds spans. A relative datetime is necessary when
/// dealing with calendar units. (But spans without calendar units can be
/// rounded without providing a relative datetime.)
/// * Span arithmetic via [`Span::checked_add`] and [`Span::checked_sub`].
/// A relative datetime is needed when adding or subtracting spans with
/// calendar units.
/// * Span comarisons via [`Span::compare`] require a relative datetime when
/// comparing spans with calendar units.
/// * Computing the "total" duration as a single floating point number via
/// [`Span::total`] also requires a relative datetime when dealing with
/// calendar units.
///
/// # Example
///
/// This example shows how to round a span with larger calendar units to
/// smaller units:
///
/// ```
/// use jiff::{SpanRound, ToSpan, Unit, Zoned};
///
/// let zdt: Zoned = "2012-01-01[Antarctica/Troll]".parse()?;
/// let round = SpanRound::new().largest(Unit::Day).relative(&zdt);
/// assert_eq!(1.year().round(round)?, 366.days());
///
/// // If you tried this without a relative datetime, it would fail:
/// let round = SpanRound::new().largest(Unit::Day);
/// assert!(1.year().round(round).is_err());
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Clone, Copy, Debug)]
pub struct SpanRelativeTo<'a> {
    kind: SpanRelativeToKind<'a>,
}

impl<'a> SpanRelativeTo<'a> {
    /// Returns true when the given unit is variable relative to this reference
    /// point.
    ///
    /// In effect, days and greater are variable when the reference point has
    /// a time zone. Otherwise, only weeks and greater are variable.
    fn is_variable(&self, unit: Unit) -> bool {
        if unit.is_definitively_variable() {
            return true;
        }
        unit == Unit::Day
            && matches!(self.kind, SpanRelativeToKind::Zoned { .. })
    }

    /// Converts this public API relative datetime into a more versatile
    /// internal representation of the same concept.
    ///
    /// Basically, the internal `Relative` type is `Cow` which means it isn't
    /// `Copy`. But it can present a more uniform API. The public API type
    /// doesn't have `Cow` so that it can be `Copy`.
    ///
    /// We also take this opportunity to attach some convenient data, such
    /// as a timestamp when the relative datetime type is civil.
    ///
    /// # Errors
    ///
    /// If there was a problem doing this conversion, then an error is
    /// returned. In practice, this only occurs for a civil datetime near the
    /// civil datetime minimum and maximum values.
    fn to_relative(&self) -> Result<Relative<'a>, Error> {
        match self.kind {
            SpanRelativeToKind::Civil(dt) => {
                Ok(Relative::Civil(RelativeCivil::new(dt)?))
            }
            SpanRelativeToKind::Zoned(zdt) => {
                Ok(Relative::Zoned(RelativeZoned {
                    zoned: Cow::Borrowed(zdt),
                }))
            }
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum SpanRelativeToKind<'a> {
    Civil(DateTime),
    Zoned(&'a Zoned),
}

impl<'a> From<&'a Zoned> for SpanRelativeTo<'a> {
    fn from(zdt: &'a Zoned) -> SpanRelativeTo<'a> {
        SpanRelativeTo { kind: SpanRelativeToKind::Zoned(zdt) }
    }
}

impl From<DateTime> for SpanRelativeTo<'static> {
    fn from(dt: DateTime) -> SpanRelativeTo<'static> {
        SpanRelativeTo { kind: SpanRelativeToKind::Civil(dt) }
    }
}

impl From<Date> for SpanRelativeTo<'static> {
    fn from(date: Date) -> SpanRelativeTo<'static> {
        let dt = DateTime::from_parts(date, Time::midnight());
        SpanRelativeTo { kind: SpanRelativeToKind::Civil(dt) }
    }
}

impl<'a> core::fmt::Display for SpanRelativeToKind<'a> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match *self {
            SpanRelativeToKind::Civil(dt) => core::fmt::Display::fmt(&dt, f),
            SpanRelativeToKind::Zoned(zdt) => core::fmt::Display::fmt(zdt, f),
        }
    }
}

/// An internal abstraction for managing a relative datetime for use in some
/// `Span` APIs.
///
/// This is effectively the same as a `SpanRelativeTo`, but uses a `Cow<Zoned>`
/// instead of a `&Zoned`. This makes it non-`Copy`, but allows us to craft a
/// more uniform API. (i.e., `relative + span = relative` instead of `relative
/// + span = owned_relative` or whatever.) Note that the `Copy` impl on
/// `SpanRelativeTo` means it has to accept a `&Zoned`. It can't ever take a
/// `Zoned` since it is non-Copy.
///
/// NOTE: Separately from above, I think it's plausible that this type could be
/// designed a bit differently. Namely, something like this:
///
/// ```text
/// struct Relative<'a> {
///     tz: Option<&'a TimeZone>,
///     dt: DateTime,
///     ts: Timestamp,
/// }
/// ```
///
/// That is, we do zone aware stuff but without an actual `Zoned` type. But I
/// think in order to make that work, we would need to expose most of the
/// `Zoned` API as functions on its component types (DateTime, Timestamp and
/// TimeZone). I think we are likely to want to do that for public API reasons,
/// but I'd like to resist it since I think it will add a lot of complexity.
/// Or maybe we need a `Unzoned` type that is `DateTime` and `Timestamp`, but
/// requires passing the time zone in to each of its methods. That might work
/// quite well, even if it was just an internal type.
///
/// Anyway, I'm not 100% sure the above would work, but I think it would. It
/// would be nicer because everything would be `Copy` all the time. We'd never
/// need a `Cow<TimeZone>` for example, because we never need to change or
/// create a new time zone.
#[derive(Clone, Debug)]
enum Relative<'a> {
    Civil(RelativeCivil),
    Zoned(RelativeZoned<'a>),
}

impl<'a> Relative<'a> {
    /// Adds the given span to this relative datetime.
    ///
    /// This defers to either [`DateTime::checked_add`] or
    /// [`Zoned::checked_add`], depending on the type of relative datetime.
    ///
    /// The `Relative` datetime returned is guaranteed to have the same
    /// internal datetie type as `self`.
    ///
    /// # Errors
    ///
    /// This returns an error in the same cases as the underlying checked
    /// arithmetic APIs. In general, this occurs when adding the given `span`
    /// would result in overflow.
    fn checked_add(&self, span: Span) -> Result<Relative, Error> {
        match *self {
            Relative::Civil(dt) => Ok(Relative::Civil(dt.checked_add(span)?)),
            Relative::Zoned(ref zdt) => {
                Ok(Relative::Zoned(zdt.checked_add(span)?))
            }
        }
    }

    /// Returns the span of time from this relative datetime to the one given,
    /// with units as large as `largest`.
    ///
    /// # Errors
    ///
    /// This returns an error in the same cases as when the underlying
    /// [`DateTime::until`] or [`Zoned::until`] fail. Because this doesn't
    /// set or expose any rounding configuration, this can generally only
    /// occur when `largest` is `Unit::Nanosecond` and the span of time
    /// between `self` and `other` is too big to represent as a 64-bit integer
    /// nanosecond count.
    ///
    /// # Panics
    ///
    /// This panics if `self` and `other` are different internal datetime
    /// types. For example, if `self` was a civil datetime and `other` were
    /// a zoned datetime.
    fn until(&self, largest: Unit, other: &Relative) -> Result<Span, Error> {
        match (self, other) {
            (&Relative::Civil(ref dt1), &Relative::Civil(ref dt2)) => {
                dt1.until(largest, dt2)
            }
            (&Relative::Zoned(ref zdt1), &Relative::Zoned(ref zdt2)) => {
                zdt1.until(largest, zdt2)
            }
            // This would be bad if `Relative` were a public API, but in
            // practice, this case never occurs because we don't mixup our
            // `Relative` datetime types.
            _ => unreachable!(),
        }
    }

    /// Converts this relative datetime to a nanosecond in UTC time.
    ///
    /// # Errors
    ///
    /// If there was a problem doing this conversion, then an error is
    /// returned. In practice, this only occurs for a civil datetime near the
    /// civil datetime minimum and maximum values.
    fn to_nanosecond(&self) -> NoUnits128 {
        match *self {
            Relative::Civil(dt) => dt.timestamp.as_nanosecond_ranged().rinto(),
            Relative::Zoned(ref zdt) => {
                zdt.zoned.timestamp().as_nanosecond_ranged().rinto()
            }
        }
    }

    /// Create a balanced span of time relative to this datetime.
    ///
    /// The relative span returned has the same internal datetime type
    /// (civil or zoned) as this relative datetime.
    ///
    /// # Errors
    ///
    /// This returns an error when the span in this range cannot be
    /// represented. In general, this only occurs when asking for largest units
    /// of `Unit::Nanosecond` *and* when the span is too big to fit into a
    /// 64-bit nanosecond count.
    ///
    /// This can also return an error in other extreme cases, such as when
    /// adding the given span to this relative datetime results in overflow,
    /// or if this relative datetime is a civil datetime and it couldn't be
    /// converted to a timestamp in UTC.
    fn into_relative_span(
        self,
        largest: Unit,
        span: Span,
    ) -> Result<RelativeSpan<'a>, Error> {
        let kind = match self {
            Relative::Civil(start) => {
                let end = start.checked_add(span)?;
                RelativeSpanKind::Civil { start, end }
            }
            Relative::Zoned(start) => {
                let end = start.checked_add(span)?;
                RelativeSpanKind::Zoned { start, end }
            }
        };
        let relspan = kind.into_relative_span(largest)?;
        if span.get_sign_ranged() != 0
            && relspan.span.get_sign_ranged() != 0
            && span.get_sign_ranged() != relspan.span.get_sign_ranged()
        {
            // I haven't quite figured out when this case is hit. I think it's
            // actually impossible right? Balancing a duration should not flip
            // the sign.
            //
            // ref: https://github.com/fullcalendar/temporal-polyfill/blob/9e001042864394247181d1a5d591c18057ce32d2/packages/temporal-polyfill/src/internal/durationMath.ts#L236-L238
            unreachable!(
                "balanced span should have same sign as original span"
            )
        }
        Ok(relspan)
    }

    /// Rounds the given span using the given rounding configuration.
    fn round(
        self,
        span: Span,
        smallest: Unit,
        largest: Unit,
        increment: NoUnits128,
        mode: RoundMode,
    ) -> Result<Span, Error> {
        let relspan = self.into_relative_span(largest, span)?;
        if relspan.span.get_sign_ranged() == 0 {
            return Ok(relspan.span);
        }
        let nudge = match relspan.kind {
            RelativeSpanKind::Civil { start, end } => {
                if smallest > Unit::Day {
                    Nudge::relative_calendar(
                        relspan.span,
                        &Relative::Civil(start),
                        &Relative::Civil(end),
                        smallest,
                        increment,
                        mode,
                    )?
                } else {
                    let relative_end = end.timestamp.as_nanosecond_ranged();
                    Nudge::relative_invariant(
                        relspan.span,
                        relative_end.rinto(),
                        smallest,
                        largest,
                        increment,
                        mode,
                    )?
                }
            }
            RelativeSpanKind::Zoned { ref start, ref end } => {
                if smallest >= Unit::Day {
                    Nudge::relative_calendar(
                        relspan.span,
                        // FIXME: Find a way to drop these clones.
                        &Relative::Zoned(start.clone()),
                        &Relative::Zoned(end.clone()),
                        smallest,
                        increment,
                        mode,
                    )?
                } else if largest >= Unit::Day {
                    // This is a special case for zoned datetimes when rounding
                    // could bleed into variable units.
                    Nudge::relative_zoned_time(
                        relspan.span,
                        start,
                        smallest,
                        increment,
                        mode,
                    )?
                } else {
                    // Otherwise, rounding is the same as civil datetime.
                    let relative_end =
                        end.zoned.timestamp().as_nanosecond_ranged();
                    Nudge::relative_invariant(
                        relspan.span,
                        relative_end.rinto(),
                        smallest,
                        largest,
                        increment,
                        mode,
                    )?
                }
            }
        };
        nudge.bubble(&relspan, smallest, largest)
    }
}

/// A balanced span between a range of civil or zoned datetimes.
///
/// The span is always balanced up to a certain unit as given to
/// `RelativeSpanKind::into_relative_span`.
#[derive(Clone, Debug)]
struct RelativeSpan<'a> {
    span: Span,
    kind: RelativeSpanKind<'a>,
}

/// A civil or zoned datetime range of time.
#[derive(Clone, Debug)]
enum RelativeSpanKind<'a> {
    Civil { start: RelativeCivil, end: RelativeCivil },
    Zoned { start: RelativeZoned<'a>, end: RelativeZoned<'a> },
}

impl<'a> RelativeSpanKind<'a> {
    /// Returns true when the given unit is variable relative to this reference
    /// span.
    ///
    /// In effect, days and greater are variable when the reference point has
    /// a time zone. Otherwise, only weeks and greater are variable.
    fn is_variable(&self, unit: Unit) -> bool {
        if unit.is_definitively_variable() {
            return true;
        }
        unit == Unit::Day && matches!(*self, RelativeSpanKind::Zoned { .. })
    }

    /// Create a balanced `RelativeSpan` from this range of time.
    ///
    /// # Errors
    ///
    /// This returns an error when the span in this range cannot be
    /// represented. In general, this only occurs when asking for largest units
    /// of `Unit::Nanosecond` *and* when the span is too big to fit into a
    /// 64-bit nanosecond count.
    fn into_relative_span(
        self,
        largest: Unit,
    ) -> Result<RelativeSpan<'a>, Error> {
        let span = match self {
            RelativeSpanKind::Civil { ref start, ref end } => start
                .datetime
                .until((largest, end.datetime))
                .with_context(|| {
                    err!(
                        "failed to get span between {start} and {end} \
                         with largest unit as {unit}",
                        start = start.datetime,
                        end = end.datetime,
                        unit = largest.plural(),
                    )
                })?,
            RelativeSpanKind::Zoned { ref start, ref end } => start
                .zoned
                .until((largest, &*end.zoned))
                .with_context(|| {
                    err!(
                        "failed to get span between {start} and {end} \
                         with largest unit as {unit}",
                        start = start.zoned,
                        end = end.zoned,
                        unit = largest.plural(),
                    )
                })?,
        };
        Ok(RelativeSpan { span, kind: self })
    }
}

/// A wrapper around a civil datetime and a timestamp corresponding to that
/// civil datetime in UTC.
///
/// Haphazardly interpreting a civil datetime in UTC is an odd and *usually*
/// incorrect thing to do. But the way we use it here is basically just to give
/// it an "anchoring" point such that we can represent it using a single
/// integer for rounding purposes. It is only used in a context *relative* to
/// another civil datetime interpreted in UTC. In this fashion, the selection
/// of UTC specifically doesn't really matter. We could use any time zone.
/// (Although, it must be a time zone without any transitions, otherwise we
/// could wind up with time zone aware results in a context where that would
/// be unexpected since this is civil time.)
#[derive(Clone, Copy, Debug)]
struct RelativeCivil {
    datetime: DateTime,
    timestamp: Timestamp,
}

impl RelativeCivil {
    /// Creates a new relative wrapper around the given civil datetime.
    ///
    /// This wrapper bundles a timestamp for the given datetime by interpreting
    /// it as being in UTC. This is an "odd" thing to do, but it's only used
    /// in the context of determining the length of time between two civil
    /// datetimes. So technically, any time zone without transitions could be
    /// used.
    ///
    /// # Errors
    ///
    /// This returns an error if the datetime could not be converted to a
    /// timestamp. This only occurs near the minimum and maximum civil datetime
    /// values.
    fn new(datetime: DateTime) -> Result<RelativeCivil, Error> {
        let timestamp = datetime
            .to_zoned(TimeZone::UTC)
            .with_context(|| {
                err!("failed to convert {datetime} to timestamp")
            })?
            .timestamp();
        Ok(RelativeCivil { datetime, timestamp })
    }

    /// Returns the result of [`DateTime::checked_add`].
    ///
    /// # Errors
    ///
    /// Returns an error in the same cases as `DateTime::checked_add`. That is,
    /// when adding the span to this zoned datetime would overflow.
    ///
    /// This also returns an error if the resulting datetime could not be
    /// converted to a timestamp in UTC. This only occurs near the minimum and
    /// maximum datetime values.
    fn checked_add(&self, span: Span) -> Result<RelativeCivil, Error> {
        let datetime = self.datetime.checked_add(span).with_context(|| {
            err!("failed to add {span} to {dt}", dt = self.datetime)
        })?;
        let timestamp = datetime
            .to_zoned(TimeZone::UTC)
            .with_context(|| {
                err!("failed to convert {datetime} to timestamp")
            })?
            .timestamp();
        Ok(RelativeCivil { datetime, timestamp })
    }

    /// Returns the result of [`DateTime::until`].
    ///
    /// # Errors
    ///
    /// Returns an error in the same cases as `DateTime::until`. That is, when
    /// the span for the given largest unit cannot be represented. This can
    /// generally only happen when `largest` is `Unit::Nanosecond` and the span
    /// cannot be represented as a 64-bit integer of nanoseconds.
    fn until(
        &self,
        largest: Unit,
        other: &RelativeCivil,
    ) -> Result<Span, Error> {
        self.datetime.until((largest, other.datetime)).with_context(|| {
            err!(
                "failed to get span between {dt1} and {dt2} \
                 with largest unit as {unit}",
                unit = largest.plural(),
                dt1 = self.datetime,
                dt2 = other.datetime,
            )
        })
    }
}

/// A simple wrapper around a possibly borrowed `Zoned`.
#[derive(Clone, Debug)]
struct RelativeZoned<'a> {
    zoned: Cow<'a, Zoned>,
}

impl<'a> RelativeZoned<'a> {
    /// Returns the result of [`Zoned::checked_add`].
    ///
    /// # Errors
    ///
    /// Returns an error in the same cases as `Zoned::checked_add`. That is,
    /// when adding the span to this zoned datetime would overflow.
    fn checked_add(
        &self,
        span: Span,
    ) -> Result<RelativeZoned<'static>, Error> {
        let zoned = self.zoned.checked_add(span).with_context(|| {
            err!("failed to add {span} to {zoned}", zoned = self.zoned)
        })?;
        Ok(RelativeZoned { zoned: Cow::Owned(zoned) })
    }

    /// Returns the result of [`Zoned::until`].
    ///
    /// # Errors
    ///
    /// Returns an error in the same cases as `Zoned::until`. That is, when
    /// the span for the given largest unit cannot be represented. This can
    /// generally only happen when `largest` is `Unit::Nanosecond` and the span
    /// cannot be represented as a 64-bit integer of nanoseconds.
    fn until(
        &self,
        largest: Unit,
        other: &RelativeZoned<'a>,
    ) -> Result<Span, Error> {
        self.zoned.until((largest, &*other.zoned)).with_context(|| {
            err!(
                "failed to get span between {zdt1} and {zdt2} \
                 with largest unit as {unit}",
                unit = largest.plural(),
                zdt1 = self.zoned,
                zdt2 = other.zoned,
            )
        })
    }
}

// The code below is the "core" rounding logic for spans. It was greatly
// inspired by this gist[1] and the fullcalendar Temporal polyfill[2]. In
// particular, the algorithm implemented below is a major simplification from
// how Temporal used to work[3]. Parts of it are still in rough and unclear
// shape IMO.
//
// [1]: https://gist.github.com/arshaw/36d3152c21482bcb78ea2c69591b20e0
// [2]: https://github.com/fullcalendar/temporal-polyfill
// [3]: https://github.com/tc39/proposal-temporal/issues/2792

/// The result of a span rounding strategy. There are three:
///
/// * Rounding spans relative to civil datetimes using only invariant
/// units (days or less). This is achieved by converting the span to a simple
/// integer number of nanoseconds and then rounding that.
/// * Rounding spans relative to either a civil datetime or a zoned datetime
/// where rounding might involve changing non-uniform units. That is, when
/// the smallest unit is greater than days for civil datetimes and greater
/// than hours for zoned datetimes.
/// * Rounding spans relative to a zoned datetime whose smallest unit is
/// less than days.
///
/// Each of these might produce a bottom heavy span that needs to be
/// re-balanced. This type represents that result via one of three constructors
/// corresponding to each of the above strategies, and then provides a routine
/// for rebalancing via "bubbling."
#[derive(Debug)]
struct Nudge {
    /// A possibly bottom heavy rounded span.
    span: Span,
    /// The nanosecond timestamp corresponding to `relative + span`, where
    /// `span` is the (possibly bottom heavy) rounded span.
    rounded_relative_end: NoUnits128,
    /// Whether rounding may have created a bottom heavy span such that a
    /// calendar unit might need to be incremented after re-balancing smaller
    /// units.
    grew_big_unit: bool,
}

impl Nudge {
    /// Performs rounding on the given span limited to invariant units.
    ///
    /// For civil datetimes, this means the smallest unit must be days or less,
    /// but the largest unit can be bigger. For zoned datetimes, this means
    /// that *both* the largest and smallest unit must be hours or less. This
    /// is because zoned datetimes with rounding that can spill up to days
    /// requires special handling.
    ///
    /// It works by converting the span to a single integer number of
    /// nanoseconds, rounding it and then converting back to a span.
    fn relative_invariant(
        balanced: Span,
        relative_end: NoUnits128,
        smallest: Unit,
        largest: Unit,
        increment: NoUnits128,
        mode: RoundMode,
    ) -> Result<Nudge, Error> {
        // Ensures this is only called when rounding invariant units.
        assert!(smallest <= Unit::Day);

        let sign = balanced.get_sign_ranged();
        let balanced_nanos = balanced.to_invariant_nanoseconds();
        let rounded_nanos = mode.round_by_unit_in_nanoseconds(
            balanced_nanos,
            smallest,
            increment,
        );
        let span = Span::from_invariant_nanoseconds(largest, rounded_nanos)
            .with_context(|| {
                err!(
                    "failed to convert rounded nanoseconds {rounded_nanos} \
                     to span for largest unit as {unit}",
                    unit = largest.plural(),
                )
            })?
            .years_ranged(balanced.get_years_ranged())
            .months_ranged(balanced.get_months_ranged())
            .weeks_ranged(balanced.get_weeks_ranged());

        let diff_nanos = rounded_nanos - balanced_nanos;
        let diff_days = rounded_nanos.div_ceil(t::NANOS_PER_CIVIL_DAY)
            - balanced_nanos.div_ceil(t::NANOS_PER_CIVIL_DAY);
        let grew_big_unit = diff_days.signum() == sign;
        let rounded_relative_end = relative_end + diff_nanos;
        Ok(Nudge { span, rounded_relative_end, grew_big_unit })
    }

    /// Performs rounding on the given span where the smallest unit configured
    /// implies that rounding will cover calendar or "non-uniform" units. (That
    /// is, units whose length can change based on the relative datetime.)
    fn relative_calendar(
        balanced: Span,
        relative_start: &Relative<'_>,
        relative_end: &Relative<'_>,
        smallest: Unit,
        increment: NoUnits128,
        mode: RoundMode,
    ) -> Result<Nudge, Error> {
        #[cfg(not(feature = "std"))]
        use crate::util::libm::F64;

        assert!(smallest >= Unit::Day);
        let sign = balanced.get_sign_ranged();
        let truncated = increment
            * balanced.get_units_ranged(smallest).div_ceil(increment);
        let span = balanced
            .without_lower(smallest)
            .try_units_ranged(smallest, truncated)
            .with_context(|| {
                err!(
                    "failed to set {unit} to {truncated} on span {balanced}",
                    unit = smallest.singular()
                )
            })?;
        let (relative0, relative1) = clamp_relative_span(
            relative_start,
            span,
            smallest,
            NoUnits::try_rfrom("increment", increment)?
                .try_checked_mul("signed increment", sign)?,
        )?;

        // FIXME: This is brutal. This is the only non-optional floating point
        // used so far in Jiff. We do expose floating point for things like
        // `Span::total`, but that's optional and not a core part of Jiff's
        // functionality. This is in the core part of Jiff's span rounding...
        let denom = (relative1 - relative0).get() as f64;
        let numer = (relative_end.to_nanosecond() - relative0).get() as f64;
        let exact = (truncated.get() as f64)
            + (numer / denom) * (sign.get() as f64) * (increment.get() as f64);
        let rounded = mode.round_float(exact, increment);
        let grew_big_unit =
            ((rounded.get() as f64) - exact).signum() == (sign.get() as f64);

        let span =
            span.try_units_ranged(smallest, rounded).with_context(|| {
                err!(
                    "failed to set {unit} to {truncated} on span {span}",
                    unit = smallest.singular()
                )
            })?;
        let rounded_relative_end =
            if grew_big_unit { relative1 } else { relative0 };
        Ok(Nudge { span, rounded_relative_end, grew_big_unit })
    }

    /// Performs rounding on the given span where the smallest unit is hours
    /// or less *and* the relative datetime is time zone aware.
    fn relative_zoned_time(
        balanced: Span,
        relative_start: &RelativeZoned<'_>,
        smallest: Unit,
        increment: NoUnits128,
        mode: RoundMode,
    ) -> Result<Nudge, Error> {
        let sign = balanced.get_sign_ranged();
        let time_nanos =
            balanced.only_lower(Unit::Day).to_invariant_nanoseconds();
        let mut rounded_time_nanos =
            mode.round_by_unit_in_nanoseconds(time_nanos, smallest, increment);
        let (relative0, relative1) = clamp_relative_span(
            // FIXME: Find a way to drop this clone.
            &Relative::Zoned(relative_start.clone()),
            balanced.without_lower(Unit::Day),
            Unit::Day,
            sign.rinto(),
        )?;
        let day_nanos = relative1 - relative0;
        let beyond_day_nanos = rounded_time_nanos - day_nanos;

        let mut day_delta = NoUnits::N::<0>();
        let rounded_relative_end =
            if beyond_day_nanos == 0 || beyond_day_nanos.signum() == sign {
                day_delta += C(1);
                rounded_time_nanos = mode.round_by_unit_in_nanoseconds(
                    beyond_day_nanos,
                    smallest,
                    increment,
                );
                relative1 + rounded_time_nanos
            } else {
                relative0 + rounded_time_nanos
            };

        let span =
            Span::from_invariant_nanoseconds(Unit::Hour, rounded_time_nanos)
                .with_context(|| {
                    err!(
                        "failed to convert rounded nanoseconds \
                     {rounded_time_nanos} to span for largest unit as {unit}",
                        unit = Unit::Hour.plural(),
                    )
                })?
                .years_ranged(balanced.get_years_ranged())
                .months_ranged(balanced.get_months_ranged())
                .weeks_ranged(balanced.get_weeks_ranged())
                .days_ranged(balanced.get_days_ranged() + day_delta);
        let grew_big_unit = day_delta != 0;
        Ok(Nudge { span, rounded_relative_end, grew_big_unit })
    }

    /// This "bubbles" up the units in a potentially "bottom heavy" span to
    /// larger units. For example, P1m50d relative to March 1 is bottom heavy.
    /// This routine will bubble the days up to months to get P2m19d.
    ///
    /// # Errors
    ///
    /// This routine fails if any arithmetic on the individual units fails, or
    /// when span arithmetic on the relative datetime given fails.
    fn bubble(
        &self,
        relative: &RelativeSpan,
        smallest: Unit,
        largest: Unit,
    ) -> Result<Span, Error> {
        if !self.grew_big_unit || smallest == Unit::Week {
            return Ok(self.span);
        }

        let smallest = smallest.max(Unit::Day);
        let mut balanced = self.span;
        let sign = balanced.get_sign_ranged();
        let mut unit = smallest;
        while let Some(u) = unit.next() {
            unit = u;
            if unit > largest {
                break;
            }
            // We only bubble smaller units up into weeks when the largest unit
            // is explicitly set to weeks. Otherwise, we leave it as-is.
            if unit == Unit::Week && largest != Unit::Week {
                continue;
            }

            let span_start = balanced.without_lower(unit);
            let new_units = span_start
                .get_units_ranged(unit)
                .try_checked_add("bubble-units", sign)
                .with_context(|| {
                    err!(
                        "failed to add sign {sign} to {unit} value {value}",
                        unit = unit.plural(),
                        value = span_start.get_units_ranged(unit),
                    )
                })?;
            let span_end = span_start
                .try_units_ranged(unit, new_units)
                .with_context(|| {
                    err!(
                        "failed to set {unit} to value \
                         {new_units} on span {span_start}",
                        unit = unit.plural(),
                    )
                })?;
            let threshold = match relative.kind {
                RelativeSpanKind::Civil { ref start, .. } => {
                    start.checked_add(span_end)?.timestamp
                }
                RelativeSpanKind::Zoned { ref start, .. } => {
                    start.checked_add(span_end)?.zoned.timestamp()
                }
            };
            let beyond =
                self.rounded_relative_end - threshold.as_nanosecond_ranged();
            if beyond == 0 || beyond.signum() == sign {
                balanced = span_end;
            } else {
                break;
            }
        }
        Ok(balanced)
    }
}

/// Rounds a span consisting of only invariant units.
///
/// This only applies when the max of the units in the span being rounded,
/// the largest configured unit and the smallest configured unit are all
/// invariant. That is, days or lower for spans without a relative datetime or
/// a relative civil datetime, and hours or lower for spans with a relative
/// zoned datetime.
///
/// All we do here is convert the span to an integer number of nanoseconds,
/// round that and then convert back. There aren't any tricky corner cases to
/// consider here.
fn round_span_invariant(
    span: Span,
    smallest: Unit,
    largest: Unit,
    increment: NoUnits128,
    mode: RoundMode,
) -> Result<Span, Error> {
    assert!(smallest <= Unit::Day);
    assert!(largest <= Unit::Day);
    let nanos = span.to_invariant_nanoseconds();
    let rounded =
        mode.round_by_unit_in_nanoseconds(nanos, smallest, increment);
    Span::from_invariant_nanoseconds(largest, rounded).with_context(|| {
        err!(
            "failed to convert rounded nanoseconds {rounded} \
             to span for largest unit as {unit}",
            unit = largest.plural(),
        )
    })
}

/// Returns the nanosecond timestamps of `relative + span` and `relative +
/// {amount of unit} + span`.
///
/// This is useful for determining the actual length, in nanoseconds, of some
/// unit amount (usually a single unit). Usually, this is called with a span
/// whose units lower than `unit` are zeroed out and with an `amount` that
/// is `-1` or `1` or `0`. So for example, if `unit` were `Unit::Day`, then
/// you'd get back two nanosecond timestamps relative to the relative datetime
/// given that start exactly "one day" apart. (Which might be different than 24
/// hours, depending on the time zone.)
///
/// # Errors
///
/// This returns an error if adding the units overflows, or if doing the span
/// arithmetic on `relative` overflows.
fn clamp_relative_span(
    relative: &Relative<'_>,
    span: Span,
    unit: Unit,
    amount: NoUnits,
) -> Result<(NoUnits128, NoUnits128), Error> {
    let amount = span
        .get_units_ranged(unit)
        .try_checked_add("clamp-units", amount)
        .with_context(|| {
            err!(
                "failed to add {amount} to {unit} \
                 value {value} on span {span}",
                unit = unit.plural(),
                value = span.get_units_ranged(unit),
            )
        })?;
    let span_amount =
        span.try_units_ranged(unit, amount).with_context(|| {
            err!(
                "failed to set {unit} unit to {amount} on span {span}",
                unit = unit.plural(),
            )
        })?;
    let relative0 = relative.checked_add(span)?.to_nanosecond();
    let relative1 = relative.checked_add(span_amount)?.to_nanosecond();
    Ok((relative0, relative1))
}

#[cfg(test)]
mod tests {
    use crate::{civil::date, RoundMode};

    use super::*;

    #[test]
    fn test_total() {
        if crate::tz::db().is_definitively_empty() {
            return;
        }

        let span = 130.hours().minutes(20);
        let total = span.total(Unit::Second).unwrap();
        assert_eq!(total, 469200.0);

        let span = 123456789.seconds();
        let total = span.total(Unit::Day).unwrap();
        assert_eq!(total, 1428.8980208333332);

        let span = 2756.hours();
        let dt = date(2020, 1, 1).at(0, 0, 0, 0);
        let zdt = dt.intz("Europe/Rome").unwrap();
        let total = span.total((Unit::Month, &zdt)).unwrap();
        assert_eq!(total, 3.7958333333333334);
        let total = span.total((Unit::Month, dt)).unwrap();
        assert_eq!(total, 3.7944444444444443);
    }

    #[test]
    fn test_compare() {
        if crate::tz::db().is_definitively_empty() {
            return;
        }

        let span1 = 79.hours().minutes(10);
        let span2 = 3.days().hours(7).seconds(630);
        let span3 = 3.days().hours(6).minutes(50);
        let mut array = [span1, span2, span3];
        array.sort_by(|sp1, sp2| sp1.compare(sp2).unwrap());
        assert_eq!(array, [span3, span1, span2]);

        let dt = date(2020, 11, 1).at(0, 0, 0, 0);
        let zdt = dt.intz("America/Los_Angeles").unwrap();
        array.sort_by(|sp1, sp2| sp1.compare((sp2, &zdt)).unwrap());
        assert_eq!(array, [span1, span3, span2]);
    }

    #[test]
    fn test_checked_add() {
        let span1 = 1.hour();
        let span2 = 30.minutes();
        let sum = span1.checked_add(span2).unwrap();
        assert_eq!(sum, 1.hour().minutes(30));

        let span1 = 1.hour().minutes(30);
        let span2 = 2.hours().minutes(45);
        let sum = span1.checked_add(span2).unwrap();
        assert_eq!(sum, 4.hours().minutes(15));

        let span = 50
            .years()
            .months(50)
            .days(50)
            .hours(50)
            .minutes(50)
            .seconds(50)
            .milliseconds(500)
            .microseconds(500)
            .nanoseconds(500);
        let relative = date(1900, 1, 1).at(0, 0, 0, 0);
        let sum = span.checked_add((span, relative)).unwrap();
        let expected = 108
            .years()
            .months(7)
            .days(12)
            .hours(5)
            .minutes(41)
            .seconds(41)
            .milliseconds(1)
            .microseconds(1)
            .nanoseconds(0);
        assert_eq!(sum, expected);

        let span = 1.month().days(15);
        let relative = date(2000, 2, 1).at(0, 0, 0, 0);
        let sum = span.checked_add((span, relative)).unwrap();
        assert_eq!(sum, 3.months());
        let relative = date(2000, 3, 1).at(0, 0, 0, 0);
        let sum = span.checked_add((span, relative)).unwrap();
        assert_eq!(sum, 2.months().days(30));
    }

    #[test]
    fn test_round_day_time() {
        let span = 29.seconds();
        let rounded = span.round(Unit::Minute).unwrap();
        assert_eq!(rounded, 0.minute());

        let span = 30.seconds();
        let rounded = span.round(Unit::Minute).unwrap();
        assert_eq!(rounded, 1.minute());

        let span = 8.seconds();
        let rounded = span
            .round(
                SpanRound::new()
                    .smallest(Unit::Nanosecond)
                    .largest(Unit::Microsecond),
            )
            .unwrap();
        assert_eq!(rounded, 8_000_000.microseconds());

        let span = 130.minutes();
        let rounded = span.round(SpanRound::new().largest(Unit::Day)).unwrap();
        assert_eq!(rounded, 2.hours().minutes(10));

        let span = 10.minutes().seconds(52);
        let rounded = span.round(Unit::Minute).unwrap();
        assert_eq!(rounded, 11.minutes());

        let span = 10.minutes().seconds(52);
        let rounded = span
            .round(
                SpanRound::new().smallest(Unit::Minute).mode(RoundMode::Trunc),
            )
            .unwrap();
        assert_eq!(rounded, 10.minutes());

        let span = 2.hours().minutes(34).seconds(18);
        let rounded =
            span.round(SpanRound::new().largest(Unit::Second)).unwrap();
        assert_eq!(rounded, 9258.seconds());

        let span = 6.minutes();
        let rounded = span
            .round(
                SpanRound::new()
                    .smallest(Unit::Minute)
                    .increment(5)
                    .mode(RoundMode::Ceil),
            )
            .unwrap();
        assert_eq!(rounded, 10.minutes());
    }

    #[test]
    fn test_round_relative_zoned_calendar() {
        if crate::tz::db().is_definitively_empty() {
            return;
        }

        let span = 2756.hours();
        let relative =
            date(2020, 1, 1).at(0, 0, 0, 0).intz("America/New_York").unwrap();
        let options = SpanRound::new()
            .largest(Unit::Year)
            .smallest(Unit::Day)
            .relative(&relative);
        let rounded = span.round(options).unwrap();
        assert_eq!(rounded, 3.months().days(24));

        let span = 24.hours().nanoseconds(5);
        let relative = date(2000, 10, 29)
            .at(0, 0, 0, 0)
            .intz("America/Vancouver")
            .unwrap();
        let options = SpanRound::new()
            .largest(Unit::Day)
            .smallest(Unit::Minute)
            .relative(&relative)
            .mode(RoundMode::Expand)
            .increment(30);
        let rounded = span.round(options).unwrap();
        // It seems like this is the correct answer, although it apparently
        // differs from Temporal and the FullCalendar polyfill. I'm not sure
        // what accounts for the difference in the implementation.
        //
        // See: https://github.com/tc39/proposal-temporal/pull/2758#discussion_r1597255245
        assert_eq!(rounded, 24.hours().minutes(30));

        // Ref: https://github.com/tc39/proposal-temporal/issues/2816#issuecomment-2115608460
        let span = -1.month().hours(24);
        let relative: crate::Zoned =
            date(2024, 4, 11).at(2, 0, 0, 0).intz("America/New_York").unwrap();
        let options =
            SpanRound::new().smallest(Unit::Millisecond).relative(&relative);
        let rounded = span.round(options).unwrap();
        assert_eq!(rounded, -1.month().days(1).hours(1));
        let dt = relative.checked_add(span).unwrap();
        let diff = relative.until((Unit::Month, &dt)).unwrap();
        assert_eq!(diff, -1.month().days(1).hours(1));

        // Like the above, but don't use a datetime near a DST transition. In
        // this case, a day is a normal 24 hours. (Unlike above, where the
        // duration includes a 23 hour day, and so an additional hour has to be
        // added to the span to account for that.)
        let span = -1.month().hours(24);
        let relative =
            date(2024, 6, 11).at(2, 0, 0, 0).intz("America/New_York").unwrap();
        let options =
            SpanRound::new().smallest(Unit::Millisecond).relative(&relative);
        let rounded = span.round(options).unwrap();
        assert_eq!(rounded, -1.month().days(1));
    }

    #[test]
    fn test_round_relative_zoned_time() {
        if crate::tz::db().is_definitively_empty() {
            return;
        }

        let span = 2756.hours();
        let relative =
            date(2020, 1, 1).at(0, 0, 0, 0).intz("America/New_York").unwrap();
        let options = SpanRound::new().largest(Unit::Year).relative(&relative);
        let rounded = span.round(options).unwrap();
        assert_eq!(rounded, 3.months().days(23).hours(21));

        let span = 2756.hours();
        let relative =
            date(2020, 9, 1).at(0, 0, 0, 0).intz("America/New_York").unwrap();
        let options = SpanRound::new().largest(Unit::Year).relative(&relative);
        let rounded = span.round(options).unwrap();
        assert_eq!(rounded, 3.months().days(23).hours(19));

        let span = 3.hours();
        let relative =
            date(2020, 3, 8).at(0, 0, 0, 0).intz("America/New_York").unwrap();
        let options = SpanRound::new().largest(Unit::Year).relative(&relative);
        let rounded = span.round(options).unwrap();
        assert_eq!(rounded, 3.hours());
    }

    #[test]
    fn test_round_relative_day_time() {
        let span = 2756.hours();
        let options =
            SpanRound::new().largest(Unit::Year).relative(date(2020, 1, 1));
        let rounded = span.round(options).unwrap();
        assert_eq!(rounded, 3.months().days(23).hours(20));

        let span = 2756.hours();
        let options =
            SpanRound::new().largest(Unit::Year).relative(date(2020, 9, 1));
        let rounded = span.round(options).unwrap();
        assert_eq!(rounded, 3.months().days(23).hours(20));

        let span = 190.days();
        let options =
            SpanRound::new().largest(Unit::Year).relative(date(2020, 1, 1));
        let rounded = span.round(options).unwrap();
        assert_eq!(rounded, 6.months().days(8));

        let span = 30
            .days()
            .hours(23)
            .minutes(59)
            .seconds(59)
            .milliseconds(999)
            .microseconds(999)
            .nanoseconds(999);
        let options = SpanRound::new()
            .smallest(Unit::Microsecond)
            .largest(Unit::Year)
            .relative(date(2024, 5, 1));
        let rounded = span.round(options).unwrap();
        assert_eq!(rounded, 1.month());

        let span = 364
            .days()
            .hours(23)
            .minutes(59)
            .seconds(59)
            .milliseconds(999)
            .microseconds(999)
            .nanoseconds(999);
        let options = SpanRound::new()
            .smallest(Unit::Microsecond)
            .largest(Unit::Year)
            .relative(date(2023, 1, 1));
        let rounded = span.round(options).unwrap();
        assert_eq!(rounded, 1.year());

        let span = 365
            .days()
            .hours(23)
            .minutes(59)
            .seconds(59)
            .milliseconds(999)
            .microseconds(999)
            .nanoseconds(999);
        let options = SpanRound::new()
            .smallest(Unit::Microsecond)
            .largest(Unit::Year)
            .relative(date(2023, 1, 1));
        let rounded = span.round(options).unwrap();
        assert_eq!(rounded, 1.year().days(1));

        let span = 365
            .days()
            .hours(23)
            .minutes(59)
            .seconds(59)
            .milliseconds(999)
            .microseconds(999)
            .nanoseconds(999);
        let options = SpanRound::new()
            .smallest(Unit::Microsecond)
            .largest(Unit::Year)
            .relative(date(2024, 1, 1));
        let rounded = span.round(options).unwrap();
        assert_eq!(rounded, 1.year());

        let span = 3.hours();
        let options =
            SpanRound::new().largest(Unit::Year).relative(date(2020, 3, 8));
        let rounded = span.round(options).unwrap();
        assert_eq!(rounded, 3.hours());
    }

    #[test]
    fn span_sign() {
        assert_eq!(Span::new().get_sign_ranged(), 0);
        assert_eq!(Span::new().days(1).get_sign_ranged(), 1);
        assert_eq!(Span::new().days(-1).get_sign_ranged(), -1);
        assert_eq!(Span::new().days(1).days(0).get_sign_ranged(), 0);
        assert_eq!(Span::new().days(-1).days(0).get_sign_ranged(), 0);
        assert_eq!(Span::new().years(1).days(1).days(0).get_sign_ranged(), 1);
        assert_eq!(
            Span::new().years(-1).days(-1).days(0).get_sign_ranged(),
            -1
        );
    }

    #[test]
    fn span_size() {
        #[cfg(target_pointer_width = "64")]
        {
            #[cfg(debug_assertions)]
            {
                assert_eq!(core::mem::align_of::<Span>(), 8);
                assert_eq!(core::mem::size_of::<Span>(), 184);
            }
            #[cfg(not(debug_assertions))]
            {
                assert_eq!(core::mem::align_of::<Span>(), 8);
                assert_eq!(core::mem::size_of::<Span>(), 64);
            }
        }
    }

    quickcheck::quickcheck! {
        fn prop_roundtrip_span_nanoseconds(span: Span) -> quickcheck::TestResult {
            let largest = span.largest_unit();
            if largest > Unit::Day {
                return quickcheck::TestResult::discard();
            }
            let nanos = span.to_invariant_nanoseconds();
            let got = Span::from_invariant_nanoseconds(largest, nanos).unwrap();
            quickcheck::TestResult::from_bool(nanos == got.to_invariant_nanoseconds())
        }
    }
}
