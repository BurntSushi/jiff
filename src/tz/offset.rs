use core::ops::{Add, AddAssign, Neg, Sub, SubAssign};

use crate::{
    civil::DateTime,
    error::Error,
    instant::{Instant, TimeScale, Unix},
    span::{Span, TimeDuration},
    util::{
        rangeint::{RFrom, RInto, TryRFrom},
        t::{self, C},
    },
};

/// An enum indicating whether a particular datetime or instant is in DST or
/// not.
///
/// DST stands for "daylight savings time." It is a label used to apply to
/// points in time as a way to contrast it with "standard time." DST is
/// usually, but not always, one hour ahead of standard time. When DST takes
/// effect is usually determined by governments, and the rules can vary
/// depending on the location. DST is typically used as a means to maximize
/// "sunlight" time during typical working hours, and as a cost cutting measure
/// by reducing energy consumption. (The effectiveness of DST and whether it
/// is overall worth it is a separate question entirely.)
///
/// In general, most users should never need to deal with this type. But it can
/// be occasionally useful in circumstances where callers need to know whether
/// DST is active or not for a particular point in time.
///
/// This type has a `From<bool>` trait implementation, where the bool is
/// interpreted as being `true` when DST is active.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub enum Dst {
    /// DST is not in effect. In other words, standard time is in effect.
    No,
    /// DST is in effect.
    Yes,
}

impl Dst {
    /// Returns true when this value is equal to `Dst::Yes`.
    pub fn is_dst(self) -> bool {
        matches!(self, Dst::Yes)
    }

    /// Returns true when this value is equal to `Dst::No`.
    ///
    /// `std` in this context refers to "standard time." That is, it is the
    /// offset from UTC used when DST is not in effect.
    pub fn is_std(self) -> bool {
        matches!(self, Dst::No)
    }
}

impl From<bool> for Dst {
    fn from(is_dst: bool) -> Dst {
        if is_dst {
            Dst::Yes
        } else {
            Dst::No
        }
    }
}

/// Represents a fixed time zone offset.
///
/// Negative offsets correspond to time zones west of the prime meridian, while
/// positive offsets correspond to time zones east of the prime meridian.
/// Equivalently, in all cases, `civil-time - offset = UTC`.
///
/// # Display format
///
/// This type implements the `std::fmt::Display` trait. It
/// will convert the offset to a string format in the form
/// `{sign}{hours}[:{minutes}[:{seconds}]]`, where `minutes` and `seconds` are
/// only present when non-zero. For example:
///
/// ```
/// use jiff::tz::Offset;
///
/// let o = Offset::constant(-5);
/// assert_eq!(o.to_string(), "-05");
/// let o = Offset::constant_seconds(-18_000);
/// assert_eq!(o.to_string(), "-05");
/// let o = Offset::constant_seconds(-18_060);
/// assert_eq!(o.to_string(), "-05:01");
/// let o = Offset::constant_seconds(-18_062);
/// assert_eq!(o.to_string(), "-05:01:02");
///
/// // The min value.
/// let o = Offset::constant_seconds(-93_599);
/// assert_eq!(o.to_string(), "-25:59:59");
/// // The max value.
/// let o = Offset::constant_seconds(93_599);
/// assert_eq!(o.to_string(), "+25:59:59");
/// // No offset.
/// let o = Offset::constant(0);
/// assert_eq!(o.to_string(), "+00");
/// ```
///
/// # Examples
///
/// TODO: Write some examples here using them with real times.
#[derive(Clone, Copy, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct Offset {
    span: t::SpanZoneOffset,
}

impl Offset {
    /// The minimum possible time zone offset.
    ///
    /// This corresponds to the offset `-25:59:59`.
    pub const MIN: Offset = Offset { span: t::SpanZoneOffset::MIN_SELF };

    /// The maximum possible time zone offset.
    ///
    /// This corresponds to the offset `25:59:59`.
    pub const MAX: Offset = Offset { span: t::SpanZoneOffset::MAX_SELF };

    /// The offset corresponding to UTC. That is, no offset at all.
    ///
    /// This is defined to always be equivalent to `Offset::ZERO`, but it is
    /// semantically distinct. This ought to be used when UTC is desired
    /// specifically, while `Offset::ZERO` ought to be used when one wants to
    /// express "no offset." For example, when adding offsets, `Offset::ZERO`
    /// corresponds to the identity.
    pub const UTC: Offset = Offset::ZERO;

    /// The offset corresponding to no offset at all.
    ///
    /// This is defined to always be equivalent to `Offset::UTC`, but it is
    /// semantically distinct. This ought to be used when a zero offset is
    /// desired specifically, while `Offset::UTC` ought to be used when one
    /// wants to express UTC. For example, when adding offsets, `Offset::ZERO`
    /// corresponds to the identity.
    pub const ZERO: Offset = Offset::constant(0);

    /// Creates a new time zone offset in a `const` context from a given number
    /// of hours.
    ///
    /// Negative offsets correspond to time zones west of the prime meridian,
    /// while positive offsets correspond to time zones east of the prime
    /// meridian. Equivalently, in all cases, `civil-time - offset = UTC`.
    ///
    /// The fallible non-const version of this constructor is [`Offset::new`].
    ///
    /// # Panics
    ///
    /// This routine panics when the given number of hours is out of range.
    /// Namely, `hours` must be in the range `-25..=25`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::tz::Offset;
    ///
    /// let o = Offset::constant(-5);
    /// assert_eq!(o.seconds(), -18_000);
    /// let o = Offset::constant(5);
    /// assert_eq!(o.seconds(), 18_000);
    /// ```
    #[inline]
    pub const fn constant(hours: i8) -> Offset {
        if !t::SpanZoneOffsetHours::contains(hours) {
            panic!("invalid time zone offset hours")
        }
        Offset::constant_seconds((hours as i32) * 60 * 60)
    }

    /// Creates a new time zone offset in a `const` context from a given number
    /// of seconds.
    ///
    /// Negative offsets correspond to time zones west of the prime meridian,
    /// while positive offsets correspond to time zones east of the prime
    /// meridian. Equivalently, in all cases, `civil-time - offset = UTC`.
    ///
    /// The fallible non-const version of this constructor is
    /// [`Offset::new_seconds`].
    ///
    /// # Panics
    ///
    /// This routine panics when the given number of seconds is out of range.
    /// The range corresponds to the offsets `-25:59:59..=25:59:59`. In units
    /// of seconds, that corresponds to `-93,599..=93,599`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::tz::Offset;
    ///
    /// let o = Offset::constant_seconds(-18_000);
    /// assert_eq!(o.seconds(), -18_000);
    /// let o = Offset::constant_seconds(18_000);
    /// assert_eq!(o.seconds(), 18_000);
    /// ```
    #[inline]
    pub const fn constant_seconds(seconds: i32) -> Offset {
        if !t::SpanZoneOffset::contains(seconds) {
            panic!("invalid time zone offset seconds")
        }
        Offset { span: t::SpanZoneOffset::new_unchecked(seconds) }
    }

    /// Creates a new time zone offset from a given number of hours.
    ///
    /// Negative offsets correspond to time zones west of the prime meridian,
    /// while positive offsets correspond to time zones east of the prime
    /// meridian. Equivalently, in all cases, `civil-time - offset = UTC`.
    ///
    /// # Errors
    ///
    /// This routine returns an error when the given number of hours is out of
    /// range. Namely, `hours` must be in the range `-25..=25`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::tz::Offset;
    ///
    /// let o = Offset::new(-5)?;
    /// assert_eq!(o.seconds(), -18_000);
    /// let o = Offset::new(5)?;
    /// assert_eq!(o.seconds(), 18_000);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn new(hours: i8) -> Result<Offset, Error> {
        let hours = t::SpanZoneOffsetHours::try_new("offset-hours", hours)?;
        Ok(Offset::new_ranged(hours))
    }

    /// Creates a new time zone offset in a `const` context from a given number
    /// of seconds.
    ///
    /// Negative offsets correspond to time zones west of the prime meridian,
    /// while positive offsets correspond to time zones east of the prime
    /// meridian. Equivalently, in all cases, `civil-time - offset = UTC`.
    ///
    /// # Errors
    ///
    /// This routine returns an error when the given number of seconds is out
    /// of range. The range corresponds to the offsets `-25:59:59..=25:59:59`.
    /// In units of seconds, that corresponds to `-93,599..=93,599`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::tz::Offset;
    ///
    /// let o = Offset::new_seconds(-18_000)?;
    /// assert_eq!(o.seconds(), -18_000);
    /// let o = Offset::new_seconds(18_000)?;
    /// assert_eq!(o.seconds(), 18_000);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn new_seconds(seconds: i32) -> Result<Offset, Error> {
        let seconds = t::SpanZoneOffset::try_new("offset-seconds", seconds)?;
        Ok(Offset::new_seconds_ranged(seconds))
    }

    /// Returns the total number of seconds in this offset.
    ///
    /// The value returned is guaranteed to represent an offset in the range
    /// `-25:59:59..=25:59:59`. Or more precisely, the value will be in units
    /// of seconds in the range `-93,599..=93,599`.
    ///
    /// Negative offsets correspond to time zones west of the prime meridian,
    /// while positive offsets correspond to time zones east of the prime
    /// meridian. Equivalently, in all cases, `civil-time - offset = UTC`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::tz::Offset;
    ///
    /// let o = Offset::constant(-5);
    /// assert_eq!(o.seconds(), -18_000);
    /// let o = Offset::constant(5);
    /// assert_eq!(o.seconds(), 18_000);
    /// ```
    #[inline]
    pub fn seconds(self) -> i32 {
        self.seconds_ranged().get()
    }

    /// Returns the negation of this offset.
    ///
    /// A negative offset will become positive and vice versa. This is a no-op
    /// if the offset is zero.
    ///
    /// This never panics.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::tz::Offset;
    ///
    /// assert_eq!(Offset::constant(-5).negate(), Offset::constant(5));
    /// // It's also available via the `-` operator:
    /// assert_eq!(-Offset::constant(-5), Offset::constant(5));
    /// ```
    pub fn negate(self) -> Offset {
        Offset { span: -self.span }
    }

    /// Returns true if and only if this offset is less than zero.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::tz::Offset;
    ///
    /// assert!(!Offset::constant(5).is_negative());
    /// assert!(!Offset::constant(0).is_negative());
    /// assert!(Offset::constant(-5).is_negative());
    /// ```
    pub fn is_negative(self) -> bool {
        self.seconds_ranged() < 0
    }

    /// Converts the given instant to a civil datetime using this offset.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::{civil::DateTime, tz::Offset, Instant};
    ///
    /// assert_eq!(
    ///     Offset::constant(-8).to_datetime(Instant::UNIX_EPOCH),
    ///     DateTime::constant(1969, 12, 31, 16, 0, 0, 0),
    /// );
    /// ```
    #[inline]
    pub fn to_datetime<S: TimeScale>(self, instant: Instant<S>) -> DateTime {
        instant.to_datetime_with_offset(self)
    }

    /// Converts the given civil datetime to an instant using this offset.
    ///
    /// # Errors
    ///
    /// This returns an error if this would have returned an instant outside
    /// of its minimum and maximum values.
    ///
    /// # Example
    ///
    /// This example shows how to find the instant corresponding to
    /// `1969-12-31T16:00:00-08`.
    ///
    /// ```
    /// use jiff::{civil::DateTime, tz::Offset, Instant};
    ///
    /// let dt = DateTime::constant(1969, 12, 31, 16, 0, 0, 0);
    /// assert_eq!(
    ///     Offset::constant(-8).to_instant(dt).unwrap(),
    ///     Instant::UNIX_EPOCH,
    /// );
    /// ```
    ///
    /// This example shows some maximum boundary conditions where this routine
    /// will fail:
    ///
    /// ```
    /// use jiff::{civil::DateTime, tz::Offset, Instant, ToSpan};
    ///
    /// let dt = DateTime::constant(9999, 12, 31, 23, 0, 0, 0);
    /// assert!(Offset::constant(-8).to_instant(dt).is_err());
    ///
    /// // If the offset is big enough, then converting it to a UTC
    /// // instant will fit, even when using the maximum civil datetime.
    /// let dt = DateTime::constant(9999, 12, 31, 23, 59, 59, 999_999_999);
    /// assert_eq!(Offset::MAX.to_instant(dt).unwrap(), Instant::MAX);
    /// // But adjust the offset down 1 second is enough to go out-of-bounds.
    /// assert!((Offset::MAX - 1.seconds()).to_instant(dt).is_err());
    /// ```
    ///
    /// Same as above, but for minimum values:
    ///
    /// ```
    /// use jiff::{civil::DateTime, tz::Offset, Instant, ToSpan};
    ///
    /// let dt = DateTime::constant(-9999, 1, 1, 1, 0, 0, 0);
    /// assert!(Offset::constant(8).to_instant(dt).is_err());
    ///
    /// // If the offset is small enough, then converting it to a UTC
    /// // instant will fit, even when using the minimum civil datetime.
    /// let dt = DateTime::constant(-9999, 1, 1, 0, 0, 0, 0);
    /// assert_eq!(Offset::MIN.to_instant(dt).unwrap(), Instant::MIN);
    /// // But adjust the offset up 1 second is enough to go out-of-bounds.
    /// assert!((Offset::MIN + 1.seconds()).to_instant(dt).is_err());
    /// ```
    #[inline]
    pub fn to_instant(self, dt: DateTime) -> Result<Instant, Error> {
        self.to_instant_with_scale(dt)
    }

    #[inline]
    pub fn to_instant_with_scale<S: TimeScale>(
        self,
        dt: DateTime,
    ) -> Result<Instant<S>, Error> {
        Instant::from_datetime_zulu_ranged(dt)?.checked_sub(self.to_span())
    }

    /// Returns the span of time since the other offset given from this offset.
    ///
    /// When the `other` is more east (i.e., more positive) of the prime
    /// meridian than this offset, then the span returned will be negative.
    ///
    /// # Properties
    ///
    /// Adding the span returned to the `other` offset will always equal this
    /// offset.
    ///
    /// # Examples
    ///
    /// ```
    /// use jiff::{tz::Offset, ToSpan};
    ///
    /// assert_eq!(
    ///     Offset::UTC.since(Offset::constant(-5)),
    ///     (5 * 60 * 60).seconds(),
    /// );
    /// // Flipping the operands in this case results in a negative span.
    /// assert_eq!(
    ///     Offset::constant(-5).since(Offset::UTC),
    ///     -(5 * 60 * 60).seconds(),
    /// );
    /// ```
    #[inline]
    pub fn since(self, other: Offset) -> Span {
        self.until(other).negate()
    }

    /// Returns the span of time from this offset until the other given.
    ///
    /// When the `other` offset is more west (i.e., more negative) of the prime
    /// meridian than this offset, then the span returned will be negative.
    ///
    /// # Properties
    ///
    /// Adding the span returned to this offset will always equal the `other`
    /// offset given.
    ///
    /// # Examples
    ///
    /// ```
    /// use jiff::{tz::Offset, ToSpan};
    ///
    /// assert_eq!(
    ///     Offset::constant(-5).until(Offset::UTC),
    ///     (5 * 60 * 60).seconds(),
    /// );
    /// // Flipping the operands in this case results in a negative span.
    /// assert_eq!(
    ///     Offset::UTC.until(Offset::constant(-5)),
    ///     -(5 * 60 * 60).seconds(),
    /// );
    /// ```
    #[inline]
    pub fn until(self, other: Offset) -> Span {
        Span::new()
            .seconds_ranged(other.seconds_ranged() - self.seconds_ranged())
    }

    /// Adds the given span of time to this offset.
    ///
    /// Since time zone offsets have second resolution, any fractional seconds
    /// in the span given are ignored.
    ///
    /// # Errors
    ///
    /// This returns an error if the result of adding the given span would
    /// exceed the minimum or maximum allowed `Offset` value.
    ///
    /// # Example
    ///
    /// This example shows how to add one hour to an offset (if the offset
    /// corresponds to standard time, then adding an hour will usually give
    /// you DST time):
    ///
    /// ```
    /// use jiff::{tz::Offset, ToSpan};
    ///
    /// let off = Offset::constant(-5);
    /// assert_eq!(off.checked_add(1.hours()).unwrap(), Offset::constant(-4));
    /// ```
    ///
    /// While unusual, adding a full day to an offset is allowed as long as it
    /// doesn't overflow.
    ///
    /// ```
    /// use jiff::{tz::Offset, ToSpan};
    ///
    /// let off = Offset::constant(-5);
    ///
    /// assert_eq!(off.checked_add(1.days()).unwrap(), Offset::constant(19));
    /// // Adding 1 day is always the same as adding 24 hours.
    /// assert_eq!(off.checked_add(24.hours()).unwrap(), Offset::constant(19));
    /// ```
    ///
    /// And note that while fractional seconds are ignored, units less than
    /// seconds aren't ignored if they sum up to a duration at least as big
    /// as one second:
    ///
    /// ```
    /// use jiff::{tz::Offset, ToSpan};
    ///
    /// let off = Offset::constant(5);
    /// let span = 900.milliseconds()
    ///     .microseconds(50_000)
    ///     .nanoseconds(50_000_000);
    /// assert_eq!(
    ///     off.checked_add(span).unwrap(),
    ///     Offset::constant_seconds((5 * 60 * 60) + 1),
    /// );
    /// // Any leftover fractional part is ignored.
    /// let span = 901.milliseconds()
    ///     .microseconds(50_001)
    ///     .nanoseconds(50_000_001);
    /// assert_eq!(
    ///     off.checked_add(span).unwrap(),
    ///     Offset::constant_seconds((5 * 60 * 60) + 1),
    /// );
    /// ```
    ///
    /// This example shows some cases where checked addition will fail.
    ///
    /// ```
    /// use jiff::{tz::Offset, ToSpan};
    ///
    /// // Adding units above 'day' always results in an error.
    /// assert!(Offset::UTC.checked_add(1.weeks()).is_err());
    /// assert!(Offset::UTC.checked_add(1.months()).is_err());
    /// assert!(Offset::UTC.checked_add(1.years()).is_err());
    ///
    /// // Adding even 1 second to the max, or subtracting 1 from the min,
    /// // will result in overflow and thus an error will be returned.
    /// assert!(Offset::MIN.checked_add(-1.seconds()).is_err());
    /// assert!(Offset::MAX.checked_add(1.seconds()).is_err());
    /// ```
    #[inline]
    pub fn checked_add(self, span: Span) -> Result<Offset, Error> {
        let td = span.time_civil_day_parts_to_duration()?;
        // A non-zero number of weeks will always lead to overflow, but I found
        // it clearer to just do the math here and let it bubble an error.
        let span_weeks = span
            .get_weeks_ranged()
            .try_checked_mul("weeks-as-seconds", t::SECONDS_PER_CIVIL_WEEK)?;
        let span_days = span
            .get_days_ranged()
            .try_checked_mul("days-as-seconds", t::SECONDS_PER_CIVIL_DAY)?;
        let span_seconds =
            t::SpanZoneOffset::try_rfrom("span-as-seconds", td.seconds())?
                .try_checked_add("weeks", span_weeks)?
                .try_checked_add("days", span_days)?;
        let seconds = self
            .seconds_ranged()
            .try_checked_add("offset-as-seconds", span_seconds)?;
        Ok(Offset::new_seconds_ranged(seconds))
    }

    /// Subtracts the given span of time from this offset.
    ///
    /// Since time zone offsets have second resolution, any fractional seconds
    /// in the span given are ignored.
    ///
    /// # Errors
    ///
    /// This returns an error if the result of subtracting the given span would
    /// exceed the minimum or maximum allowed `Offset` value.
    ///
    /// # Example
    ///
    /// This example shows how to subtract one hour to an offset (if the offset
    /// corresponds to DST, then subtracting an hour will usually give you
    /// standard time):
    ///
    /// ```
    /// use jiff::{tz::Offset, ToSpan};
    ///
    /// let off = Offset::constant(-4);
    /// assert_eq!(off.checked_sub(1.hours()).unwrap(), Offset::constant(-5));
    /// ```
    ///
    /// While unusual, subtracting a full day from an offset is allowed as long
    /// as it doesn't overflow.
    ///
    /// ```
    /// use jiff::{tz::Offset, ToSpan};
    ///
    /// let off = Offset::constant(5);
    ///
    /// assert_eq!(off.checked_sub(1.days()).unwrap(), Offset::constant(-19));
    /// // Subtracting 1 day is always the same as subtracting 24 hours.
    /// assert_eq!(off.checked_sub(24.hours()).unwrap(), Offset::constant(-19));
    /// ```
    ///
    /// And note that while fractional seconds are ignored, units less than
    /// seconds aren't ignored if they sum up to a duration at least as big
    /// as one second:
    ///
    /// ```
    /// use jiff::{tz::Offset, ToSpan};
    ///
    /// let off = Offset::constant(5);
    /// let span = 900.milliseconds()
    ///     .microseconds(50_000)
    ///     .nanoseconds(50_000_000);
    /// assert_eq!(
    ///     off.checked_sub(span).unwrap(),
    ///     Offset::constant_seconds((5 * 60 * 60) - 1),
    /// );
    /// // Any leftover fractional part is ignored.
    /// let span = 901.milliseconds()
    ///     .microseconds(50_001)
    ///     .nanoseconds(50_000_001);
    /// assert_eq!(
    ///     off.checked_sub(span).unwrap(),
    ///     Offset::constant_seconds((5 * 60 * 60) - 1),
    /// );
    /// ```
    ///
    /// This example shows some cases where checked subtraction will fail.
    ///
    /// ```
    /// use jiff::{tz::Offset, ToSpan};
    ///
    /// // Subtracting units above 'day' always results in an error.
    /// assert!(Offset::UTC.checked_sub(1.weeks()).is_err());
    /// assert!(Offset::UTC.checked_sub(1.months()).is_err());
    /// assert!(Offset::UTC.checked_sub(1.years()).is_err());
    ///
    /// // Adding even 1 second to the max, or subtracting 1 from the min,
    /// // will result in overflow and thus an error will be returned.
    /// assert!(Offset::MIN.checked_sub(1.seconds()).is_err());
    /// assert!(Offset::MAX.checked_sub(-1.seconds()).is_err());
    /// ```
    #[inline]
    pub fn checked_sub(self, span: Span) -> Result<Offset, Error> {
        self.checked_add(span.negate())
    }

    /// Adds the given span of time to this offset, saturating on overflow.
    ///
    /// Since time zone offsets have second resolution, any fractional seconds
    /// in the span given are ignored.
    ///
    /// # Example
    ///
    /// This example shows some cases where saturation will occur.
    ///
    /// ```
    /// use jiff::{tz::Offset, ToSpan};
    ///
    /// // Adding units above 'day' always results in saturation.
    /// assert_eq!(Offset::UTC.saturating_add(1.weeks()), Offset::MAX);
    /// assert_eq!(Offset::UTC.saturating_add(1.months()), Offset::MAX);
    /// assert_eq!(Offset::UTC.saturating_add(1.years()), Offset::MAX);
    ///
    /// // Adding even 1 second to the max, or subtracting 1 from the min,
    /// // will result in saturationg.
    /// assert_eq!(Offset::MIN.saturating_add(-1.seconds()), Offset::MIN);
    /// assert_eq!(Offset::MAX.saturating_add(1.seconds()), Offset::MAX);
    /// ```
    #[inline]
    pub fn saturating_add(self, span: Span) -> Offset {
        self.checked_add(span).unwrap_or_else(|_| {
            if span.is_negative() {
                Offset::MIN
            } else {
                Offset::MAX
            }
        })
    }

    /// Subtracts the given span of time from this offset, saturating on
    /// overflow.
    ///
    /// Since time zone offsets have second resolution, any fractional seconds
    /// in the span given are ignored.
    ///
    /// # Example
    ///
    /// This example shows some cases where saturation will occur.
    ///
    /// ```
    /// use jiff::{tz::Offset, ToSpan};
    ///
    /// // Adding units above 'day' always results in saturation.
    /// assert_eq!(Offset::UTC.saturating_sub(1.weeks()), Offset::MIN);
    /// assert_eq!(Offset::UTC.saturating_sub(1.months()), Offset::MIN);
    /// assert_eq!(Offset::UTC.saturating_sub(1.years()), Offset::MIN);
    ///
    /// // Adding even 1 second to the max, or subtracting 1 from the min,
    /// // will result in saturationg.
    /// assert_eq!(Offset::MIN.saturating_sub(1.seconds()), Offset::MIN);
    /// assert_eq!(Offset::MAX.saturating_sub(-1.seconds()), Offset::MAX);
    /// ```
    #[inline]
    pub fn saturating_sub(self, span: Span) -> Offset {
        self.saturating_add(span.negate())
    }

    /// Returns this offset as a [`Span`].
    #[inline]
    pub(crate) fn to_span(self) -> Span {
        Span::new().seconds_ranged(self.seconds_ranged())
    }

    /// Returns this offset as a [`TimeDuration`].
    #[inline]
    pub(crate) fn to_time_duration(self) -> TimeDuration {
        TimeDuration::new(self.seconds_ranged(), C(0))
    }
}

impl Offset {
    /// This creates an `Offset` via hours/minutes/seconds components.
    ///
    /// Currently, it exists because it's convenient for use in tests.
    ///
    /// I originally wanted to expose this in the public API, but I couldn't
    /// decide on how I wanted to treat signedness. There are a variety of
    /// choices:
    ///
    /// * Require all values to be positive, and ask the caller to use
    /// `-offset` to negate it.
    /// * Require all values to have the same sign. If any differs, either
    /// panic or return an error.
    /// * If any have a negative sign, then behave as if all have a negative
    /// sign.
    /// * Permit any combination of sign and combine them correctly. Similar
    /// to how `TimeDuration::new(-1s, 1ns)` is turned into `-999,999,999ns`.
    ///
    /// I think the last option is probably the right behavior, but also the
    /// most annoying to implement. But if someone wants to take a crack at it,
    /// a PR is welcome.
    #[cfg(test)]
    #[inline]
    pub(crate) const fn hms(hours: i8, minutes: i8, seconds: i8) -> Offset {
        let total = (hours as i32 * 60 * 60)
            + (minutes as i32 * 60)
            + (seconds as i32);
        Offset { span: t::SpanZoneOffset::new_unchecked(total) }
    }

    #[inline]
    pub(crate) fn new_ranged(
        hours: impl RInto<t::SpanZoneOffsetHours>,
    ) -> Offset {
        let hours: t::SpanZoneOffset = hours.rinto().rinto();
        Offset::new_seconds_ranged(hours * t::SECONDS_PER_HOUR)
    }

    #[inline]
    pub(crate) fn new_seconds_ranged(
        seconds: impl RInto<t::SpanZoneOffset>,
    ) -> Offset {
        Offset { span: seconds.rinto() }
    }

    #[inline]
    pub(crate) fn seconds_ranged(self) -> t::SpanZoneOffset {
        self.span
    }

    #[inline]
    pub(crate) fn part_hours_ranged(self) -> t::SpanZoneOffsetHours {
        self.span.div_ceil(t::SECONDS_PER_HOUR).rinto()
    }

    #[inline]
    pub(crate) fn part_minutes_ranged(self) -> t::SpanZoneOffsetMinutes {
        self.span
            .div_ceil(t::SECONDS_PER_MINUTE)
            .rem_ceil(t::MINUTES_PER_HOUR)
            .rinto()
    }

    #[inline]
    pub(crate) fn part_seconds_ranged(self) -> t::SpanZoneOffsetSeconds {
        self.span.rem_ceil(t::SECONDS_PER_MINUTE).rinto()
    }
}

impl core::fmt::Debug for Offset {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        let sign = if self.seconds_ranged() < 0 { "-" } else { "" };
        write!(
            f,
            "Offset({sign}{:02}:{:02}:{:02})",
            self.part_hours_ranged().abs(),
            self.part_minutes_ranged().abs(),
            self.part_seconds_ranged().abs(),
        )
    }
}

impl core::fmt::Display for Offset {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        let sign = if self.span < 0 { "-" } else { "+" };
        let hours = self.part_hours_ranged().abs().get();
        let minutes = self.part_minutes_ranged().abs().get();
        let seconds = self.part_seconds_ranged().abs().get();
        if hours == 0 && minutes == 0 && seconds == 0 {
            write!(f, "+00")
        } else if hours != 0 && minutes == 0 && seconds == 0 {
            write!(f, "{sign}{hours:02}")
        } else if minutes != 0 && seconds == 0 {
            write!(f, "{sign}{hours:02}:{minutes:02}")
        } else {
            write!(f, "{sign}{hours:02}:{minutes:02}:{seconds:02}")
        }
    }
}

/// Adds a span of time to an offset. This panics on overflow.
///
/// For checked arithmetic, see [`Offset::checked_add`].
impl Add<Span> for Offset {
    type Output = Offset;

    #[inline]
    fn add(self, rhs: Span) -> Offset {
        self.checked_add(rhs)
            .expect("adding span to offset should not overflow")
    }
}

/// Adds a span of time to an offset in place. This panics on overflow.
///
/// For checked arithmetic, see [`Offset::checked_add`].
impl AddAssign<Span> for Offset {
    #[inline]
    fn add_assign(&mut self, rhs: Span) {
        *self = self.add(rhs);
    }
}

/// Subtracts a span of time from an offset. This panics on overflow.
///
/// For checked arithmetic, see [`Offset::checked_sub`].
impl Sub<Span> for Offset {
    type Output = Offset;

    #[inline]
    fn sub(self, rhs: Span) -> Offset {
        self.checked_sub(rhs)
            .expect("subtracting span from offsetsshould not overflow")
    }
}

/// Subtracts a span of time from an offset in place. This panics on overflow.
///
/// For checked arithmetic, see [`Offset::checked_sub`].
impl SubAssign<Span> for Offset {
    #[inline]
    fn sub_assign(&mut self, rhs: Span) {
        *self = self.sub(rhs);
    }
}

/// Computes the span of time between two offsets.
///
/// This will return a negative span when the offset being subtracted is
/// greater (i.e., more east with respect to the prime meridian).
impl Sub for Offset {
    type Output = Span;

    #[inline]
    fn sub(self, rhs: Offset) -> Span {
        self.since(rhs)
    }
}

/// Negate this offset.
///
/// A positive offset becomes negative and vice versa. This is a no-op for the
/// zero offset.
///
/// This never panics.
impl Neg for Offset {
    type Output = Offset;

    #[inline]
    fn neg(self) -> Offset {
        self.negate()
    }
}
