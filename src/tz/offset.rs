use core::ops::{Add, AddAssign, Neg, Sub, SubAssign};

use crate::{
    civil,
    error::{err, Error, ErrorContext},
    span::Span,
    timestamp::Timestamp,
    tz::{AmbiguousOffset, AmbiguousTimestamp, AmbiguousZoned, TimeZone},
    util::{
        rangeint::{RFrom, RInto, TryRFrom},
        t::{self, C},
    },
};

/// An enum indicating whether a particular datetime  is in DST or not.
///
/// DST stands for "daylight saving time." It is a label used to apply to
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
/// use jiff::tz;
///
/// let o = tz::offset(-5);
/// assert_eq!(o.to_string(), "-05");
/// let o = tz::Offset::from_seconds(-18_000).unwrap();
/// assert_eq!(o.to_string(), "-05");
/// let o = tz::Offset::from_seconds(-18_060).unwrap();
/// assert_eq!(o.to_string(), "-05:01");
/// let o = tz::Offset::from_seconds(-18_062).unwrap();
/// assert_eq!(o.to_string(), "-05:01:02");
///
/// // The min value.
/// let o = tz::Offset::from_seconds(-93_599).unwrap();
/// assert_eq!(o.to_string(), "-25:59:59");
/// // The max value.
/// let o = tz::Offset::from_seconds(93_599).unwrap();
/// assert_eq!(o.to_string(), "+25:59:59");
/// // No offset.
/// let o = tz::offset(0);
/// assert_eq!(o.to_string(), "+00");
/// ```
///
/// # Example
///
/// This shows how to create a zoned datetime with a time zone using a fixed
/// offset:
///
/// ```
/// use jiff::{civil::date, tz, Zoned};
///
/// let offset = tz::offset(-4).to_time_zone();
/// let zdt = date(2024, 7, 8).at(15, 20, 0, 0).to_zoned(offset)?;
/// assert_eq!(zdt.to_string(), "2024-07-08T15:20:00-04:00[-04:00]");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// Notice that the zoned datetime still includes a time zone annotation. But
/// since there is no time zone identifier, the offset instead is repeated as
/// an additional assertion that a fixed offset datetime was intended.
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
    /// The fallible non-const version of this constructor is
    /// [`Offset::from_hours`].
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
    ///
    /// Alternatively, one can use the terser `jiff::tz::offset` free function:
    ///
    /// ```
    /// use jiff::tz;
    ///
    /// let o = tz::offset(-5);
    /// assert_eq!(o.seconds(), -18_000);
    /// let o = tz::offset(5);
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
    /// [`Offset::from_seconds`].
    ///
    /// # Panics
    ///
    /// This routine panics when the given number of seconds is out of range.
    /// The range corresponds to the offsets `-25:59:59..=25:59:59`. In units
    /// of seconds, that corresponds to `-93,599..=93,599`.
    ///
    /// # Example
    ///
    /// ```ignore
    /// use jiff::tz::Offset;
    ///
    /// let o = Offset::constant_seconds(-18_000);
    /// assert_eq!(o.seconds(), -18_000);
    /// let o = Offset::constant_seconds(18_000);
    /// assert_eq!(o.seconds(), 18_000);
    /// ```
    // This is currently unexported because I find the name too long and
    // very off-putting. I don't think non-hour offsets are used enough to
    // warrant its existence. And I think I'd rather `Offset::hms` be const and
    // exported instead of this monstrosity.
    #[inline]
    const fn constant_seconds(seconds: i32) -> Offset {
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
    /// let o = Offset::from_hours(-5)?;
    /// assert_eq!(o.seconds(), -18_000);
    /// let o = Offset::from_hours(5)?;
    /// assert_eq!(o.seconds(), 18_000);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn from_hours(hours: i8) -> Result<Offset, Error> {
        let hours = t::SpanZoneOffsetHours::try_new("offset-hours", hours)?;
        Ok(Offset::from_hours_ranged(hours))
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
    /// let o = Offset::from_seconds(-18_000)?;
    /// assert_eq!(o.seconds(), -18_000);
    /// let o = Offset::from_seconds(18_000)?;
    /// assert_eq!(o.seconds(), 18_000);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn from_seconds(seconds: i32) -> Result<Offset, Error> {
        let seconds = t::SpanZoneOffset::try_new("offset-seconds", seconds)?;
        Ok(Offset::from_seconds_ranged(seconds))
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
    /// use jiff::tz;
    ///
    /// let o = tz::offset(-5);
    /// assert_eq!(o.seconds(), -18_000);
    /// let o = tz::offset(5);
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
    /// use jiff::tz;
    ///
    /// assert_eq!(tz::offset(-5).negate(), tz::offset(5));
    /// // It's also available via the `-` operator:
    /// assert_eq!(-tz::offset(-5), tz::offset(5));
    /// ```
    pub fn negate(self) -> Offset {
        Offset { span: -self.span }
    }

    /// Returns true if and only if this offset is less than zero.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::tz;
    ///
    /// assert!(!tz::offset(5).is_negative());
    /// assert!(!tz::offset(0).is_negative());
    /// assert!(tz::offset(-5).is_negative());
    /// ```
    pub fn is_negative(self) -> bool {
        self.seconds_ranged() < 0
    }

    /// Converts this offset into a [`TimeZone`].
    ///
    /// This is a convenience function for calling [`TimeZone::fixed`] with
    /// this offset.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::tz::offset;
    ///
    /// let tz = offset(-4).to_time_zone();
    /// assert_eq!(
    ///     tz.to_datetime(jiff::Timestamp::UNIX_EPOCH).to_string(),
    ///     "1969-12-31T20:00:00",
    /// );
    /// ```
    pub fn to_time_zone(self) -> TimeZone {
        TimeZone::fixed(self)
    }

    /// Converts the given timestamp to a civil datetime using this offset.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::{civil::date, tz, Timestamp};
    ///
    /// assert_eq!(
    ///     tz::offset(-8).to_datetime(Timestamp::UNIX_EPOCH),
    ///     date(1969, 12, 31).at(16, 0, 0, 0),
    /// );
    /// ```
    #[inline]
    pub fn to_datetime(self, timestamp: Timestamp) -> civil::DateTime {
        timestamp_to_datetime_zulu(timestamp, self)
    }

    /// Converts the given civil datetime to a timestamp using this offset.
    ///
    /// # Errors
    ///
    /// This returns an error if this would have returned a timestamp outside
    /// of its minimum and maximum values.
    ///
    /// # Example
    ///
    /// This example shows how to find the timestamp corresponding to
    /// `1969-12-31T16:00:00-08`.
    ///
    /// ```
    /// use jiff::{civil::date, tz, Timestamp};
    ///
    /// assert_eq!(
    ///     tz::offset(-8).to_timestamp(date(1969, 12, 31).at(16, 0, 0, 0))?,
    ///     Timestamp::UNIX_EPOCH,
    /// );
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// This example shows some maximum boundary conditions where this routine
    /// will fail:
    ///
    /// ```
    /// use jiff::{civil::date, tz, Timestamp, ToSpan};
    ///
    /// let dt = date(9999, 12, 31).at(23, 0, 0, 0);
    /// assert!(tz::offset(-8).to_timestamp(dt).is_err());
    ///
    /// // If the offset is big enough, then converting it to a UTC
    /// // timestamp will fit, even when using the maximum civil datetime.
    /// let dt = date(9999, 12, 31).at(23, 59, 59, 999_999_999);
    /// assert_eq!(tz::Offset::MAX.to_timestamp(dt).unwrap(), Timestamp::MAX);
    /// // But adjust the offset down 1 second is enough to go out-of-bounds.
    /// assert!((tz::Offset::MAX - 1.seconds()).to_timestamp(dt).is_err());
    /// ```
    ///
    /// Same as above, but for minimum values:
    ///
    /// ```
    /// use jiff::{civil::date, tz, Timestamp, ToSpan};
    ///
    /// let dt = date(-9999, 1, 1).at(1, 0, 0, 0);
    /// assert!(tz::offset(8).to_timestamp(dt).is_err());
    ///
    /// // If the offset is small enough, then converting it to a UTC
    /// // timestamp will fit, even when using the minimum civil datetime.
    /// let dt = date(-9999, 1, 1).at(0, 0, 0, 0);
    /// assert_eq!(tz::Offset::MIN.to_timestamp(dt).unwrap(), Timestamp::MIN);
    /// // But adjust the offset up 1 second is enough to go out-of-bounds.
    /// assert!((tz::Offset::MIN + 1.seconds()).to_timestamp(dt).is_err());
    /// ```
    #[inline]
    pub fn to_timestamp(
        self,
        dt: civil::DateTime,
    ) -> Result<Timestamp, Error> {
        // datetime_zulu_to_timestamp(dt)?.checked_sub(self.to_span())
        datetime_zulu_to_timestamp(dt)?
            .checked_sub_seconds(i64::from(self.seconds()))
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
    /// use jiff::{tz, ToSpan};
    ///
    /// assert_eq!(
    ///     tz::Offset::UTC.since(tz::offset(-5)),
    ///     (5 * 60 * 60).seconds(),
    /// );
    /// // Flipping the operands in this case results in a negative span.
    /// assert_eq!(
    ///     tz::offset(-5).since(tz::Offset::UTC),
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
    /// use jiff::{tz, ToSpan};
    ///
    /// assert_eq!(
    ///     tz::offset(-5).until(tz::Offset::UTC),
    ///     (5 * 60 * 60).seconds(),
    /// );
    /// // Flipping the operands in this case results in a negative span.
    /// assert_eq!(
    ///     tz::Offset::UTC.until(tz::offset(-5)),
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
    /// This also returns an error if the span given contains any non-zero
    /// units bigger than hours.
    ///
    /// # Example
    ///
    /// This example shows how to add one hour to an offset (if the offset
    /// corresponds to standard time, then adding an hour will usually give
    /// you DST time):
    ///
    /// ```
    /// use jiff::{tz, ToSpan};
    ///
    /// let off = tz::offset(-5);
    /// assert_eq!(off.checked_add(1.hours()).unwrap(), tz::offset(-4));
    /// ```
    ///
    /// And note that while fractional seconds are ignored, units less than
    /// seconds aren't ignored if they sum up to a duration at least as big
    /// as one second:
    ///
    /// ```
    /// use jiff::{tz, ToSpan};
    ///
    /// let off = tz::offset(5);
    /// let span = 900.milliseconds()
    ///     .microseconds(50_000)
    ///     .nanoseconds(50_000_000);
    /// assert_eq!(
    ///     off.checked_add(span).unwrap(),
    ///     tz::Offset::from_seconds((5 * 60 * 60) + 1).unwrap(),
    /// );
    /// // Any leftover fractional part is ignored.
    /// let span = 901.milliseconds()
    ///     .microseconds(50_001)
    ///     .nanoseconds(50_000_001);
    /// assert_eq!(
    ///     off.checked_add(span).unwrap(),
    ///     tz::Offset::from_seconds((5 * 60 * 60) + 1).unwrap(),
    /// );
    /// ```
    ///
    /// This example shows some cases where checked addition will fail.
    ///
    /// ```
    /// # // See: https://github.com/rust-lang/rust/pull/121364
    /// # #![allow(unknown_lints, ambiguous_negative_literals)]
    /// use jiff::{tz::Offset, ToSpan};
    ///
    /// // Adding units above 'hour' always results in an error.
    /// assert!(Offset::UTC.checked_add(1.day()).is_err());
    /// assert!(Offset::UTC.checked_add(1.week()).is_err());
    /// assert!(Offset::UTC.checked_add(1.month()).is_err());
    /// assert!(Offset::UTC.checked_add(1.year()).is_err());
    ///
    /// // Adding even 1 second to the max, or subtracting 1 from the min,
    /// // will result in overflow and thus an error will be returned.
    /// assert!(Offset::MIN.checked_add(-1.seconds()).is_err());
    /// assert!(Offset::MAX.checked_add(1.seconds()).is_err());
    /// ```
    #[inline]
    pub fn checked_add(self, span: Span) -> Result<Offset, Error> {
        if let Some(err) = span.smallest_non_time_non_zero_unit_error() {
            return Err(err);
        }
        let span_seconds = t::SpanZoneOffset::try_rfrom(
            "span-seconds",
            span.to_invariant_nanoseconds().div_ceil(t::NANOS_PER_SECOND),
        )?;
        let offset_seconds = self.seconds_ranged();
        let seconds =
            offset_seconds.try_checked_add("offset-seconds", span_seconds)?;
        Ok(Offset::from_seconds_ranged(seconds))
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
    /// use jiff::{tz, ToSpan};
    ///
    /// let off = tz::offset(-4);
    /// assert_eq!(off.checked_sub(1.hours()).unwrap(), tz::offset(-5));
    /// ```
    ///
    /// And note that while fractional seconds are ignored, units less than
    /// seconds aren't ignored if they sum up to a duration at least as big
    /// as one second:
    ///
    /// ```
    /// use jiff::{tz, ToSpan};
    ///
    /// let off = tz::offset(5);
    /// let span = 900.milliseconds()
    ///     .microseconds(50_000)
    ///     .nanoseconds(50_000_000);
    /// assert_eq!(
    ///     off.checked_sub(span).unwrap(),
    ///     tz::Offset::from_seconds((5 * 60 * 60) - 1).unwrap(),
    /// );
    /// // Any leftover fractional part is ignored.
    /// let span = 901.milliseconds()
    ///     .microseconds(50_001)
    ///     .nanoseconds(50_000_001);
    /// assert_eq!(
    ///     off.checked_sub(span).unwrap(),
    ///     tz::Offset::from_seconds((5 * 60 * 60) - 1).unwrap(),
    /// );
    /// ```
    ///
    /// This example shows some cases where checked subtraction will fail.
    ///
    /// ```
    /// # // See: https://github.com/rust-lang/rust/pull/121364
    /// # #![allow(unknown_lints, ambiguous_negative_literals)]
    /// use jiff::{tz::Offset, ToSpan};
    ///
    /// // Subtracting units above 'hour' always results in an error.
    /// assert!(Offset::UTC.checked_sub(1.day()).is_err());
    /// assert!(Offset::UTC.checked_sub(1.week()).is_err());
    /// assert!(Offset::UTC.checked_sub(1.month()).is_err());
    /// assert!(Offset::UTC.checked_sub(1.year()).is_err());
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
    /// # // See: https://github.com/rust-lang/rust/pull/121364
    /// # #![allow(unknown_lints, ambiguous_negative_literals)]
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
    /// # // See: https://github.com/rust-lang/rust/pull/121364
    /// # #![allow(unknown_lints, ambiguous_negative_literals)]
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
    /// * Permit any combination of sign and combine them correctly.
    /// Similar to how `std::time::Duration::new(-1s, 1ns)` is turned into
    /// `-999,999,999ns`.
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
    pub(crate) fn from_hours_ranged(
        hours: impl RInto<t::SpanZoneOffsetHours>,
    ) -> Offset {
        let hours: t::SpanZoneOffset = hours.rinto().rinto();
        Offset::from_seconds_ranged(hours * t::SECONDS_PER_HOUR)
    }

    #[inline]
    pub(crate) fn from_seconds_ranged(
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
            "{sign}{:02}:{:02}:{:02}",
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

/// Configuration for resolving disparities between an offset and a time zone.
///
/// A conflict between an offset and a time zone most commonly appears in a
/// datetime string. For example, `2024-06-14T17:30-05[America/New_York]`
/// has a definitive inconsistency between the reported offset (`-05`) and
/// the time zone (`America/New_York`), because at this time in New York,
/// daylight saving time (DST) was in effect. In New York in the year 2024,
/// DST corresponded to the UTC offset `-04`.
///
/// Other conflict variations exist. For example, in 2019, Brazil abolished
/// DST completely. But if one were to create a datetime for 2020 in 2018, that
/// datetime in 2020 would reflect the DST rules as they exist in 2018. That
/// could in turn result in a datetime with an offset that is incorrect with
/// respect to the rules in 2019.
///
/// For this reason, this crate exposes a few ways of resolving these
/// conflicts. It is most commonly used as configuration for parsing
/// [`Zoned`](crate::Zoned) values via
/// [`fmt::temporal::DateTimeParser::offset_conflict`](crate::fmt::temporal::DateTimeParser::offset_conflict). But this configuration can also be used directly via
/// [`OffsetConflict::resolve`].
///
/// The default value is `OffsetConflict::Reject`, which results in an
/// error being returned if the offset and a time zone are not in agreement.
/// This is the default so that Jiff does not automatically make silent choices
/// about whether to prefer the time zone or the offset. The
/// [`fmt::temporal::DateTimeParser::parse_zoned_with`](crate::fmt::temporal::DateTimeParser::parse_zoned_with)
/// documentation shows an example demonstrating its utility in the face
/// of changes in the law, such as the abolition of daylight saving time.
/// By rejecting such things, one can ensure that the original timestamp is
/// preserved or else an error occurs.
///
/// This enum is non-exhaustive so that other forms of offset conflicts may be
/// added in semver compatible releases.
///
/// # Example
///
/// This example shows how to always use the time zone even if the offset is
/// wrong.
///
/// ```
/// use jiff::{civil::date, tz};
///
/// let dt = date(2024, 6, 14).at(17, 30, 0, 0);
/// let offset = tz::offset(-5); // wrong! should be -4
/// let newyork = tz::db().get("America/New_York")?;
///
/// // The default conflict resolution, 'Reject', will error.
/// let result = tz::OffsetConflict::Reject
///     .resolve(dt, offset, newyork.clone());
/// assert!(result.is_err());
///
/// // But we can change it to always prefer the time zone.
/// let zdt = tz::OffsetConflict::AlwaysTimeZone
///     .resolve(dt, offset, newyork.clone())?
///     .unambiguous()?;
/// assert_eq!(zdt.datetime(), date(2024, 6, 14).at(17, 30, 0, 0));
/// // The offset has been corrected automatically.
/// assert_eq!(zdt.offset(), tz::offset(-4));
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Example: parsing
///
/// This example shows how to set the offset conflict resolution configuration
/// while parsing a [`Zoned`](crate::Zoned) datetime. In this example, we
/// always prefer the offset, even if it conflicts with the time zone.
///
/// ```
/// use jiff::{civil::date, fmt::temporal::DateTimeParser, tz};
///
/// static PARSER: DateTimeParser = DateTimeParser::new()
///     .offset_conflict(tz::OffsetConflict::AlwaysOffset);
///
/// let zdt = PARSER.parse_zoned("2024-06-14T17:30-05[America/New_York]")?;
/// // The time *and* offset have been corrected. The offset given was invalid,
/// // so it cannot be kept, but the timestamp returned is equivalent to
/// // `2024-06-14T17:30-05`. It is just adjusted automatically to be correct
/// // in the `America/New_York` time zone.
/// assert_eq!(zdt.datetime(), date(2024, 6, 14).at(18, 30, 0, 0));
/// assert_eq!(zdt.offset(), tz::offset(-4));
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Clone, Copy, Debug, Default)]
#[non_exhaustive]
pub enum OffsetConflict {
    /// When the offset and time zone are in conflict, this will always use
    /// the offset to interpret the date time.
    ///
    /// When resolving to a [`AmbiguousZoned`], the time zone attached
    /// to the timestamp will still be the same as the time zone given. The
    /// difference here is that the offset will be adjusted such that it is
    /// correct for the given time zone. However, the timestamp itself will
    /// always match the datetime and offset given (and which is always
    /// unambiguous).
    ///
    /// Basically, you should use this option when you want to keep the exact
    /// time unchanged (as indicated by the datetime and offset), even if it
    /// means a change to civil time.
    AlwaysOffset,
    /// When the offset and time zone are in conflict, this will always use
    /// the time zone to interpret the date time.
    ///
    /// When resolving to an [`AmbiguousZoned`], the offset attached to the
    /// timestamp will always be determined by only looking at the time zone.
    /// This in turn implies that the timestamp returned could be ambiguous,
    /// since this conflict resolution strategy specifically ignores the
    /// offset. (And, we're only at this point because the offset is not
    /// possible for the given time zone, so it can't be used in concert with
    /// the time zone anyway.) This is unlike the `AlwaysOffset` strategy where
    /// the timestamp returned is guaranteed to be unambiguous.
    ///
    /// You should use this option when you want to keep the civil time
    /// unchanged even if it means a change to the exact time.
    AlwaysTimeZone,
    /// Always attempt to use the offset to resolve a datetime to a timestamp,
    /// unless the offset is invalid for the provided time zone. In that case,
    /// use the time zone. When the time zone is used, it's possible for an
    /// ambiguous datetime to be returned.
    PreferOffset,
    /// When the offset and time zone are in conflict, this strategy always
    /// results in conflict resolution returning an error.
    ///
    /// This is the default since a conflict between the offset and the time
    /// zone usually implies an invalid datetime in some way.
    #[default]
    Reject,
}

impl OffsetConflict {
    /// Resolve a potential conflict between an [`Offset`] and a [`TimeZone`].
    ///
    /// # Errors
    ///
    /// This returns an error if this would have returned a timestamp outside
    /// of its minimum and maximum values.
    ///
    /// This can also return an error when using the [`OffsetConflict::Reject`]
    /// strategy. Namely, when using the `Reject` strategy, any offset that is
    /// not compatible with the given datetime and time zone will always result
    /// in an error.
    ///
    /// # Example
    ///
    /// This example shows how each of the different conflict resolution
    /// strategies are applied.
    ///
    /// ```
    /// use jiff::{civil::date, tz};
    ///
    /// let dt = date(2024, 6, 14).at(17, 30, 0, 0);
    /// let offset = tz::offset(-5); // wrong! should be -4
    /// let newyork = tz::db().get("America/New_York")?;
    ///
    /// // Here, we use the offset and ignore the time zone.
    /// let zdt = tz::OffsetConflict::AlwaysOffset
    ///     .resolve(dt, offset, newyork.clone())?
    ///     .unambiguous()?;
    /// // The datetime (and offset) have been corrected automatically
    /// // and the resulting Zoned instant corresponds precisely to
    /// // `2024-06-14T17:30-05[UTC]`.
    /// assert_eq!(zdt.to_string(), "2024-06-14T18:30:00-04:00[America/New_York]");
    ///
    /// // Here, we use the time zone and ignore the offset.
    /// let zdt = tz::OffsetConflict::AlwaysTimeZone
    ///     .resolve(dt, offset, newyork.clone())?
    ///     .unambiguous()?;
    /// // The offset has been corrected automatically and the resulting
    /// // Zoned instant corresponds precisely to `2024-06-14T17:30-04[UTC]`.
    /// // Notice how the civil time remains the same, but the exact instant
    /// // has changed!
    /// assert_eq!(zdt.to_string(), "2024-06-14T17:30:00-04:00[America/New_York]");
    ///
    /// // Here, we prefer the offset, but fall back to the time zone.
    /// // In this example, it has the same behavior as `AlwaysTimeZone`.
    /// let zdt = tz::OffsetConflict::PreferOffset
    ///     .resolve(dt, offset, newyork.clone())?
    ///     .unambiguous()?;
    /// assert_eq!(zdt.to_string(), "2024-06-14T17:30:00-04:00[America/New_York]");
    ///
    /// // The default conflict resolution, 'Reject', will error.
    /// let result = tz::OffsetConflict::Reject
    ///     .resolve(dt, offset, newyork.clone());
    /// assert!(result.is_err());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub fn resolve(
        self,
        dt: civil::DateTime,
        offset: Offset,
        tz: TimeZone,
    ) -> Result<AmbiguousZoned, Error> {
        match self {
            // In this case, we ignore any TZ annotation (although still
            // require that it exists) and always use the provided offset.
            OffsetConflict::AlwaysOffset => {
                let kind = AmbiguousOffset::Unambiguous { offset };
                Ok(AmbiguousTimestamp::new(dt, kind).into_ambiguous_zoned(tz))
            }
            // In this case, we ignore any provided offset and always use the
            // time zone annotation.
            OffsetConflict::AlwaysTimeZone => Ok(tz.into_ambiguous_zoned(dt)),
            // In this case, we use the offset if it's correct, but otherwise
            // fall back to the time zone annotation if it's not.
            OffsetConflict::PreferOffset => {
                Ok(OffsetConflict::resolve_via_prefer(dt, offset, tz))
            }
            // In this case, if the offset isn't possible for the provided time
            // zone annotation, then we return an error.
            OffsetConflict::Reject => {
                OffsetConflict::resolve_via_reject(dt, offset, tz)
            }
        }
    }

    /// Given a parsed datetime, a parsed offset and a parsed time zone, this
    /// attempts to resolve the datetime to a particular instant based on the
    /// 'prefer' strategy.
    ///
    /// In the 'prefer' strategy, we prefer to use the parsed offset to resolve
    /// any ambiguity in the parsed datetime and time zone, but only if the
    /// parsed offset is valid for the parsed datetime and time zone. If the
    /// parsed offset isn't valid, then it is ignored. In the case where it is
    /// ignored, it is possible for an ambiguous instant to be returned.
    fn resolve_via_prefer(
        dt: civil::DateTime,
        given: Offset,
        tz: TimeZone,
    ) -> AmbiguousZoned {
        use crate::tz::AmbiguousOffset::*;

        let amb = tz.to_ambiguous_timestamp(dt);
        match amb.offset() {
            // Basically, if the offset parsed matches one of our ambiguous
            // offsets, then the offset is used to resolve the ambiguity and
            // yields an unambiguous result. But in every other case, the
            // offset parsed is completely ignored. (And this may result in
            // returning an ambiguous instant.)
            Gap { before, after } | Fold { before, after }
                if given == before || given == after =>
            {
                let kind = Unambiguous { offset: given };
                AmbiguousTimestamp::new(dt, kind)
            }
            _ => amb,
        }
        .into_ambiguous_zoned(tz)
    }

    /// Given a parsed datetime, a parsed offset and a parsed time zone, this
    /// attempts to resolve the datetime to a particular instant based on the
    /// 'reject' strategy.
    ///
    /// That is, if the offset is not possibly valid for the given datetime and
    /// time zone, then this returns an error.
    ///
    /// This guarantees that on success, an unambiguous timestamp is returned.
    /// This occurs because if the datetime is ambiguous for the given time
    /// zone, then the parsed offset either matches one of the possible offsets
    /// (and thus provides an unambiguous choice), or it doesn't and an error
    /// is returned.
    fn resolve_via_reject(
        dt: civil::DateTime,
        given: Offset,
        tz: TimeZone,
    ) -> Result<AmbiguousZoned, Error> {
        use crate::tz::AmbiguousOffset::*;

        let amb = tz.to_ambiguous_timestamp(dt);
        match amb.offset() {
            Unambiguous { offset } if given != offset => Err(err!(
                "datetime {dt} could not resolve to a timestamp since \
                 'reject' conflict resolution was chosen, and because \
                 datetime has offset {given}, but the time zone {tzname} for \
                 the given datetime unambiguously has offset {offset}",
                tzname = tz.diagnostic_name(),
            )),
            Unambiguous { .. } => Ok(amb.into_ambiguous_zoned(tz)),
            Gap { before, after } if given != before && given != after => {
                // Temporal actually seems to report an error whenever a gap
                // is found, even if the parsed offset matches one of the two
                // offsets in the gap. I think the reasoning is because the
                // parsed offset and offsets from the gap will flip-flop, thus
                // resulting in a datetime with an offset distinct from the one
                // given. Here's an example. Consider this datetime:
                //
                //     2024-03-10T02:30-04:00[America/New_York]
                //
                // This occurs in the EST->EDT transition gap, such that
                // `02:30` never actually appears on a clock for folks in
                // `America/New_York`. The `-04` offset means that the
                // timestamp this corresponds to is unambiguous. Namely, it is:
                //
                //     2024-03-10T06:30Z
                //
                // This instant, when converted to `America/New_York`, is:
                //
                //     2024-03-10T01:30-05:00[America/New_York]
                //
                // As you can see, the offset flip-flopped. The same flip-flop
                // happens the other way if you use `02:30-05:00`. Presumably,
                // Temporal errors here because the offset changes. But the
                // instant in time is the same *and* it is unambiguous. So it's
                // not clear to me why we ought to error in this case.
                //
                // Ref: https://github.com/tc39/proposal-temporal/issues/2892
                Err(err!(
                    "datetime {dt} could not resolve to timestamp \
                     since 'reject' conflict resolution was chosen, and \
                     because datetime has offset {given}, but the time \
                     zone {tzname} for the given datetime falls in a gap \
                     between offsets {before} and {after}, neither of which \
                     match the offset",
                    tzname = tz.diagnostic_name(),
                ))
            }
            Fold { before, after } if given != before && given != after => {
                Err(err!(
                    "datetime {dt} could not resolve to timestamp \
                     since 'reject' conflict resolution was chosen, and \
                     because datetime has offset {given}, but the time \
                     zone {tzname} for the given datetime falls in a fold \
                     between offsets {before} and {after}, neither of which \
                     match the offset",
                    tzname = tz.diagnostic_name(),
                ))
            }
            Gap { .. } | Fold { .. } => {
                let kind = Unambiguous { offset: given };
                Ok(AmbiguousTimestamp::new(dt, kind).into_ambiguous_zoned(tz))
            }
        }
    }
}

fn timestamp_to_datetime_zulu(
    timestamp: Timestamp,
    offset: Offset,
) -> civil::DateTime {
    let mut second = timestamp.as_second_ranged();
    let nanosecond = timestamp.subsec_nanosecond_ranged();
    second += offset.seconds_ranged();
    // This is a little tricky. The day, second and nanosecond can all be
    // shifted when nanoseconds are themselves negative. Since all three
    // can vary, we need to shove them into a single `NoUnits::vary_many`
    // closure to make range arithmetic work correctly. We convert them
    // back to their proper units afterwards.
    let day = second.without_bounds().div_floor(t::SECONDS_PER_CIVIL_DAY);
    let second: t::NoUnits =
        second.without_bounds().rem_floor(t::SECONDS_PER_CIVIL_DAY);
    let nanosecond = nanosecond.without_bounds();
    let [delta_day, delta_second, delta_nanosecond] = t::NoUnits::vary_many(
        [day, second, nanosecond],
        |[_, second, nanosecond]| {
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
    // minimal value, *and* the number of nanoseconds is non-zero. That
    // case is specifically rejected when constructing a `Timestamp` value,
    // so it is correct to assert that the overflow can never happen.
    let day = t::UnixEpochDays::rfrom(day)
        .try_checked_add("day", delta_day)
        .unwrap();
    let second = (second + delta_second) * t::NANOS_PER_SECOND;
    let nanosecond = nanosecond + delta_nanosecond;
    let civil_day_nanosecond = second + nanosecond;
    let date = civil::Date::from_unix_epoch_days(day);
    let time = civil::Time::from_nanosecond(civil_day_nanosecond);
    civil::DateTime::from_parts(date, time)
}

fn datetime_zulu_to_timestamp(
    dt: civil::DateTime,
) -> Result<Timestamp, Error> {
    let (date, time) = (dt.date(), dt.time());
    let day = date.to_unix_epoch_days().without_bounds();
    let civil_day_nanosecond = time.to_nanosecond().without_bounds();
    let second = civil_day_nanosecond.div_floor(t::NANOS_PER_SECOND);
    let nanosecond = civil_day_nanosecond.rem_floor(t::NANOS_PER_SECOND);
    let [delta_day, delta_second, delta_nanosecond] = t::NoUnits::vary_many(
        [day, second, nanosecond],
        |[day, _second, nanosecond]| {
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
    Timestamp::new_ranged(second, nanosecond).with_context(|| {
        err!(
            "converting {dt} to timestamp overflowed \
             (second={second}, nanosecond={nanosecond})",
        )
    })
}
