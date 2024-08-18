use core::time::Duration;

use crate::{
    civil::{Date, DateTime, Time},
    error::{err, ErrorContext},
    tz::Offset,
    Error, Timestamp, Zoned,
};

#[cfg(not(feature = "std"))]
use crate::util::libm::Float;

// BREADCRUMBS: Update relevant portions of crate documentation too.

/// A signed duration of time represented as a 96-bit integer of nanoseconds.
///
/// Each duration is made up of a 64-bit integer of whole seconds and a
/// 32-bit integer of fractional nanoseconds less than 1 whole second. Unlike
/// [`std::time::Duration`], this duration is signed. The sign applies
/// to the entire duration. That is, either _both_ the seconds and the
/// fractional nanoseconds are negative or _neither_ are. Stated differently,
/// it is guaranteed that the signs of [`SignedDuration::as_secs`] and
/// [`SignedDuration::subsec_nanos`] are always the same.
///
/// # Parsing and printing
///
/// Like the [`Span`](crate::Span) type, the `SignedDuration` type
/// provides convenient trait implementations of [`std::str::FromStr`] and
/// [`std::fmt::Display`]:
///
/// ```
/// use jiff::SignedDuration;
///
/// let duration: SignedDuration = "PT2h30m".parse()?;
/// assert_eq!(duration.to_string(), "PT2h30m");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// Unlike the `Span` type, though, only uniform units are supported. This
/// means that ISO 8601 durations with non-zero units of days or greater cannot
/// be parsed directly into a `SignedDuration`:
///
/// ```
/// use jiff::SignedDuration;
///
/// assert_eq!(
///     "P1d".parse::<SignedDuration>().unwrap_err().to_string(),
///     "failed to parse ISO 8601 duration string into `SignedDuration`: \
///      parsing ISO 8601 duration into SignedDuration requires that the \
///      duration contain a time component and no components of days or \
///      greater",
/// );
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// To parse such durations, one should first parse them into a `Span` and
/// then convert them to a `SignedDuration` by providing a relative date:
///
/// ```
/// use jiff::{civil::date, SignedDuration, Span};
///
/// let span: Span = "P1d".parse()?;
/// let relative = date(2024, 11, 3).intz("US/Eastern")?;
/// let duration = span.to_jiff_duration(&relative)?;
/// // This example also motivates *why* a relative date
/// // is required. Not all days are the same length!
/// assert_eq!(duration.to_string(), "PT25h");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// The format supported is a variation (nearly a subset) of the duration
/// format specified in [ISO 8601]. Here are more examples:
///
/// ```
/// use jiff::SignedDuration;
///
/// let durations = [
///     ("PT2H30M", SignedDuration::from_secs(2 * 60 * 60 + 30 * 60)),
///     ("PT2.5h", SignedDuration::from_secs(2 * 60 * 60 + 30 * 60)),
///     ("PT1m", SignedDuration::from_mins(1)),
///     ("PT1.5m", SignedDuration::from_secs(90)),
///     ("PT0.0021s", SignedDuration::new(0, 2_100_000)),
///     ("PT0s", SignedDuration::ZERO),
///     ("PT0.000000001s", SignedDuration::from_nanos(1)),
/// ];
/// for (string, duration) in durations {
///     let parsed: SignedDuration = string.parse()?;
///     assert_eq!(duration, parsed, "result of parsing {string:?}");
/// }
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// For more details, see the [`fmt::temporal`](crate::fmt::temporal) module.
///
/// [ISO 8601]: https://www.iso.org/iso-8601-date-and-time-format.html
///
/// # API design
///
/// A `SignedDuration` is, as much as is possible, a replica of the
/// `std::time::Duration` API. While there are probably some quirks in the API
/// of `std::time::Duration` that could have been fixed here, it is probably
/// more important that it behave "exactly like a `std::time::Duration` but
/// with a sign." That is, this type mirrors the parallels between signed and
/// unsigned integer types.
///
/// While the goal was to match the `std::time::Duration` API as much as
/// possible, there are some differences worth highlighting:
///
/// * As stated, a `SignedDuration` has a sign. Therefore, it uses `i64` and
/// `i32` instead of `u64` and `u32` to represent its 96-bit integer.
/// * Because it's signed, the range of possible values is different. For
/// example, a `SignedDuration::MAX` has a whole number of seconds equivalent
/// to `i64::MAX`, which is less than `u64::MAX`.
/// * There are some additional APIs that don't make sense on an unsigned
/// duration, like [`SignedDuration::abs`] and [`SignedDuration::checked_neg`].
/// * A [`SignedDuration::system_until`] routine is provided as a replacement
/// for [`std::time::SystemTime::duration_since`], but with signed durations.
/// * Constructors and getters for units of hours and minutes are provided,
/// where as these routines are unstable in the standard library.
/// * Unlike the standard library, this type implements the `std::fmt::Display`
/// and `std::str::FromStr` traits via the ISO 8601 duration format, just
/// like the [`Span`](crate::Span) type does. Also like `Span`, the ISO
/// 8601 duration format is used to implement the serde `Serialize` and
/// `Deserialize` traits when the `serde` crate feature is enabled.
/// * The `std::fmt::Debug` trait implementation is a bit different. If you
/// have a problem with it, please file an issue.
/// * At present, there is no `SignedDuration::abs_diff` since there are some
/// API design questions. If you want it, please file an issue.
///
/// # When should I use `SignedDuration` versus [`Span`](crate::Span)?
///
/// Jiff's primary duration type is `Span`. The key differences between it and
/// `SignedDuration` are:
///
/// * A `Span` keeps track of each individual unit separately. That is, even
/// though `1 hour 60 minutes` and `2 hours` are equivalent durations
/// of time, representing each as a `Span` corresponds to two distinct values
/// in memory. And serializing them to the ISO 8601 duration format will also
/// preserve the units, for example, `PT1h60m` and `PT2h`.
/// * A `Span` supports non-uniform units like days, weeks, months and years.
/// Since not all days, weeks, months and years have the same length, they
/// cannot be represented by a `SignedDuration`. In some cases, it may be
/// appropriate, for example, to assume that all days are 24 hours long. But
/// since Jiff sometimes assumes all days are 24 hours (for civil time) and
/// sometimes doesn't (like for `Zoned` when respecting time zones), it would
/// be inappropriate to bake one of those assumptions into a `SignedDuration`.
/// * A `SignedDuration` is a much smaller type than a `Span`. Specifically,
/// it's a 96-bit integer. In contrast, a `Span` is much larger since it needs
/// to track each individual unit separately.
///
/// Those differences in turn motivate some approximate reasoning for when to
/// use `Span` and when to use `SignedDuration`:
///
/// * If you don't care about keeping track of individual units separately or
/// don't need the sophisticated rounding options available on a `Span`, it
/// might be simpler and faster to use a `SignedDuration`.
/// * If you specifically need performance on arithmetic operations involving
/// datetimes and durations, even if it's not as convenient or correct, then it
/// might make sense to use a `SignedDuration`.
/// * If you need to perform arithmetic using a `std::time::Duration` and
/// otherwise don't need the functionality of a `Span`, it might make sense
/// to first convert the `std::time::Duration` to a `SignedDuration`, and then
/// use one of the corresponding operations defined for `SignedDuration` on
/// the datetime types. (They all support it.)
///
/// In general, a `Span` provides more functionality and is overall more
/// flexible. A `Span` can also deserialize all forms of ISO 8601 durations
/// (as long as they're within Jiff's limits), including durations with units
/// of years, months, weeks and days. A `SignedDuration`, by contrast, only
/// supports units up to and including hours.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct SignedDuration {
    secs: i64,
    nanos: i32,
}

const NANOS_PER_SEC: i32 = 1_000_000_000;
const NANOS_PER_MILLI: i32 = 1_000_000;
const NANOS_PER_MICRO: i32 = 1_000;
const MILLIS_PER_SEC: i64 = 1_000;
const MICROS_PER_SEC: i64 = 1_000_000;
const SECS_PER_MINUTE: i64 = 60;
const MINS_PER_HOUR: i64 = 60;

impl SignedDuration {
    /// A duration of zero time.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::ZERO;
    /// assert!(duration.is_zero());
    /// assert_eq!(duration.as_secs(), 0);
    /// assert_eq!(duration.subsec_nanos(), 0);
    /// ```
    pub const ZERO: SignedDuration = SignedDuration { secs: 0, nanos: 0 };

    /// The minimum possible duration. Or the "most negative" duration.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::MIN;
    /// assert_eq!(duration.as_secs(), i64::MIN);
    /// assert_eq!(duration.subsec_nanos(), -999_999_999);
    /// ```
    pub const MIN: SignedDuration =
        SignedDuration { secs: i64::MIN, nanos: -(NANOS_PER_SEC - 1) };

    /// The maximum possible duration.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::MAX;
    /// assert_eq!(duration.as_secs(), i64::MAX);
    /// assert_eq!(duration.subsec_nanos(), 999_999_999);
    /// ```
    pub const MAX: SignedDuration =
        SignedDuration { secs: i64::MAX, nanos: NANOS_PER_SEC - 1 };

    /// Creates a new `SignedDuration` from the given number of whole seconds
    /// and additional nanoseconds.
    ///
    /// If the absolute value of the nanoseconds is greater than or equal to
    /// 1 second, then the excess balances into the number of whole seconds.
    ///
    /// # Panics
    ///
    /// When the absolute value of the nanoseconds is greater than or equal
    /// to 1 second and the excess that carries over to the number of whole
    /// seconds overflows `i64`.
    ///
    /// This never panics when `nanos` is less than `1_000_000_000`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::new(12, 0);
    /// assert_eq!(duration.as_secs(), 12);
    /// assert_eq!(duration.subsec_nanos(), 0);
    ///
    /// let duration = SignedDuration::new(12, -1);
    /// assert_eq!(duration.as_secs(), 11);
    /// assert_eq!(duration.subsec_nanos(), 999_999_999);
    ///
    /// let duration = SignedDuration::new(12, 1_000_000_000);
    /// assert_eq!(duration.as_secs(), 13);
    /// assert_eq!(duration.subsec_nanos(), 0);
    /// ```
    #[inline]
    pub const fn new(mut secs: i64, mut nanos: i32) -> SignedDuration {
        // When |nanos| exceeds 1 second, we balance the excess up to seconds.
        if !(-NANOS_PER_SEC < nanos && nanos < NANOS_PER_SEC) {
            // Never wraps or panics because NANOS_PER_SEC!={0,-1}.
            let addsecs = nanos / NANOS_PER_SEC;
            secs = match secs.checked_add(addsecs as i64) {
                Some(secs) => secs,
                None => panic!(
                    "nanoseconds overflowed seconds in SignedDuration::new"
                ),
            };
            // Never wraps or panics because NANOS_PER_SEC!={0,-1}.
            nanos = nanos % NANOS_PER_SEC;
        }
        // At this point, we're done if either unit is zero or if they have the
        // same sign.
        if nanos == 0 || secs == 0 || secs.signum() == (nanos.signum() as i64)
        {
            return SignedDuration { secs, nanos };
        }
        // Otherwise, the only work we have to do is to balance negative nanos
        // into positive seconds, or positive nanos into negative seconds.
        if secs < 0 {
            debug_assert!(nanos > 0);
            // Never wraps because adding +1 to a negative i64 never overflows.
            //
            // MSRV(1.79): Consider using `unchecked_add` here.
            secs += 1;
            // Never wraps because subtracting +1_000_000_000 from a positive
            // i32 never overflows.
            //
            // MSRV(1.79): Consider using `unchecked_sub` here.
            nanos -= NANOS_PER_SEC;
        } else {
            debug_assert!(secs > 0);
            debug_assert!(nanos < 0);
            // Never wraps because subtracting +1 from a positive i64 never
            // overflows.
            //
            // MSRV(1.79): Consider using `unchecked_add` here.
            secs -= 1;
            // Never wraps because adding +1_000_000_000 to a negative i32
            // never overflows.
            //
            // MSRV(1.79): Consider using `unchecked_add` here.
            nanos += NANOS_PER_SEC;
        }
        SignedDuration { secs, nanos }
    }

    /// Creates a new `SignedDuration` from the given number of whole seconds.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::from_secs(12);
    /// assert_eq!(duration.as_secs(), 12);
    /// assert_eq!(duration.subsec_nanos(), 0);
    /// ```
    #[inline]
    pub const fn from_secs(secs: i64) -> SignedDuration {
        SignedDuration { secs, nanos: 0 }
    }

    /// Creates a new `SignedDuration` from the given number of whole
    /// milliseconds.
    ///
    /// Note that since this accepts an `i64`, this method cannot be used
    /// to construct the full range of possible signed duration values. In
    /// particular, [`SignedDuration::as_millis`] returns an `i128`, and this
    /// may be a value that would otherwise overflow an `i64`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::from_millis(12_456);
    /// assert_eq!(duration.as_secs(), 12);
    /// assert_eq!(duration.subsec_nanos(), 456_000_000);
    ///
    /// let duration = SignedDuration::from_millis(-12_456);
    /// assert_eq!(duration.as_secs(), -12);
    /// assert_eq!(duration.subsec_nanos(), -456_000_000);
    /// ```
    #[inline]
    pub const fn from_millis(millis: i64) -> SignedDuration {
        // OK because MILLIS_PER_SEC!={-1,0}.
        let secs = millis / MILLIS_PER_SEC;
        // OK because MILLIS_PER_SEC!={-1,0} and because
        // millis % MILLIS_PER_SEC can be at most 999, and 999 * 1_000_000
        // never overflows i32.
        let nanos = (millis % MILLIS_PER_SEC) as i32 * NANOS_PER_MILLI;
        SignedDuration { secs, nanos }
    }

    /// Creates a new `SignedDuration` from the given number of whole
    /// microseconds.
    ///
    /// Note that since this accepts an `i64`, this method cannot be used
    /// to construct the full range of possible signed duration values. In
    /// particular, [`SignedDuration::as_micros`] returns an `i128`, and this
    /// may be a value that would otherwise overflow an `i64`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::from_micros(12_000_456);
    /// assert_eq!(duration.as_secs(), 12);
    /// assert_eq!(duration.subsec_nanos(), 456_000);
    ///
    /// let duration = SignedDuration::from_micros(-12_000_456);
    /// assert_eq!(duration.as_secs(), -12);
    /// assert_eq!(duration.subsec_nanos(), -456_000);
    /// ```
    #[inline]
    pub const fn from_micros(micros: i64) -> SignedDuration {
        // OK because MICROS_PER_SEC!={-1,0}.
        let secs = micros / MICROS_PER_SEC;
        // OK because MICROS_PER_SEC!={-1,0} and because
        // millis % MICROS_PER_SEC can be at most 999, and 999 * 1_000_000
        // never overflows i32.
        let nanos = (micros % MICROS_PER_SEC) as i32 * NANOS_PER_MICRO;
        SignedDuration { secs, nanos }
    }

    /// Creates a new `SignedDuration` from the given number of whole
    /// nanoseconds.
    ///
    /// Note that since this accepts an `i64`, this method cannot be used
    /// to construct the full range of possible signed duration values. In
    /// particular, [`SignedDuration::as_nanos`] returns an `i128`, and this
    /// may be a value that would otherwise overflow an `i64`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::from_nanos(12_000_000_456);
    /// assert_eq!(duration.as_secs(), 12);
    /// assert_eq!(duration.subsec_nanos(), 456);
    ///
    /// let duration = SignedDuration::from_nanos(-12_000_000_456);
    /// assert_eq!(duration.as_secs(), -12);
    /// assert_eq!(duration.subsec_nanos(), -456);
    /// ```
    #[inline]
    pub const fn from_nanos(nanos: i64) -> SignedDuration {
        // OK because NANOS_PER_SEC!={-1,0}.
        let secs = nanos / (NANOS_PER_SEC as i64);
        // OK because NANOS_PER_SEC!={-1,0}.
        let nanos = (nanos % (NANOS_PER_SEC as i64)) as i32;
        SignedDuration { secs, nanos }
    }

    /// Creates a new `SignedDuration` from the given number of hours. Every
    /// hour is exactly `3,600` seconds.
    ///
    /// # Panics
    ///
    /// Panics if the number of hours, after being converted to nanoseconds,
    /// overflows the minimum or maximum `SignedDuration` values.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::from_hours(24);
    /// assert_eq!(duration.as_secs(), 86_400);
    /// assert_eq!(duration.subsec_nanos(), 0);
    ///
    /// let duration = SignedDuration::from_hours(-24);
    /// assert_eq!(duration.as_secs(), -86_400);
    /// assert_eq!(duration.subsec_nanos(), 0);
    /// ```
    #[inline]
    pub const fn from_hours(hours: i64) -> SignedDuration {
        // OK because (SECS_PER_MINUTE*MINS_PER_HOUR)!={-1,0}.
        const MIN_HOUR: i64 = i64::MIN / (SECS_PER_MINUTE * MINS_PER_HOUR);
        // OK because (SECS_PER_MINUTE*MINS_PER_HOUR)!={-1,0}.
        const MAX_HOUR: i64 = i64::MAX / (SECS_PER_MINUTE * MINS_PER_HOUR);
        // OK because (SECS_PER_MINUTE*MINS_PER_HOUR)!={-1,0}.
        if hours < MIN_HOUR {
            panic!("hours overflowed minimum number of SignedDuration seconds")
        }
        // OK because (SECS_PER_MINUTE*MINS_PER_HOUR)!={-1,0}.
        if hours > MAX_HOUR {
            panic!("hours overflowed maximum number of SignedDuration seconds")
        }
        SignedDuration::from_secs(hours * MINS_PER_HOUR * SECS_PER_MINUTE)
    }

    /// Creates a new `SignedDuration` from the given number of minutes. Every
    /// minute is exactly `60` seconds.
    ///
    /// # Panics
    ///
    /// Panics if the number of minutes, after being converted to nanoseconds,
    /// overflows the minimum or maximum `SignedDuration` values.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::from_mins(1_440);
    /// assert_eq!(duration.as_secs(), 86_400);
    /// assert_eq!(duration.subsec_nanos(), 0);
    ///
    /// let duration = SignedDuration::from_mins(-1_440);
    /// assert_eq!(duration.as_secs(), -86_400);
    /// assert_eq!(duration.subsec_nanos(), 0);
    /// ```
    #[inline]
    pub const fn from_mins(minutes: i64) -> SignedDuration {
        // OK because SECS_PER_MINUTE!={-1,0}.
        const MIN_MINUTE: i64 = i64::MIN / SECS_PER_MINUTE;
        // OK because SECS_PER_MINUTE!={-1,0}.
        const MAX_MINUTE: i64 = i64::MAX / SECS_PER_MINUTE;
        // OK because SECS_PER_MINUTE!={-1,0}.
        if minutes < MIN_MINUTE {
            panic!(
                "minutes overflowed minimum number of SignedDuration seconds"
            )
        }
        // OK because SECS_PER_MINUTE!={-1,0}.
        if minutes > MAX_MINUTE {
            panic!(
                "minutes overflowed maximum number of SignedDuration seconds"
            )
        }
        SignedDuration::from_secs(minutes * SECS_PER_MINUTE)
    }

    /// Converts the given timestamp into a signed duration.
    ///
    /// This isn't exported because it's not clear that it makes semantic
    /// sense, since it somewhat encodes the assumption that the "desired"
    /// duration is relative to the Unix epoch. Which is... probably fine?
    /// But I'm not sure.
    ///
    /// But the point of this is to make the conversion a little cheaper.
    /// Namely, since a `Timestamp` internally uses same representation as a
    /// `SignedDuration` with the same guarantees (except with smaller limits),
    /// we can avoid a fair bit of case analysis done in `SignedDuration::new`.
    pub(crate) fn from_timestamp(timestamp: Timestamp) -> SignedDuration {
        SignedDuration {
            secs: timestamp.as_second(),
            nanos: timestamp.subsec_nanosecond(),
        }
    }

    /// Returns true if this duration spans no time.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// assert!(SignedDuration::ZERO.is_zero());
    /// assert!(!SignedDuration::MIN.is_zero());
    /// assert!(!SignedDuration::MAX.is_zero());
    /// ```
    #[inline]
    pub const fn is_zero(&self) -> bool {
        self.secs == 0 && self.nanos == 0
    }

    /// Returns the number of whole seconds in this duration.
    ///
    /// The value returned is negative when the duration is negative.
    ///
    /// This does not include any fractional component corresponding to units
    /// less than a second. To access those, use one of the `subsec` methods
    /// such as [`SignedDuration::subsec_nanos`].
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::new(12, 999_999_999);
    /// assert_eq!(duration.as_secs(), 12);
    ///
    /// let duration = SignedDuration::new(-12, -999_999_999);
    /// assert_eq!(duration.as_secs(), -12);
    /// ```
    #[inline]
    pub const fn as_secs(&self) -> i64 {
        self.secs
    }

    /// Returns the fractional part of this duration in whole milliseconds.
    ///
    /// The value returned is negative when the duration is negative. It is
    /// guaranteed that the range of the value returned is in the inclusive
    /// range `-999..=999`.
    ///
    /// To get the length of the total duration represented in milliseconds,
    /// use [`SignedDuration::as_millis`].
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::new(12, 123_456_789);
    /// assert_eq!(duration.subsec_millis(), 123);
    ///
    /// let duration = SignedDuration::new(-12, -123_456_789);
    /// assert_eq!(duration.subsec_millis(), -123);
    /// ```
    #[inline]
    pub const fn subsec_millis(&self) -> i32 {
        // OK because NANOS_PER_MILLI!={-1,0}.
        self.nanos / NANOS_PER_MILLI
    }

    /// Returns the fractional part of this duration in whole microseconds.
    ///
    /// The value returned is negative when the duration is negative. It is
    /// guaranteed that the range of the value returned is in the inclusive
    /// range `-999_999..=999_999`.
    ///
    /// To get the length of the total duration represented in microseconds,
    /// use [`SignedDuration::as_micros`].
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::new(12, 123_456_789);
    /// assert_eq!(duration.subsec_micros(), 123_456);
    ///
    /// let duration = SignedDuration::new(-12, -123_456_789);
    /// assert_eq!(duration.subsec_micros(), -123_456);
    /// ```
    #[inline]
    pub const fn subsec_micros(&self) -> i32 {
        // OK because NANOS_PER_MICRO!={-1,0}.
        self.nanos / NANOS_PER_MICRO
    }

    /// Returns the fractional part of this duration in whole nanoseconds.
    ///
    /// The value returned is negative when the duration is negative. It is
    /// guaranteed that the range of the value returned is in the inclusive
    /// range `-999_999_999..=999_999_999`.
    ///
    /// To get the length of the total duration represented in nanoseconds,
    /// use [`SignedDuration::as_nanos`].
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::new(12, 123_456_789);
    /// assert_eq!(duration.subsec_nanos(), 123_456_789);
    ///
    /// let duration = SignedDuration::new(-12, -123_456_789);
    /// assert_eq!(duration.subsec_nanos(), -123_456_789);
    /// ```
    #[inline]
    pub const fn subsec_nanos(&self) -> i32 {
        self.nanos
    }

    /// Returns the total duration in units of whole milliseconds.
    ///
    /// The value returned is negative when the duration is negative.
    ///
    /// To get only the fractional component of this duration in units of
    /// whole milliseconds, use [`SignedDuration::subsec_millis`].
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::new(12, 123_456_789);
    /// assert_eq!(duration.as_millis(), 12_123);
    ///
    /// let duration = SignedDuration::new(-12, -123_456_789);
    /// assert_eq!(duration.as_millis(), -12_123);
    /// ```
    #[inline]
    pub const fn as_millis(&self) -> i128 {
        // OK because 1_000 times any i64 will never overflow i128.
        let millis = (self.secs as i128) * (MILLIS_PER_SEC as i128);
        // OK because NANOS_PER_MILLI!={-1,0}.
        let subsec_millis = (self.nanos / NANOS_PER_MILLI) as i128;
        // OK because subsec_millis maxes out at 999, and adding that to
        // i64::MAX*1_000 will never overflow a i128.
        millis + subsec_millis
    }

    /// Returns the total duration in units of whole microseconds.
    ///
    /// The value returned is negative when the duration is negative.
    ///
    /// To get only the fractional component of this duration in units of
    /// whole microseconds, use [`SignedDuration::subsec_micros`].
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::new(12, 123_456_789);
    /// assert_eq!(duration.as_micros(), 12_123_456);
    ///
    /// let duration = SignedDuration::new(-12, -123_456_789);
    /// assert_eq!(duration.as_micros(), -12_123_456);
    /// ```
    #[inline]
    pub const fn as_micros(&self) -> i128 {
        // OK because 1_000_000 times any i64 will never overflow i128.
        let micros = (self.secs as i128) * (MICROS_PER_SEC as i128);
        // OK because NANOS_PER_MICRO!={-1,0}.
        let subsec_micros = (self.nanos / NANOS_PER_MICRO) as i128;
        // OK because subsec_micros maxes out at 999_999, and adding that to
        // i64::MAX*1_000_000 will never overflow a i128.
        micros + subsec_micros
    }

    /// Returns the total duration in units of whole nanoseconds.
    ///
    /// The value returned is negative when the duration is negative.
    ///
    /// To get only the fractional component of this duration in units of
    /// whole nanoseconds, use [`SignedDuration::subsec_nanos`].
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::new(12, 123_456_789);
    /// assert_eq!(duration.as_nanos(), 12_123_456_789);
    ///
    /// let duration = SignedDuration::new(-12, -123_456_789);
    /// assert_eq!(duration.as_nanos(), -12_123_456_789);
    /// ```
    #[inline]
    pub const fn as_nanos(&self) -> i128 {
        // OK because 1_000_000_000 times any i64 will never overflow i128.
        let nanos = (self.secs as i128) * (NANOS_PER_SEC as i128);
        // OK because subsec_nanos maxes out at 999_999_999, and adding that to
        // i64::MAX*1_000_000_000 will never overflow a i128.
        nanos + (self.nanos as i128)
    }

    // NOTE: We don't provide `abs_diff` here because we can't represent the
    // difference between all possible durations. For example,
    // `abs_diff(SignedDuration::MAX, SignedDuration::MIN)`. It therefore seems
    // like we should actually return a `std::time::Duration` here, but I'm
    // trying to be conservative when divering from std.

    /// Add two signed durations together. If overflow occurs, then `None` is
    /// returned.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration1 = SignedDuration::new(12, 500_000_000);
    /// let duration2 = SignedDuration::new(0, 500_000_000);
    /// assert_eq!(
    ///     duration1.checked_add(duration2),
    ///     Some(SignedDuration::new(13, 0)),
    /// );
    ///
    /// let duration1 = SignedDuration::MAX;
    /// let duration2 = SignedDuration::new(0, 1);
    /// assert_eq!(duration1.checked_add(duration2), None);
    /// ```
    #[inline]
    pub const fn checked_add(
        self,
        rhs: SignedDuration,
    ) -> Option<SignedDuration> {
        let Some(mut secs) = self.secs.checked_add(rhs.secs) else {
            return None;
        };
        // OK because `-999_999_999 <= nanos <= 999_999_999`, and so adding
        // them together will never overflow an i32.
        let mut nanos = self.nanos + rhs.nanos;
        // The below is effectively SignedDuration::new, but with checked
        // arithmetic. My suspicion is that there is probably a better way
        // to do this. The main complexity here is that 1) `|nanos|` might
        // now exceed 1 second and 2) the signs of `secs` and `nanos` might
        // not be the same. The other difference from SignedDuration::new is
        // that we know that `-1_999_999_998 <= nanos <= 1_999_999_998` since
        // `|SignedDuration::nanos|` is guaranteed to be less than 1 second. So
        // we can skip the div and modulus operations.

        // When |nanos| exceeds 1 second, we balance the excess up to seconds.
        if nanos >= NANOS_PER_SEC {
            nanos -= NANOS_PER_SEC;
            secs = match secs.checked_add(1) {
                None => return None,
                Some(secs) => secs,
            };
        } else if nanos <= -NANOS_PER_SEC {
            nanos += NANOS_PER_SEC;
            secs = match secs.checked_sub(1) {
                None => return None,
                Some(secs) => secs,
            };
        }
        if secs != 0 && nanos != 0 && secs.signum() != (nanos.signum() as i64)
        {
            if secs < 0 {
                debug_assert!(nanos > 0);
                // OK because secs<0.
                secs += 1;
                // OK because nanos>0.
                nanos -= NANOS_PER_SEC;
            } else {
                debug_assert!(secs > 0);
                debug_assert!(nanos < 0);
                // OK because secs>0.
                secs -= 1;
                // OK because nanos<0.
                nanos += NANOS_PER_SEC;
            }
        }
        Some(SignedDuration { secs, nanos })
    }

    /// Add two signed durations together. If overflow occurs, then arithmetic
    /// saturates.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration1 = SignedDuration::MAX;
    /// let duration2 = SignedDuration::new(0, 1);
    /// assert_eq!(duration1.saturating_add(duration2), SignedDuration::MAX);
    ///
    /// let duration1 = SignedDuration::MIN;
    /// let duration2 = SignedDuration::new(0, -1);
    /// assert_eq!(duration1.saturating_add(duration2), SignedDuration::MIN);
    /// ```
    #[inline]
    pub const fn saturating_add(self, rhs: SignedDuration) -> SignedDuration {
        let Some(sum) = self.checked_add(rhs) else {
            return if rhs.is_negative() {
                SignedDuration::MIN
            } else {
                SignedDuration::MAX
            };
        };
        sum
    }

    /// Subtract one signed duration from another. If overflow occurs, then
    /// `None` is returned.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration1 = SignedDuration::new(12, 500_000_000);
    /// let duration2 = SignedDuration::new(0, 500_000_000);
    /// assert_eq!(
    ///     duration1.checked_sub(duration2),
    ///     Some(SignedDuration::new(12, 0)),
    /// );
    ///
    /// let duration1 = SignedDuration::MIN;
    /// let duration2 = SignedDuration::new(0, 1);
    /// assert_eq!(duration1.checked_sub(duration2), None);
    /// ```
    #[inline]
    pub const fn checked_sub(
        self,
        rhs: SignedDuration,
    ) -> Option<SignedDuration> {
        let Some(rhs) = rhs.checked_neg() else { return None };
        self.checked_add(rhs)
    }

    /// Add two signed durations together. If overflow occurs, then arithmetic
    /// saturates.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration1 = SignedDuration::MAX;
    /// let duration2 = SignedDuration::new(0, -1);
    /// assert_eq!(duration1.saturating_sub(duration2), SignedDuration::MAX);
    ///
    /// let duration1 = SignedDuration::MIN;
    /// let duration2 = SignedDuration::new(0, 1);
    /// assert_eq!(duration1.saturating_sub(duration2), SignedDuration::MIN);
    /// ```
    #[inline]
    pub const fn saturating_sub(self, rhs: SignedDuration) -> SignedDuration {
        let Some(diff) = self.checked_sub(rhs) else {
            return if rhs.is_positive() {
                SignedDuration::MIN
            } else {
                SignedDuration::MAX
            };
        };
        diff
    }

    /// Multiply this signed duration by an integer. If the multiplication
    /// overflows, then `None` is returned.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::new(12, 500_000_000);
    /// assert_eq!(
    ///     duration.checked_mul(2),
    ///     Some(SignedDuration::new(25, 0)),
    /// );
    /// ```
    #[inline]
    pub const fn checked_mul(self, rhs: i32) -> Option<SignedDuration> {
        let rhs = rhs as i64;
        // Multiplying any two i32 values never overflows an i64.
        let nanos = (self.nanos as i64) * rhs;
        // OK since NANOS_PER_SEC!={-1,0}.
        let addsecs = nanos / (NANOS_PER_SEC as i64);
        // OK since NANOS_PER_SEC!={-1,0}.
        let nanos = (nanos % (NANOS_PER_SEC as i64)) as i32;
        let Some(secs) = self.secs.checked_mul(rhs) else { return None };
        let Some(secs) = secs.checked_add(addsecs) else { return None };
        Some(SignedDuration { secs, nanos })
    }

    /// Multiply this signed duration by an integer. If the multiplication
    /// overflows, then the result saturates to either the minimum or maximum
    /// duration depending on the sign of the product.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::new(i64::MAX, 0);
    /// assert_eq!(duration.saturating_mul(2), SignedDuration::MAX);
    /// assert_eq!(duration.saturating_mul(-2), SignedDuration::MIN);
    ///
    /// let duration = SignedDuration::new(i64::MIN, 0);
    /// assert_eq!(duration.saturating_mul(2), SignedDuration::MIN);
    /// assert_eq!(duration.saturating_mul(-2), SignedDuration::MAX);
    /// ```
    #[inline]
    pub const fn saturating_mul(self, rhs: i32) -> SignedDuration {
        let Some(product) = self.checked_mul(rhs) else {
            let sign = (self.signum() as i64) * (rhs as i64).signum();
            return if sign.is_negative() {
                SignedDuration::MIN
            } else {
                SignedDuration::MAX
            };
        };
        product
    }

    /// Divide this duration by an integer. If the division overflows, then
    /// `None` is returned.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::new(12, 500_000_000);
    /// assert_eq!(
    ///     duration.checked_div(2),
    ///     Some(SignedDuration::new(6, 250_000_000)),
    /// );
    /// assert_eq!(
    ///     duration.checked_div(-2),
    ///     Some(SignedDuration::new(-6, -250_000_000)),
    /// );
    ///
    /// let duration = SignedDuration::new(-12, -500_000_000);
    /// assert_eq!(
    ///     duration.checked_div(2),
    ///     Some(SignedDuration::new(-6, -250_000_000)),
    /// );
    /// assert_eq!(
    ///     duration.checked_div(-2),
    ///     Some(SignedDuration::new(6, 250_000_000)),
    /// );
    /// ```
    #[inline]
    pub const fn checked_div(self, rhs: i32) -> Option<SignedDuration> {
        if rhs == 0 || (self.secs == i64::MIN && rhs == -1) {
            return None;
        }
        // OK since rhs!={-1,0}.
        let secs = self.secs / (rhs as i64);
        // OK since rhs!={-1,0}.
        let addsecs = self.secs % (rhs as i64);
        // OK since rhs!=0 and self.nanos>i32::MIN.
        let mut nanos = self.nanos / rhs;
        // OK since rhs!=0 and self.nanos>i32::MIN.
        let addnanos = self.nanos % rhs;
        let leftover_nanos =
            (addsecs * (NANOS_PER_SEC as i64)) + (addnanos as i64);
        nanos += (leftover_nanos / (rhs as i64)) as i32;
        debug_assert!(nanos < NANOS_PER_SEC);
        Some(SignedDuration { secs, nanos })
    }

    /// Returns the number of seconds, with a possible fractional nanosecond
    /// component, represented by this signed duration as a 64-bit float.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::new(12, 123_456_789);
    /// assert_eq!(duration.as_secs_f64(), 12.123456789);
    ///
    /// let duration = SignedDuration::new(-12, -123_456_789);
    /// assert_eq!(duration.as_secs_f64(), -12.123456789);
    /// ```
    #[inline]
    pub fn as_secs_f64(&self) -> f64 {
        (self.secs as f64) + ((self.nanos as f64) / (NANOS_PER_SEC as f64))
    }

    /// Returns the number of seconds, with a possible fractional nanosecond
    /// component, represented by this signed duration as a 32-bit float.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::new(12, 123_456_789);
    /// assert_eq!(duration.as_secs_f32(), 12.123456789);
    ///
    /// let duration = SignedDuration::new(-12, -123_456_789);
    /// assert_eq!(duration.as_secs_f32(), -12.123456789);
    /// ```
    #[inline]
    pub fn as_secs_f32(&self) -> f32 {
        (self.secs as f32) + ((self.nanos as f32) / (NANOS_PER_SEC as f32))
    }

    /// Returns the number of milliseconds, with a possible fractional
    /// nanosecond component, represented by this signed duration as a 64-bit
    /// float.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::new(12, 123_456_789);
    /// assert_eq!(duration.as_millis_f64(), 12123.456789);
    ///
    /// let duration = SignedDuration::new(-12, -123_456_789);
    /// assert_eq!(duration.as_millis_f64(), -12123.456789);
    /// ```
    #[inline]
    pub fn as_millis_f64(&self) -> f64 {
        ((self.secs as f64) * (MILLIS_PER_SEC as f64))
            + ((self.nanos as f64) / (NANOS_PER_MILLI as f64))
    }

    /// Returns the number of milliseconds, with a possible fractional
    /// nanosecond component, represented by this signed duration as a 32-bit
    /// float.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::new(12, 123_456_789);
    /// assert_eq!(duration.as_millis_f32(), 12123.456789);
    ///
    /// let duration = SignedDuration::new(-12, -123_456_789);
    /// assert_eq!(duration.as_millis_f32(), -12123.456789);
    /// ```
    #[inline]
    pub fn as_millis_f32(&self) -> f32 {
        ((self.secs as f32) * (MILLIS_PER_SEC as f32))
            + ((self.nanos as f32) / (NANOS_PER_MILLI as f32))
    }

    /// Returns a signed duration corresponding to the number of seconds
    /// represented as a 64-bit float. The number given may have a fractional
    /// nanosecond component.
    ///
    /// # Panics
    ///
    /// If the given float overflows the minimum or maximum signed duration
    /// values, then this panics.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::from_secs_f64(12.123456789);
    /// assert_eq!(duration.as_secs(), 12);
    /// assert_eq!(duration.subsec_nanos(), 123_456_789);
    ///
    /// let duration = SignedDuration::from_secs_f64(-12.123456789);
    /// assert_eq!(duration.as_secs(), -12);
    /// assert_eq!(duration.subsec_nanos(), -123_456_789);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn from_secs_f64(secs: f64) -> SignedDuration {
        SignedDuration::try_from_secs_f64(secs)
            .expect("finite and in-bounds f64")
    }

    /// Returns a signed duration corresponding to the number of seconds
    /// represented as a 32-bit float. The number given may have a fractional
    /// nanosecond component.
    ///
    /// # Panics
    ///
    /// If the given float overflows the minimum or maximum signed duration
    /// values, then this panics.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::from_secs_f32(12.123456789);
    /// assert_eq!(duration.as_secs(), 12);
    /// // loss of precision!
    /// assert_eq!(duration.subsec_nanos(), 123_456_952);
    ///
    /// let duration = SignedDuration::from_secs_f32(-12.123456789);
    /// assert_eq!(duration.as_secs(), -12);
    /// // loss of precision!
    /// assert_eq!(duration.subsec_nanos(), -123_456_952);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn from_secs_f32(secs: f32) -> SignedDuration {
        SignedDuration::try_from_secs_f32(secs)
            .expect("finite and in-bounds f32")
    }

    /// Returns a signed duration corresponding to the number of seconds
    /// represented as a 64-bit float. The number given may have a fractional
    /// nanosecond component.
    ///
    /// If the given float overflows the minimum or maximum signed duration
    /// values, then an error is returned.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::try_from_secs_f64(12.123456789)?;
    /// assert_eq!(duration.as_secs(), 12);
    /// assert_eq!(duration.subsec_nanos(), 123_456_789);
    ///
    /// let duration = SignedDuration::try_from_secs_f64(-12.123456789)?;
    /// assert_eq!(duration.as_secs(), -12);
    /// assert_eq!(duration.subsec_nanos(), -123_456_789);
    ///
    /// assert!(SignedDuration::try_from_secs_f64(f64::NAN).is_err());
    /// assert!(SignedDuration::try_from_secs_f64(f64::INFINITY).is_err());
    /// assert!(SignedDuration::try_from_secs_f64(f64::NEG_INFINITY).is_err());
    /// assert!(SignedDuration::try_from_secs_f64(f64::MIN).is_err());
    /// assert!(SignedDuration::try_from_secs_f64(f64::MAX).is_err());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn try_from_secs_f64(secs: f64) -> Result<SignedDuration, Error> {
        if !secs.is_finite() {
            return Err(err!(
                "could not convert non-finite seconds \
                 {secs} to signed duration",
            ));
        }
        if secs < (i64::MIN as f64) {
            return Err(err!(
                "floating point seconds {secs} overflows signed duration \
                 minimum value of {:?}",
                SignedDuration::MIN,
            ));
        }
        if secs > (i64::MAX as f64) {
            return Err(err!(
                "floating point seconds {secs} overflows signed duration \
                 maximum value of {:?}",
                SignedDuration::MAX,
            ));
        }
        let nanos = (secs.fract() * (NANOS_PER_SEC as f64)).round() as i32;
        let secs = secs.trunc() as i64;
        Ok(SignedDuration { secs, nanos })
    }

    /// Returns a signed duration corresponding to the number of seconds
    /// represented as a 32-bit float. The number given may have a fractional
    /// nanosecond component.
    ///
    /// If the given float overflows the minimum or maximum signed duration
    /// values, then an error is returned.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::try_from_secs_f32(12.123456789)?;
    /// assert_eq!(duration.as_secs(), 12);
    /// // loss of precision!
    /// assert_eq!(duration.subsec_nanos(), 123_456_952);
    ///
    /// let duration = SignedDuration::try_from_secs_f32(-12.123456789)?;
    /// assert_eq!(duration.as_secs(), -12);
    /// // loss of precision!
    /// assert_eq!(duration.subsec_nanos(), -123_456_952);
    ///
    /// assert!(SignedDuration::try_from_secs_f32(f32::NAN).is_err());
    /// assert!(SignedDuration::try_from_secs_f32(f32::INFINITY).is_err());
    /// assert!(SignedDuration::try_from_secs_f32(f32::NEG_INFINITY).is_err());
    /// assert!(SignedDuration::try_from_secs_f32(f32::MIN).is_err());
    /// assert!(SignedDuration::try_from_secs_f32(f32::MAX).is_err());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn try_from_secs_f32(secs: f32) -> Result<SignedDuration, Error> {
        if !secs.is_finite() {
            return Err(err!(
                "could not convert non-finite seconds \
                 {secs} to signed duration",
            ));
        }
        if secs < (i64::MIN as f32) {
            return Err(err!(
                "floating point seconds {secs} overflows signed duration \
                 minimum value of {:?}",
                SignedDuration::MIN,
            ));
        }
        if secs > (i64::MAX as f32) {
            return Err(err!(
                "floating point seconds {secs} overflows signed duration \
                 maximum value of {:?}",
                SignedDuration::MAX,
            ));
        }
        let nanos = (secs.fract() * (NANOS_PER_SEC as f32)).round() as i32;
        let secs = secs.trunc() as i64;
        Ok(SignedDuration { secs, nanos })
    }

    /// Returns the result of multiplying this duration by the given 64-bit
    /// float.
    ///
    /// # Panics
    ///
    /// This panics if the result is not finite or overflows a
    /// `SignedDuration`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::new(12, 300_000_000);
    /// assert_eq!(
    ///     duration.mul_f64(2.0),
    ///     SignedDuration::new(24, 600_000_000),
    /// );
    /// assert_eq!(
    ///     duration.mul_f64(-2.0),
    ///     SignedDuration::new(-24, -600_000_000),
    /// );
    /// ```
    #[inline]
    pub fn mul_f64(self, rhs: f64) -> SignedDuration {
        SignedDuration::from_secs_f64(rhs * self.as_secs_f64())
    }

    /// Returns the result of multiplying this duration by the given 32-bit
    /// float.
    ///
    /// # Panics
    ///
    /// This panics if the result is not finite or overflows a
    /// `SignedDuration`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::new(12, 300_000_000);
    /// assert_eq!(
    ///     duration.mul_f32(2.0),
    ///     // loss of precision!
    ///     SignedDuration::new(24, 600_000_384),
    /// );
    /// assert_eq!(
    ///     duration.mul_f32(-2.0),
    ///     // loss of precision!
    ///     SignedDuration::new(-24, -600_000_384),
    /// );
    /// ```
    #[inline]
    pub fn mul_f32(self, rhs: f32) -> SignedDuration {
        SignedDuration::from_secs_f32(rhs * self.as_secs_f32())
    }

    /// Returns the result of dividing this duration by the given 64-bit
    /// float.
    ///
    /// # Panics
    ///
    /// This panics if the result is not finite or overflows a
    /// `SignedDuration`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::new(12, 300_000_000);
    /// assert_eq!(
    ///     duration.div_f64(2.0),
    ///     SignedDuration::new(6, 150_000_000),
    /// );
    /// assert_eq!(
    ///     duration.div_f64(-2.0),
    ///     SignedDuration::new(-6, -150_000_000),
    /// );
    /// ```
    #[inline]
    pub fn div_f64(self, rhs: f64) -> SignedDuration {
        SignedDuration::from_secs_f64(self.as_secs_f64() / rhs)
    }

    /// Returns the result of dividing this duration by the given 32-bit
    /// float.
    ///
    /// # Panics
    ///
    /// This panics if the result is not finite or overflows a
    /// `SignedDuration`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::new(12, 300_000_000);
    /// assert_eq!(
    ///     duration.div_f32(2.0),
    ///     // loss of precision!
    ///     SignedDuration::new(6, 150_000_096),
    /// );
    /// assert_eq!(
    ///     duration.div_f32(-2.0),
    ///     // loss of precision!
    ///     SignedDuration::new(-6, -150_000_096),
    /// );
    /// ```
    #[inline]
    pub fn div_f32(self, rhs: f32) -> SignedDuration {
        SignedDuration::from_secs_f32(self.as_secs_f32() / rhs)
    }

    /// Divides this signed duration by another signed duration and returns the
    /// corresponding 64-bit float result.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration1 = SignedDuration::new(12, 600_000_000);
    /// let duration2 = SignedDuration::new(6, 300_000_000);
    /// assert_eq!(duration1.div_duration_f64(duration2), 2.0);
    ///
    /// let duration1 = SignedDuration::new(-12, -600_000_000);
    /// let duration2 = SignedDuration::new(6, 300_000_000);
    /// assert_eq!(duration1.div_duration_f64(duration2), -2.0);
    ///
    /// let duration1 = SignedDuration::new(-12, -600_000_000);
    /// let duration2 = SignedDuration::new(-6, -300_000_000);
    /// assert_eq!(duration1.div_duration_f64(duration2), 2.0);
    /// ```
    #[inline]
    pub fn div_duration_f64(self, rhs: SignedDuration) -> f64 {
        let lhs_nanos =
            (self.secs as f64) * (NANOS_PER_SEC as f64) + (self.nanos as f64);
        let rhs_nanos =
            (rhs.secs as f64) * (NANOS_PER_SEC as f64) + (rhs.nanos as f64);
        lhs_nanos / rhs_nanos
    }

    /// Divides this signed duration by another signed duration and returns the
    /// corresponding 32-bit float result.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration1 = SignedDuration::new(12, 600_000_000);
    /// let duration2 = SignedDuration::new(6, 300_000_000);
    /// assert_eq!(duration1.div_duration_f32(duration2), 2.0);
    ///
    /// let duration1 = SignedDuration::new(-12, -600_000_000);
    /// let duration2 = SignedDuration::new(6, 300_000_000);
    /// assert_eq!(duration1.div_duration_f32(duration2), -2.0);
    ///
    /// let duration1 = SignedDuration::new(-12, -600_000_000);
    /// let duration2 = SignedDuration::new(-6, -300_000_000);
    /// assert_eq!(duration1.div_duration_f32(duration2), 2.0);
    /// ```
    #[inline]
    pub fn div_duration_f32(self, rhs: SignedDuration) -> f32 {
        let lhs_nanos =
            (self.secs as f32) * (NANOS_PER_SEC as f32) + (self.nanos as f32);
        let rhs_nanos =
            (rhs.secs as f32) * (NANOS_PER_SEC as f32) + (rhs.nanos as f32);
        lhs_nanos / rhs_nanos
    }
}

/// Additional APIs not found in the standard library.
///
/// In most cases, these APIs exist as a result of the fact that this duration
/// is signed.
impl SignedDuration {
    /// Returns the number of whole hours in this duration.
    ///
    /// The value returned is negative when the duration is negative.
    ///
    /// This does not include any fractional component corresponding to units
    /// less than an hour.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::new(86_400, 999_999_999);
    /// assert_eq!(duration.as_hours(), 24);
    ///
    /// let duration = SignedDuration::new(-86_400, -999_999_999);
    /// assert_eq!(duration.as_hours(), -24);
    /// ```
    #[inline]
    pub const fn as_hours(&self) -> i64 {
        self.as_secs() / (MINS_PER_HOUR * SECS_PER_MINUTE)
    }

    /// Returns the number of whole minutes in this duration.
    ///
    /// The value returned is negative when the duration is negative.
    ///
    /// This does not include any fractional component corresponding to units
    /// less than a minute.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::new(3_600, 999_999_999);
    /// assert_eq!(duration.as_mins(), 60);
    ///
    /// let duration = SignedDuration::new(-3_600, -999_999_999);
    /// assert_eq!(duration.as_mins(), -60);
    /// ```
    #[inline]
    pub const fn as_mins(&self) -> i64 {
        self.as_secs() / SECS_PER_MINUTE
    }

    /// Returns the absolute value of this signed duration.
    ///
    /// If this duration isn't negative, then this returns the original
    /// duration unchanged.
    ///
    /// # Panics
    ///
    /// This panics when the seconds component of this signed duration is
    /// equal to `i64::MIN`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::new(1, -1_999_999_999);
    /// assert_eq!(duration.abs(), SignedDuration::new(0, 999_999_999));
    /// ```
    #[inline]
    pub const fn abs(self) -> SignedDuration {
        SignedDuration { secs: self.secs.abs(), nanos: self.nanos.abs() }
    }

    /// Returns the absolute value of this signed duration as a
    /// [`std::time::Duration`]. More specifically, this routine cannot
    /// panic because the absolute value of `SignedDuration::MIN` is
    /// representable in a `std::time::Duration`.
    ///
    /// # Example
    ///
    /// ```
    /// use std::time::Duration;
    ///
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::MIN;
    /// assert_eq!(
    ///     duration.unsigned_abs(),
    ///     Duration::new(i64::MIN.unsigned_abs(), 999_999_999),
    /// );
    /// ```
    #[inline]
    pub const fn unsigned_abs(self) -> Duration {
        Duration::new(self.secs.unsigned_abs(), self.nanos.unsigned_abs())
    }

    /// Returns this duration with its sign flipped.
    ///
    /// If this duration is zero, then this returns the duration unchanged.
    ///
    /// This returns none if the negation does not exist. This occurs in
    /// precisely the cases when [`SignedDuration::as_secs`] is equal to
    /// `i64::MIN`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::new(12, 123_456_789);
    /// assert_eq!(
    ///     duration.checked_neg(),
    ///     Some(SignedDuration::new(-12, -123_456_789)),
    /// );
    ///
    /// let duration = SignedDuration::new(-12, -123_456_789);
    /// assert_eq!(
    ///     duration.checked_neg(),
    ///     Some(SignedDuration::new(12, 123_456_789)),
    /// );
    ///
    /// // Negating the minimum seconds isn't possible.
    /// assert_eq!(SignedDuration::MIN.checked_neg(), None);
    /// ```
    #[inline]
    pub const fn checked_neg(self) -> Option<SignedDuration> {
        let Some(secs) = self.secs.checked_neg() else { return None };
        Some(SignedDuration {
            secs,
            // Always OK because `-999_999_999 <= self.nanos <= 999_999_999`.
            nanos: -self.nanos,
        })
    }

    /// Returns a number that represents the sign of this duration.
    ///
    /// * When [`SignedDuration::is_zero`] is true, this returns `0`.
    /// * When [`SignedDuration::is_positive`] is true, this returns `1`.
    /// * When [`SignedDuration::is_negative`] is true, this returns `-1`.
    ///
    /// The above cases are mutually exclusive.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// assert_eq!(0, SignedDuration::ZERO.signum());
    /// ```
    #[inline]
    pub const fn signum(self) -> i8 {
        if self.is_zero() {
            0
        } else if self.is_positive() {
            1
        } else {
            debug_assert!(self.is_negative());
            -1
        }
    }

    /// Returns true when this duration is positive. That is, greater than
    /// [`SignedDuration::ZERO`].
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::new(0, 1);
    /// assert!(duration.is_positive());
    /// ```
    #[inline]
    pub const fn is_positive(&self) -> bool {
        self.secs.is_positive() || self.nanos.is_positive()
    }

    /// Returns true when this duration is negative. That is, less than
    /// [`SignedDuration::ZERO`].
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::SignedDuration;
    ///
    /// let duration = SignedDuration::new(0, -1);
    /// assert!(duration.is_negative());
    /// ```
    #[inline]
    pub const fn is_negative(&self) -> bool {
        self.secs.is_negative() || self.nanos.is_negative()
    }
}

/// Additional APIs for computing the duration between date and time values.
impl SignedDuration {
    pub(crate) fn zoned_until(
        zoned1: &Zoned,
        zoned2: &Zoned,
    ) -> SignedDuration {
        SignedDuration::timestamp_until(zoned1.timestamp(), zoned2.timestamp())
    }

    pub(crate) fn timestamp_until(
        timestamp1: Timestamp,
        timestamp2: Timestamp,
    ) -> SignedDuration {
        let dur1 = SignedDuration::from_timestamp(timestamp1);
        let dur2 = SignedDuration::from_timestamp(timestamp2);
        // OK because all the difference between any two timestamp values can
        // fit into a signed duration.
        dur2 - dur1
    }

    pub(crate) fn datetime_until(
        datetime1: DateTime,
        datetime2: DateTime,
    ) -> SignedDuration {
        let date_until =
            SignedDuration::date_until(datetime1.date(), datetime2.date());
        let time_until =
            SignedDuration::time_until(datetime1.time(), datetime2.time());
        // OK because the difference between any two datetimes can bit into a
        // 96-bit integer of nanoseconds.
        date_until + time_until
    }

    pub(crate) fn date_until(date1: Date, date2: Date) -> SignedDuration {
        let days = date1.until_days_ranged(date2);
        // OK because difference in days fits in an i32, and multiplying an
        // i32 by 24 will never overflow an i64.
        let hours = 24 * i64::from(days.get());
        SignedDuration::from_hours(hours)
    }

    pub(crate) fn time_until(time1: Time, time2: Time) -> SignedDuration {
        let nanos = time1.until_nanoseconds(time2);
        SignedDuration::from_nanos(nanos.get())
    }

    pub(crate) fn offset_until(
        offset1: Offset,
        offset2: Offset,
    ) -> SignedDuration {
        let secs1 = i64::from(offset1.seconds());
        let secs2 = i64::from(offset2.seconds());
        // OK because subtracting any two i32 values will
        // never overflow an i64.
        let diff = secs2 - secs1;
        SignedDuration::from_secs(diff)
    }

    /// Returns the duration from `time1` until `time2` where the times are
    /// [`std::time::SystemTime`] values from the standard library.
    ///
    /// # Errors
    ///
    /// This returns an error if the difference between the two time values
    /// overflows the signed duration limits.
    ///
    /// # Example
    ///
    /// ```
    /// use std::time::{Duration, SystemTime};
    /// use jiff::SignedDuration;
    ///
    /// let time1 = SystemTime::UNIX_EPOCH;
    /// let time2 = time1.checked_add(Duration::from_secs(86_400)).unwrap();
    /// assert_eq!(
    ///     SignedDuration::system_until(time1, time2)?,
    ///     SignedDuration::from_hours(24),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[cfg(feature = "std")]
    #[inline]
    pub fn system_until(
        time1: std::time::SystemTime,
        time2: std::time::SystemTime,
    ) -> Result<SignedDuration, Error> {
        match time2.duration_since(time1) {
            Ok(dur) => SignedDuration::try_from(dur).with_context(|| {
                err!(
                    "unsigned duration {dur:?} for system time since \
                     Unix epoch overflowed signed duration"
                )
            }),
            Err(err) => {
                let dur = err.duration();
                let dur =
                    SignedDuration::try_from(dur).with_context(|| {
                        err!(
                        "unsigned duration {dur:?} for system time before \
                         Unix epoch overflowed signed duration"
                    )
                    })?;
                dur.checked_neg().ok_or_else(|| {
                    err!("negating duration {dur:?} from before the Unix epoch \
                     overflowed signed duration")
                })
            }
        }
    }
}

impl core::fmt::Display for SignedDuration {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        use crate::fmt::{temporal::DEFAULT_SPAN_PRINTER, StdFmtWrite};

        DEFAULT_SPAN_PRINTER
            .print_duration(self, StdFmtWrite(f))
            .map_err(|_| core::fmt::Error)
    }
}

impl core::fmt::Debug for SignedDuration {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        // TODO: Replace with `jiff::fmt::friendly` printer when it exists.
        if self.nanos == 0 {
            write!(f, "{}s", self.secs)
        } else if self.secs == 0 {
            write!(f, "{}ns", self.nanos)
        } else {
            write!(f, "{}s{}ns", self.secs, self.nanos.abs())
        }
    }
}

impl TryFrom<Duration> for SignedDuration {
    type Error = Error;

    fn try_from(d: Duration) -> Result<SignedDuration, Error> {
        let secs = i64::try_from(d.as_secs()).map_err(|_| {
            err!("seconds in unsigned duration {d:?} overflowed i64")
        })?;
        // Guaranteed to succeed since 0<=nanos<=999,999,999.
        let nanos = i32::try_from(d.subsec_nanos()).unwrap();
        Ok(SignedDuration { secs, nanos })
    }
}

impl TryFrom<SignedDuration> for Duration {
    type Error = Error;

    fn try_from(sd: SignedDuration) -> Result<Duration, Error> {
        let secs = u64::try_from(sd.as_secs()).map_err(|_| {
            err!("seconds in signed duration {sd:?} overflowed u64")
        })?;
        // Guaranteed to succeed because the above only succeeds
        // when `sd` is non-negative. And when `sd` is non-negative,
        // we are guaranteed that 0<=nanos<=999,999,999.
        let nanos = u32::try_from(sd.subsec_nanos()).unwrap();
        Ok(Duration::new(secs, nanos))
    }
}

impl core::str::FromStr for SignedDuration {
    type Err = Error;

    #[inline]
    fn from_str(string: &str) -> Result<SignedDuration, Error> {
        use crate::fmt::temporal::DEFAULT_SPAN_PARSER;

        DEFAULT_SPAN_PARSER.parse_duration(string)
    }
}

impl core::ops::Neg for SignedDuration {
    type Output = SignedDuration;

    #[inline]
    fn neg(self) -> SignedDuration {
        self.checked_neg().expect("overflow when negating signed duration")
    }
}

impl core::ops::Add for SignedDuration {
    type Output = SignedDuration;

    #[inline]
    fn add(self, rhs: SignedDuration) -> SignedDuration {
        self.checked_add(rhs).expect("overflow when adding signed durations")
    }
}

impl core::ops::AddAssign for SignedDuration {
    #[inline]
    fn add_assign(&mut self, rhs: SignedDuration) {
        *self = *self + rhs;
    }
}

impl core::ops::Sub for SignedDuration {
    type Output = SignedDuration;

    #[inline]
    fn sub(self, rhs: SignedDuration) -> SignedDuration {
        self.checked_sub(rhs)
            .expect("overflow when subtracting signed durations")
    }
}

impl core::ops::SubAssign for SignedDuration {
    #[inline]
    fn sub_assign(&mut self, rhs: SignedDuration) {
        *self = *self - rhs;
    }
}

impl core::ops::Mul<i32> for SignedDuration {
    type Output = SignedDuration;

    #[inline]
    fn mul(self, rhs: i32) -> SignedDuration {
        self.checked_mul(rhs)
            .expect("overflow when multiplying signed duration by scalar")
    }
}

impl core::ops::Mul<SignedDuration> for i32 {
    type Output = SignedDuration;

    #[inline]
    fn mul(self, rhs: SignedDuration) -> SignedDuration {
        rhs * self
    }
}

impl core::ops::MulAssign<i32> for SignedDuration {
    #[inline]
    fn mul_assign(&mut self, rhs: i32) {
        *self = *self * rhs;
    }
}

impl core::ops::Div<i32> for SignedDuration {
    type Output = SignedDuration;

    #[inline]
    fn div(self, rhs: i32) -> SignedDuration {
        self.checked_div(rhs)
            .expect("overflow when dividing signed duration by scalar")
    }
}

impl core::ops::DivAssign<i32> for SignedDuration {
    #[inline]
    fn div_assign(&mut self, rhs: i32) {
        *self = *self / rhs;
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for SignedDuration {
    #[inline]
    fn serialize<S: serde::Serializer>(
        &self,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        serializer.collect_str(self)
    }
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for SignedDuration {
    #[inline]
    fn deserialize<D: serde::Deserializer<'de>>(
        deserializer: D,
    ) -> Result<SignedDuration, D::Error> {
        use serde::de;

        struct SignedDurationVisitor;

        impl<'de> de::Visitor<'de> for SignedDurationVisitor {
            type Value = SignedDuration;

            fn expecting(
                &self,
                f: &mut core::fmt::Formatter,
            ) -> core::fmt::Result {
                f.write_str("a signed duration string")
            }

            #[inline]
            fn visit_bytes<E: de::Error>(
                self,
                value: &[u8],
            ) -> Result<SignedDuration, E> {
                use crate::fmt::temporal::DEFAULT_SPAN_PARSER;

                DEFAULT_SPAN_PARSER
                    .parse_duration(value)
                    .map_err(de::Error::custom)
            }

            #[inline]
            fn visit_str<E: de::Error>(
                self,
                value: &str,
            ) -> Result<SignedDuration, E> {
                self.visit_bytes(value.as_bytes())
            }
        }

        deserializer.deserialize_bytes(SignedDurationVisitor)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new() {
        let d = SignedDuration::new(12, i32::MAX);
        assert_eq!(d.as_secs(), 14);
        assert_eq!(d.subsec_nanos(), 147_483_647);

        let d = SignedDuration::new(-12, i32::MIN);
        assert_eq!(d.as_secs(), -14);
        assert_eq!(d.subsec_nanos(), -147_483_648);

        let d = SignedDuration::new(i64::MAX, i32::MIN);
        assert_eq!(d.as_secs(), i64::MAX - 3);
        assert_eq!(d.subsec_nanos(), 852_516_352);

        let d = SignedDuration::new(i64::MIN, i32::MAX);
        assert_eq!(d.as_secs(), i64::MIN + 3);
        assert_eq!(d.subsec_nanos(), -852_516_353);
    }

    #[test]
    #[should_panic]
    fn new_fail_positive() {
        SignedDuration::new(i64::MAX, 1_000_000_000);
    }

    #[test]
    #[should_panic]
    fn new_fail_negative() {
        SignedDuration::new(i64::MIN, -1_000_000_000);
    }

    #[test]
    fn from_hours_limits() {
        let d = SignedDuration::from_hours(2_562_047_788_015_215);
        assert_eq!(d.as_secs(), 9223372036854774000);

        let d = SignedDuration::from_hours(-2_562_047_788_015_215);
        assert_eq!(d.as_secs(), -9223372036854774000);
    }

    #[test]
    #[should_panic]
    fn from_hours_fail_positive() {
        SignedDuration::from_hours(2_562_047_788_015_216);
    }

    #[test]
    #[should_panic]
    fn from_hours_fail_negative() {
        SignedDuration::from_hours(-2_562_047_788_015_216);
    }

    #[test]
    fn from_minutes_limits() {
        let d = SignedDuration::from_mins(153_722_867_280_912_930);
        assert_eq!(d.as_secs(), 9223372036854775800);

        let d = SignedDuration::from_mins(-153_722_867_280_912_930);
        assert_eq!(d.as_secs(), -9223372036854775800);
    }

    #[test]
    #[should_panic]
    fn from_minutes_fail_positive() {
        SignedDuration::from_mins(153_722_867_280_912_931);
    }

    #[test]
    #[should_panic]
    fn from_minutes_fail_negative() {
        SignedDuration::from_mins(-153_722_867_280_912_931);
    }

    #[test]
    fn add() {
        let add = |(secs1, nanos1): (i64, i32),
                   (secs2, nanos2): (i64, i32)|
         -> (i64, i32) {
            let d1 = SignedDuration::new(secs1, nanos1);
            let d2 = SignedDuration::new(secs2, nanos2);
            let sum = d1.checked_add(d2).unwrap();
            (sum.as_secs(), sum.subsec_nanos())
        };

        assert_eq!(add((1, 1), (1, 1)), (2, 2));
        assert_eq!(add((1, 1), (-1, -1)), (0, 0));
        assert_eq!(add((-1, -1), (1, 1)), (0, 0));
        assert_eq!(add((-1, -1), (-1, -1)), (-2, -2));

        assert_eq!(add((1, 500_000_000), (1, 500_000_000)), (3, 0));
        assert_eq!(add((-1, -500_000_000), (-1, -500_000_000)), (-3, 0));
        assert_eq!(
            add((5, 200_000_000), (-1, -500_000_000)),
            (3, 700_000_000)
        );
        assert_eq!(
            add((-5, -200_000_000), (1, 500_000_000)),
            (-3, -700_000_000)
        );
    }

    #[test]
    fn add_overflow() {
        let add = |(secs1, nanos1): (i64, i32),
                   (secs2, nanos2): (i64, i32)|
         -> Option<(i64, i32)> {
            let d1 = SignedDuration::new(secs1, nanos1);
            let d2 = SignedDuration::new(secs2, nanos2);
            d1.checked_add(d2).map(|d| (d.as_secs(), d.subsec_nanos()))
        };
        assert_eq!(None, add((i64::MAX, 0), (1, 0)));
        assert_eq!(None, add((i64::MIN, 0), (-1, 0)));
        assert_eq!(None, add((i64::MAX, 1), (0, 999_999_999)));
        assert_eq!(None, add((i64::MIN, -1), (0, -999_999_999)));
    }
}
