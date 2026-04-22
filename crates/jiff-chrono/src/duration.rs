use chrono::{Months as ChronoMonths, TimeDelta as ChronoTimeDelta};
use jiff::{SignedDuration as JiffSignedDuration, Span as JiffSpan};

use crate::{
    error::{err, Error},
    traits::{ConvertFrom, ConvertTryFrom},
};

/// Converts from a [`chrono::TimeDelta`] to a [`jiff::SignedDuration`].
///
/// This conversion is infallible: chrono's `TimeDelta` range (bounded to
/// what fits in milliseconds as `i64`) is a subset of `SignedDuration`'s
/// range (seconds as `i64`).
///
/// # Example
///
/// ```
/// use jiff_chrono::ConvertFrom as _;
///
/// let td = chrono::TimeDelta::new(86_400, 123_456_789).unwrap();
/// let sd = jiff::SignedDuration::convert_from(td);
/// assert_eq!(sd.as_secs(), 86_400);
/// assert_eq!(sd.subsec_nanos(), 123_456_789);
///
/// let td = -chrono::TimeDelta::milliseconds(1_500);
/// let sd = jiff::SignedDuration::convert_from(td);
/// assert_eq!(sd.as_secs(), -1);
/// assert_eq!(sd.subsec_nanos(), -500_000_000);
/// ```
impl ConvertFrom<ChronoTimeDelta> for JiffSignedDuration {
    fn convert_from(v: ChronoTimeDelta) -> JiffSignedDuration {
        // `TimeDelta` stores a non-negative subsec-nanos field internally and
        // uses floored seconds. `num_seconds()` rounds toward zero and
        // `subsec_nanos()` returns a value whose sign matches the overall
        // delta. `SignedDuration::new` accepts values with the same sign,
        // so this is a direct construction.
        //
        // `TimeDelta` cannot represent a duration larger (in absolute value)
        // than `i64::MAX / 1000` seconds, so the `new` call cannot panic.
        JiffSignedDuration::new(v.num_seconds(), v.subsec_nanos())
    }
}

/// Converts from a [`jiff::SignedDuration`] to a [`chrono::TimeDelta`].
///
/// This conversion is fallible. `SignedDuration` supports seconds across the
/// full `i64` range, whereas `TimeDelta`'s range is limited to values whose
/// total milliseconds fit in `i64` (roughly `±2.9 * 10^11` seconds).
///
/// # Example
///
/// ```
/// use jiff_chrono::ConvertTryFrom as _;
///
/// let sd = jiff::SignedDuration::new(86_400, 123_456_789);
/// let td = chrono::TimeDelta::convert_try_from(sd)?;
/// assert_eq!(td.num_seconds(), 86_400);
/// assert_eq!(td.subsec_nanos(), 123_456_789);
///
/// // Negative durations are preserved.
/// let sd = jiff::SignedDuration::new(-1, -500_000_000);
/// let td = chrono::TimeDelta::convert_try_from(sd)?;
/// assert_eq!(td.num_milliseconds(), -1_500);
///
/// // Values outside `TimeDelta`'s range are rejected.
/// assert!(chrono::TimeDelta::convert_try_from(
///     jiff::SignedDuration::MAX
/// ).is_err());
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
impl ConvertTryFrom<JiffSignedDuration> for ChronoTimeDelta {
    type Error = Error;

    fn convert_try_from(
        v: JiffSignedDuration,
    ) -> Result<ChronoTimeDelta, Error> {
        let secs = v.as_secs();
        let nanos = v.subsec_nanos();
        // `TimeDelta::new` requires a non-negative `nanos` argument in
        // `0..1_000_000_000` and combines it with floored seconds.
        // `SignedDuration` stores `secs` and `nanos` with the same sign,
        // so for negative values we shift one second's worth of nanos
        // into the positive range.
        let (secs, nanos) = if nanos < 0 {
            let secs = secs.checked_sub(1).ok_or_else(|| {
                err!(
                    "Jiff `SignedDuration` of {v} overflows when converting \
                     to `chrono::TimeDelta`",
                )
            })?;
            (secs, (nanos + 1_000_000_000) as u32)
        } else {
            (secs, nanos as u32)
        };
        ChronoTimeDelta::new(secs, nanos).ok_or_else(|| {
            err!(
                "Jiff `SignedDuration` of {v} is out of range for \
                 `chrono::TimeDelta`",
            )
        })
    }
}

/// Converts from a [`chrono::TimeDelta`] to a [`jiff::Span`].
///
/// This conversion is infallible. The resulting `Span` has non-zero units
/// only in seconds and below (never years/months/weeks/days), matching the
/// behavior of Jiff's own `TryFrom<SignedDuration> for Span`.
///
/// # Example
///
/// ```
/// use jiff_chrono::ConvertFrom as _;
///
/// let td = chrono::TimeDelta::new(90, 500_000_000).unwrap();
/// let span = jiff::Span::convert_from(td);
/// assert_eq!(span.get_seconds(), 90);
/// assert_eq!(span.get_milliseconds(), 500);
/// ```
impl ConvertFrom<ChronoTimeDelta> for JiffSpan {
    fn convert_from(v: ChronoTimeDelta) -> JiffSpan {
        let sd = JiffSignedDuration::convert_from(v);
        // `Span` has sufficient range to represent any `SignedDuration`
        // derived from a `TimeDelta`, so this conversion cannot fail.
        JiffSpan::try_from(sd).unwrap()
    }
}

/// Converts from a [`jiff::Span`] to a [`chrono::TimeDelta`].
///
/// This conversion is fallible. It fails if the span has any non-zero
/// calendar units (years, months, weeks, or days), since those units
/// cannot be meaningfully converted to an absolute `TimeDelta` without a
/// reference date. It also fails if the resulting duration is outside
/// `TimeDelta`'s range.
///
/// If you need to convert a span with calendar units, you have two
/// options:
///
/// * If the span only adds nonzero `days` and you are comfortable
///   treating each day as exactly 24 hours (ignoring DST), use
///   [`crate::lossy::span_to_timedelta_days_are_24h`].
/// * Otherwise, resolve the span to a [`jiff::SignedDuration`] via
///   [`jiff::Span::to_duration`] with an explicit reference point, then
///   convert the resulting `SignedDuration`.
///
/// # Example
///
/// ```
/// use jiff::ToSpan;
/// use jiff_chrono::ConvertTryFrom as _;
///
/// let span = 2.hours().minutes(30);
/// let td = chrono::TimeDelta::convert_try_from(span)?;
/// assert_eq!(td.num_minutes(), 150);
///
/// // Calendar units are rejected.
/// let span = 1.month();
/// assert!(chrono::TimeDelta::convert_try_from(span).is_err());
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
impl ConvertTryFrom<JiffSpan> for ChronoTimeDelta {
    type Error = Error;

    fn convert_try_from(v: JiffSpan) -> Result<ChronoTimeDelta, Error> {
        // Jiff's own `TryFrom<Span> for SignedDuration` rejects spans whose
        // largest unit requires a reference date (years, months, weeks,
        // days), which is exactly the policy we want here.
        let sd = JiffSignedDuration::try_from(v)?;
        ChronoTimeDelta::convert_try_from(sd)
    }
}

/// Converts from a [`chrono::Months`] to a [`jiff::Span`].
///
/// This conversion is infallible. The resulting span has its `months` field
/// set and all other fields zero.
///
/// Note: there is no corresponding conversion for [`chrono::Days`] because,
/// as of `chrono` 0.4.44, the inner `u64` of `chrono::Days` is not exposed
/// through any public accessor. If you have a [`chrono::Days`] value,
/// reconstruct it on the Jiff side using
/// [`jiff::ToSpan::days`](jiff::ToSpan::days) directly.
///
/// # Example
///
/// ```
/// use jiff_chrono::ConvertFrom as _;
///
/// let months = chrono::Months::new(18);
/// let span = jiff::Span::convert_from(months);
/// assert_eq!(span.get_months(), 18);
/// assert_eq!(span.get_years(), 0);
/// ```
impl ConvertFrom<ChronoMonths> for JiffSpan {
    fn convert_from(v: ChronoMonths) -> JiffSpan {
        use jiff::ToSpan as _;
        // `Months::as_u32()` returns a `u32`, which fits losslessly in the
        // `i64` accepted by `Span::months`. `Span` internally caps months
        // at a value well above `u32::MAX`, so this cannot fail.
        i64::from(v.as_u32()).months()
    }
}

#[cfg(test)]
mod tests {
    use jiff::ToSpan;

    use crate::traits::{ConvertInto as _, ConvertTryInto as _};

    use super::*;

    quickcheck::quickcheck! {
        /// Round-trip `TimeDelta` through `SignedDuration`. The chrono side
        /// is the narrower domain, so this is the interesting direction.
        fn prop_timedelta_to_signed_duration_roundtrip(secs: i64, nanos: u32) -> quickcheck::TestResult {
            let nanos = nanos % 1_000_000_000;
            let Some(td) = ChronoTimeDelta::new(secs, nanos) else {
                return quickcheck::TestResult::discard();
            };
            let sd: JiffSignedDuration = td.convert_into();
            let back: ChronoTimeDelta = sd.convert_try_into().unwrap();
            quickcheck::TestResult::from_bool(td == back)
        }
    }

    #[test]
    fn span_with_calendar_units_is_rejected() {
        assert!(ChronoTimeDelta::convert_try_from(1.year()).is_err());
        assert!(ChronoTimeDelta::convert_try_from(1.month()).is_err());
        assert!(ChronoTimeDelta::convert_try_from(1.week()).is_err());
        assert!(ChronoTimeDelta::convert_try_from(1.day()).is_err());
    }

    #[test]
    fn span_with_time_units_converts() {
        let span = 2.hours().minutes(30).seconds(15);
        let td = ChronoTimeDelta::convert_try_from(span).unwrap();
        assert_eq!(td.num_seconds(), 2 * 3600 + 30 * 60 + 15);
    }

    #[test]
    fn signed_duration_negative_fractional_roundtrips_via_timedelta() {
        let sd = JiffSignedDuration::new(-1, -500_000_000);
        let td: ChronoTimeDelta = sd.convert_try_into().unwrap();
        assert_eq!(td.num_milliseconds(), -1_500);
        let back: JiffSignedDuration = td.convert_into();
        assert_eq!(back, sd);
    }

    #[test]
    fn signed_duration_max_is_rejected_by_timedelta() {
        assert!(
            ChronoTimeDelta::convert_try_from(JiffSignedDuration::MAX).is_err()
        );
    }
}
