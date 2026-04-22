use chrono::{DateTime as ChronoDateTime, TimeZone as ChronoTimeZone, Utc};
use jiff::Timestamp as JiffTimestamp;

use crate::{
    error::{err, Error},
    traits::{ConvertFrom, ConvertTryFrom},
};

/// Converts from a [`jiff::Timestamp`] to a [`chrono::DateTime<Utc>`](chrono::DateTime).
///
/// This conversion is infallible because Jiff's `Timestamp` range is a
/// subset of chrono's `DateTime<Utc>` range.
///
/// # Example
///
/// ```
/// use jiff_chrono::ConvertFrom as _;
///
/// let jiff_ts: jiff::Timestamp = "2025-01-30T17:58:30Z".parse()?;
/// let chrono_dt = chrono::DateTime::<chrono::Utc>::convert_from(jiff_ts);
/// assert_eq!(chrono_dt.to_rfc3339(), "2025-01-30T17:58:30+00:00");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
impl ConvertFrom<JiffTimestamp> for ChronoDateTime<Utc> {
    fn convert_from(v: JiffTimestamp) -> ChronoDateTime<Utc> {
        // `subsec_nanosecond` is in `-999_999_999..=999_999_999` and shares
        // the sign of the seconds, so after calling `.unsigned_abs()` it
        // fits in `0..1_000_000_000`, which is what `from_timestamp` wants.
        ChronoDateTime::from_timestamp(
            v.as_second(),
            v.subsec_nanosecond().unsigned_abs(),
        )
        .unwrap()
    }
}

/// Converts from a [`chrono::DateTime<Tz>`](chrono::DateTime) to a
/// [`jiff::Timestamp`], for any chrono time zone type.
///
/// This is generic over `Tz: chrono::TimeZone`, so it covers
/// [`chrono::Utc`], [`chrono::FixedOffset`], and (with the `chrono-tz`
/// feature on the chrono side) any `chrono_tz::Tz`. The time-zone
/// information is discarded — only the underlying UTC instant is kept.
///
/// This conversion is fallible. It can fail if:
///
/// * The chrono value falls outside Jiff's supported timestamp range.
/// * The chrono value represents a leap second
///   (`timestamp_subsec_nanos() >= 1_000_000_000`), which Jiff does not
///   model. Use [`crate::lossy::utc_datetime_saturating`] if you want to
///   clamp leap-second readings instead.
///
/// # Example
///
/// ```
/// use jiff_chrono::ConvertTryFrom as _;
///
/// // `DateTime<Utc>`:
/// let cdt: chrono::DateTime<chrono::Utc> =
///     "2025-01-30T17:58:30Z".parse()?;
/// let ts = jiff::Timestamp::convert_try_from(cdt)?;
/// assert_eq!(ts.to_string(), "2025-01-30T17:58:30Z");
///
/// // `DateTime<FixedOffset>`, converted directly without going through UTC:
/// let cdt = chrono::DateTime::parse_from_rfc3339(
///     "2025-01-30T12:58:30-05:00",
/// )?;
/// let ts = jiff::Timestamp::convert_try_from(cdt)?;
/// assert_eq!(ts.to_string(), "2025-01-30T17:58:30Z");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
impl<Tz: ChronoTimeZone> ConvertTryFrom<ChronoDateTime<Tz>> for JiffTimestamp {
    type Error = Error;

    fn convert_try_from(
        v: ChronoDateTime<Tz>,
    ) -> Result<JiffTimestamp, Error> {
        let secs = v.timestamp();
        let nanos = v.timestamp_subsec_nanos();
        if nanos >= 1_000_000_000 {
            return Err(err!(
                "chrono `DateTime` subsec nanos {nanos} represent a \
                 leap second, which is not representable in \
                 `jiff::Timestamp`",
            ));
        }
        // `nanos` is in `0..1_000_000_000`, which fits in `i32` with a
        // non-negative value. `Timestamp::new` rebalances negative seconds
        // with positive nanos, so this construction is safe.
        Ok(JiffTimestamp::new(secs, nanos as i32)?)
    }
}

#[cfg(test)]
mod tests {
    use crate::traits::{ConvertInto as _, ConvertTryInto as _};

    use super::*;

    quickcheck::quickcheck! {
        fn prop_timestamp_roundtrip(secs: i64, nanos: u32) -> quickcheck::TestResult {
            let nanos = (nanos % 1_000_000_000) as i32;
            let Ok(ts) = JiffTimestamp::new(secs, nanos) else {
                return quickcheck::TestResult::discard();
            };
            let cdt: ChronoDateTime<Utc> = ts.convert_into();
            let back: JiffTimestamp = cdt.convert_try_into().unwrap();
            quickcheck::TestResult::from_bool(ts == back)
        }
    }
}
