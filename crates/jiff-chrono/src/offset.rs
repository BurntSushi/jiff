use chrono::FixedOffset as ChronoFixedOffset;
use jiff::tz::Offset as JiffOffset;

use crate::{
    error::{err, Error},
    traits::{ConvertFrom, ConvertTryFrom},
};

/// Converts from a [`chrono::FixedOffset`] to a [`jiff::tz::Offset`].
///
/// This conversion is infallible because chrono's offset range
/// (`±23:59:59`) is strictly smaller than Jiff's (`±25:59:59`).
///
/// # Example
///
/// ```
/// use jiff_chrono::ConvertFrom as _;
///
/// let chrono_offset = chrono::FixedOffset::east_opt(-5 * 3600).unwrap();
/// let jiff_offset = jiff::tz::Offset::convert_from(chrono_offset);
/// assert_eq!(jiff_offset, jiff::tz::offset(-5));
/// ```
impl ConvertFrom<ChronoFixedOffset> for JiffOffset {
    fn convert_from(v: ChronoFixedOffset) -> JiffOffset {
        // `FixedOffset::local_minus_utc()` returns seconds in
        // `-86_399..=86_399`. That is a strict subset of Jiff's
        // `-93_599..=93_599`, so this unwrap never fires.
        JiffOffset::from_seconds(v.local_minus_utc()).unwrap()
    }
}

/// Converts from a [`jiff::tz::Offset`] to a [`chrono::FixedOffset`].
///
/// This conversion is fallible because Jiff's offset range (`±25:59:59`) is
/// wider than chrono's (`±23:59:59`). In practice all offsets used by real
/// IANA time zones fit comfortably within chrono's range.
///
/// # Example
///
/// ```
/// use jiff_chrono::ConvertTryFrom as _;
///
/// let jiff_offset = jiff::tz::offset(-5);
/// let chrono_offset =
///     chrono::FixedOffset::convert_try_from(jiff_offset)?;
/// assert_eq!(chrono_offset.local_minus_utc(), -5 * 3600);
///
/// // Offsets beyond chrono's ±23:59:59 limit are rejected.
/// let big = jiff::tz::Offset::from_seconds(25 * 3600).unwrap();
/// assert!(chrono::FixedOffset::convert_try_from(big).is_err());
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
impl ConvertTryFrom<JiffOffset> for ChronoFixedOffset {
    type Error = Error;

    fn convert_try_from(v: JiffOffset) -> Result<ChronoFixedOffset, Error> {
        ChronoFixedOffset::east_opt(v.seconds()).ok_or_else(|| {
            err!(
                "failed to convert Jiff offset of {v} seconds to \
                 `chrono::FixedOffset`: chrono requires the offset to be \
                 within ±23:59:59",
            )
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::traits::{ConvertInto as _, ConvertTryInto as _};

    use super::*;

    quickcheck::quickcheck! {
        fn prop_fixed_offset_to_jiff_roundtrip(seconds: i32) -> quickcheck::TestResult {
            // Restrict to chrono's valid range.
            if !(-86_399..=86_399).contains(&seconds) {
                return quickcheck::TestResult::discard();
            }
            let chrono_offset = ChronoFixedOffset::east_opt(seconds).unwrap();
            let jiff_offset: JiffOffset = chrono_offset.convert_into();
            let back: ChronoFixedOffset =
                jiff_offset.convert_try_into().unwrap();
            quickcheck::TestResult::from_bool(chrono_offset == back)
        }
    }

    #[test]
    fn jiff_offset_beyond_chrono_is_rejected() {
        let big = JiffOffset::from_seconds(25 * 3600).unwrap();
        assert!(ChronoFixedOffset::convert_try_from(big).is_err());
    }
}
