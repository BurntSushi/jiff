use chrono::{
    Datelike as _, NaiveDate as ChronoNaiveDate,
    NaiveDateTime as ChronoNaiveDateTime, NaiveTime as ChronoNaiveTime,
    Timelike as _, Weekday as ChronoWeekday,
};
use jiff::civil::{
    Date as JiffDate, DateTime as JiffDateTime, Time as JiffTime,
    Weekday as JiffWeekday,
};

use crate::{
    error::{err, Error},
    traits::{ConvertFrom, ConvertInto as _, ConvertTryFrom},
};

/// Converts from a [`jiff::civil::Date`] to a [`chrono::NaiveDate`].
///
/// This conversion is infallible because the range of valid Jiff dates
/// (years `-9999..=9999`) is strictly smaller than the range of valid
/// chrono dates.
///
/// # Example
///
/// ```
/// use jiff_chrono::ConvertFrom as _;
///
/// let jiff_date = jiff::civil::date(2025, 1, 30);
/// let chrono_date = chrono::NaiveDate::convert_from(jiff_date);
/// assert_eq!(chrono_date.to_string(), "2025-01-30");
///
/// let chrono_date = chrono::NaiveDate::convert_from(jiff::civil::Date::MIN);
/// assert_eq!(chrono_date.to_string(), "-9999-01-01");
///
/// let chrono_date = chrono::NaiveDate::convert_from(jiff::civil::Date::MAX);
/// assert_eq!(chrono_date.to_string(), "9999-12-31");
/// ```
impl ConvertFrom<JiffDate> for ChronoNaiveDate {
    fn convert_from(v: JiffDate) -> ChronoNaiveDate {
        // All Jiff dates are valid chrono dates.
        ChronoNaiveDate::from_ymd_opt(
            i32::from(v.year()),
            u32::from(v.month().unsigned_abs()),
            u32::from(v.day().unsigned_abs()),
        )
        .unwrap()
    }
}

/// Converts from a [`chrono::NaiveDate`] to a [`jiff::civil::Date`].
///
/// This conversion is fallible because chrono's date range is wider than
/// Jiff's (Jiff years are limited to `-9999..=9999`).
///
/// # Example
///
/// ```
/// use jiff_chrono::ConvertTryFrom as _;
///
/// let chrono_date =
///     chrono::NaiveDate::from_ymd_opt(2025, 1, 30).unwrap();
/// let jiff_date = jiff::civil::Date::convert_try_from(chrono_date)?;
/// assert_eq!(jiff_date.to_string(), "2025-01-30");
///
/// // Years outside Jiff's range fail:
/// let chrono_date =
///     chrono::NaiveDate::from_ymd_opt(50_000, 1, 1).unwrap();
/// assert!(jiff::civil::Date::convert_try_from(chrono_date).is_err());
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
impl ConvertTryFrom<ChronoNaiveDate> for JiffDate {
    type Error = Error;

    fn convert_try_from(v: ChronoNaiveDate) -> Result<JiffDate, Error> {
        let year = v.year();
        let year = i16::try_from(year).map_err(|_| {
            err!("failed to convert chrono year of {year} to Jiff `i16` year")
        })?;
        // NaiveDate guarantees month in 1..=12 and day in 1..=31, so the
        // casts below never lose information.
        let month = v.month() as i8;
        let day = v.day() as i8;
        Ok(JiffDate::new(year, month, day)?)
    }
}

/// Converts from a [`jiff::civil::Time`] to a [`chrono::NaiveTime`].
///
/// This conversion is infallible. Jiff times never represent leap seconds,
/// so the resulting chrono time always has nanoseconds in `0..1_000_000_000`.
///
/// # Example
///
/// ```
/// use jiff_chrono::ConvertFrom as _;
///
/// let jiff_time = jiff::civil::time(17, 58, 30, 0);
/// let chrono_time = chrono::NaiveTime::convert_from(jiff_time);
/// assert_eq!(chrono_time.to_string(), "17:58:30");
///
/// let chrono_time =
///     chrono::NaiveTime::convert_from(jiff::civil::Time::MAX);
/// assert_eq!(chrono_time.to_string(), "23:59:59.999999999");
/// ```
impl ConvertFrom<JiffTime> for ChronoNaiveTime {
    fn convert_from(v: JiffTime) -> ChronoNaiveTime {
        // All Jiff times are valid non-leap chrono times.
        ChronoNaiveTime::from_hms_nano_opt(
            u32::from(v.hour().unsigned_abs()),
            u32::from(v.minute().unsigned_abs()),
            u32::from(v.second().unsigned_abs()),
            v.subsec_nanosecond().unsigned_abs(),
        )
        .unwrap()
    }
}

/// Converts from a [`chrono::NaiveTime`] to a [`jiff::civil::Time`].
///
/// This conversion is fallible. A chrono time representing a leap second
/// (nanoseconds `>= 1_000_000_000`) is rejected, since Jiff civil times
/// do not model leap seconds. If you want to accept leap-second values
/// by clamping them to `:59.999999999`, use
/// [`crate::lossy::naive_time_saturating`].
///
/// # Example
///
/// ```
/// use jiff_chrono::ConvertTryFrom as _;
///
/// let chrono_time =
///     chrono::NaiveTime::from_hms_nano_opt(17, 58, 30, 0).unwrap();
/// let jiff_time = jiff::civil::Time::convert_try_from(chrono_time)?;
/// assert_eq!(jiff_time, jiff::civil::time(17, 58, 30, 0));
///
/// // Leap-second values are rejected.
/// let leap =
///     chrono::NaiveTime::from_hms_nano_opt(23, 59, 59, 1_500_000_000)
///         .unwrap();
/// assert!(jiff::civil::Time::convert_try_from(leap).is_err());
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
impl ConvertTryFrom<ChronoNaiveTime> for JiffTime {
    type Error = Error;

    fn convert_try_from(v: ChronoNaiveTime) -> Result<JiffTime, Error> {
        let nano = v.nanosecond();
        if nano >= 1_000_000_000 {
            return Err(err!(
                "chrono `NaiveTime` with nanosecond value {nano} represents \
                 a leap second, which is not representable in \
                 `jiff::civil::Time`",
            ));
        }
        // NaiveTime guarantees hour in 0..24, minute in 0..60, second in 0..60,
        // and (now) nano in 0..1_000_000_000.
        let hour = v.hour() as i8;
        let minute = v.minute() as i8;
        let second = v.second() as i8;
        let nano = nano as i32;
        Ok(JiffTime::new(hour, minute, second, nano)?)
    }
}

/// Converts from a [`jiff::civil::DateTime`] to a [`chrono::NaiveDateTime`].
///
/// This conversion is infallible.
///
/// # Example
///
/// ```
/// use jiff_chrono::ConvertFrom as _;
///
/// let jiff_datetime = jiff::civil::date(2025, 1, 30).at(17, 58, 30, 0);
/// let chrono_datetime =
///     chrono::NaiveDateTime::convert_from(jiff_datetime);
/// assert_eq!(chrono_datetime.to_string(), "2025-01-30 17:58:30");
/// ```
impl ConvertFrom<JiffDateTime> for ChronoNaiveDateTime {
    fn convert_from(v: JiffDateTime) -> ChronoNaiveDateTime {
        ChronoNaiveDateTime::new(v.date().convert_into(), v.time().convert_into())
    }
}

/// Converts from a [`chrono::NaiveDateTime`] to a [`jiff::civil::DateTime`].
///
/// This conversion is fallible for the same reasons as the `NaiveDate` and
/// `NaiveTime` conversions.
///
/// # Example
///
/// ```
/// use jiff_chrono::ConvertTryFrom as _;
///
/// let chrono_datetime = chrono::NaiveDate::from_ymd_opt(2025, 1, 30)
///     .unwrap()
///     .and_hms_opt(17, 58, 30)
///     .unwrap();
/// let jiff_datetime =
///     jiff::civil::DateTime::convert_try_from(chrono_datetime)?;
/// assert_eq!(jiff_datetime.to_string(), "2025-01-30T17:58:30");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
impl ConvertTryFrom<ChronoNaiveDateTime> for JiffDateTime {
    type Error = Error;

    fn convert_try_from(
        v: ChronoNaiveDateTime,
    ) -> Result<JiffDateTime, Error> {
        let date = JiffDate::convert_try_from(v.date())?;
        let time = JiffTime::convert_try_from(v.time())?;
        Ok(JiffDateTime::from_parts(date, time))
    }
}

/// Converts from a [`jiff::civil::Weekday`] to a [`chrono::Weekday`].
///
/// # Example
///
/// ```
/// use jiff_chrono::ConvertFrom as _;
///
/// let jiff_weekday = jiff::civil::Weekday::Wednesday;
/// let chrono_weekday = chrono::Weekday::convert_from(jiff_weekday);
/// assert_eq!(chrono_weekday, chrono::Weekday::Wed);
/// ```
impl ConvertFrom<JiffWeekday> for ChronoWeekday {
    fn convert_from(v: JiffWeekday) -> ChronoWeekday {
        match v {
            JiffWeekday::Monday => ChronoWeekday::Mon,
            JiffWeekday::Tuesday => ChronoWeekday::Tue,
            JiffWeekday::Wednesday => ChronoWeekday::Wed,
            JiffWeekday::Thursday => ChronoWeekday::Thu,
            JiffWeekday::Friday => ChronoWeekday::Fri,
            JiffWeekday::Saturday => ChronoWeekday::Sat,
            JiffWeekday::Sunday => ChronoWeekday::Sun,
        }
    }
}

/// Converts from a [`chrono::Weekday`] to a [`jiff::civil::Weekday`].
///
/// # Example
///
/// ```
/// use jiff_chrono::ConvertFrom as _;
///
/// let chrono_weekday = chrono::Weekday::Wed;
/// let jiff_weekday = jiff::civil::Weekday::convert_from(chrono_weekday);
/// assert_eq!(jiff_weekday, jiff::civil::Weekday::Wednesday);
/// ```
impl ConvertFrom<ChronoWeekday> for JiffWeekday {
    fn convert_from(v: ChronoWeekday) -> JiffWeekday {
        match v {
            ChronoWeekday::Mon => JiffWeekday::Monday,
            ChronoWeekday::Tue => JiffWeekday::Tuesday,
            ChronoWeekday::Wed => JiffWeekday::Wednesday,
            ChronoWeekday::Thu => JiffWeekday::Thursday,
            ChronoWeekday::Fri => JiffWeekday::Friday,
            ChronoWeekday::Sat => JiffWeekday::Saturday,
            ChronoWeekday::Sun => JiffWeekday::Sunday,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::traits::{ConvertInto as _, ConvertTryInto as _};

    use super::*;

    fn arb_date(seed: u32) -> Option<JiffDate> {
        // Map the seed to every valid Jiff date:
        //     years  -9999..=9999 (20_000 values)
        //     months 1..=12
        //     days   1..=31
        let year = (seed % 20_000) as i16 - 9999;
        let month = ((seed / 20_000) % 12) as i8 + 1;
        let day = ((seed / (20_000 * 12)) % 31) as i8 + 1;
        JiffDate::new(year, month, day).ok()
    }

    fn arb_time(seed: u64) -> JiffTime {
        let nano = (seed % 1_000_000_000) as i32;
        let second = ((seed / 1_000_000_000) % 60) as i8;
        let minute = ((seed / (1_000_000_000 * 60)) % 60) as i8;
        let hour = ((seed / (1_000_000_000 * 3_600)) % 24) as i8;
        JiffTime::new(hour, minute, second, nano).unwrap()
    }

    quickcheck::quickcheck! {
        fn prop_date_roundtrip(seed: u32) -> quickcheck::TestResult {
            let Some(d) = arb_date(seed) else {
                return quickcheck::TestResult::discard();
            };
            let chrono_date: ChronoNaiveDate = d.convert_into();
            let back: JiffDate = chrono_date.convert_try_into().unwrap();
            quickcheck::TestResult::from_bool(d == back)
        }

        fn prop_time_roundtrip(seed: u64) -> bool {
            let t = arb_time(seed);
            let chrono_time: ChronoNaiveTime = t.convert_into();
            let back: JiffTime = chrono_time.convert_try_into().unwrap();
            t == back
        }

        fn prop_datetime_roundtrip(dseed: u32, tseed: u64) -> quickcheck::TestResult {
            let Some(d) = arb_date(dseed) else {
                return quickcheck::TestResult::discard();
            };
            let dt = JiffDateTime::from_parts(d, arb_time(tseed));
            let chrono_dt: ChronoNaiveDateTime = dt.convert_into();
            let back: JiffDateTime = chrono_dt.convert_try_into().unwrap();
            quickcheck::TestResult::from_bool(dt == back)
        }

        fn prop_weekday_roundtrip(seed: u32) -> quickcheck::TestResult {
            let Some(d) = arb_date(seed) else {
                return quickcheck::TestResult::discard();
            };
            let jw = d.weekday();
            let cw: ChronoWeekday = jw.convert_into();
            let back: JiffWeekday = cw.convert_into();
            quickcheck::TestResult::from_bool(jw == back)
        }
    }

    #[test]
    fn naive_time_leap_second_is_rejected() {
        let leap =
            ChronoNaiveTime::from_hms_nano_opt(23, 59, 59, 1_500_000_000)
                .unwrap();
        assert!(JiffTime::convert_try_from(leap).is_err());
    }

    #[test]
    fn naive_date_outside_jiff_range_is_rejected() {
        let big = ChronoNaiveDate::from_ymd_opt(50_000, 1, 1).unwrap();
        assert!(JiffDate::convert_try_from(big).is_err());
        let small = ChronoNaiveDate::from_ymd_opt(-50_000, 1, 1).unwrap();
        assert!(JiffDate::convert_try_from(small).is_err());
    }
}
