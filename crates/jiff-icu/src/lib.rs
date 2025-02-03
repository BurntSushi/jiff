/*!
This crate provides conversion routines between [`jiff`] and
[`icu`](https://docs.rs/icu/1/).

The conversion routines are implemented via conversion traits defined in this
crate. The traits mirror the [`From`], [`Into`], [`TryFrom`] and [`TryInto`]
traits from the standard library.

# Available conversions

* [`jiff::civil::DateTime`] infallibly converts to
[`icu::calendar::DateTime`](icu_calendar::DateTime).
The reverse is fallible.
* [`jiff::civil::Date`] infallibly converts to
[`icu::calendar::Date`](icu_calendar::Date).
The reverse is fallible.
* [`jiff::civil::Time`] infallibly converts to
[`icu::calendar::Time`](icu_calendar::Time).
The reverse is fallible.
* [`jiff::civil::Weekday`] infallibly converts to
[`icu::calendar::types::IsoWeekday`](icu_calendar::types::IsoWeekday).
The reverse is also infallible.

# Format a datetime in another locale

This example shows how one can bridge `jiff` to `icu` in order to format a
datetime in a particular locale. This makes use of the infallible
[`ConvertFrom`] trait to convert a [`jiff::civil::DateTime`] into a
[`icu::calendar::DateTime`](icu_calendar::DateTime).

```
use icu::{
    calendar::{gregorian::Gregorian, DateTime},
    datetime::TypedDateTimeFormatter,
    locid::locale,
};
use jiff::Zoned;
use jiff_icu::{ConvertFrom as _};

let zdt: Zoned = "2024-09-10T23:37:20-04[America/New_York]".parse()?;
let icu_datetime = DateTime::convert_from(zdt.datetime()).to_calendar(Gregorian);

// Format for the en-GB locale:
let formatter = TypedDateTimeFormatter::try_new(
    &locale!("en-GB").into(),
    Default::default(),
)?;
assert_eq!(
    formatter.format(&icu_datetime).to_string(),
    "10 Sept 2024, 23:37:20",
);

// Or in the en-US locale:
let formatter = TypedDateTimeFormatter::try_new(
    &locale!("en-US").into(),
    Default::default(),
)?;
assert_eq!(
    formatter.format(&icu_datetime).to_string(),
    "Sep 10, 2024, 11:37:20 PM",
);

# Ok::<(), Box<dyn std::error::Error>>(())
```

# Convert to another calendar

While Jiff only supports the Gregorian calendar (technically the ISO
8601 calendar), ICU4X supports [many calendars](icu_calendar). This
example shows how to convert a date in the Hebrew calendar to a Jiff
date. This makes use of the fallible [`ConvertTryFrom`] trait to
convert a [`icu::calendar::DateTime`](icu_calendar::DateTime) into a
[`jiff::civil::DateTime`]:

```
use icu::{
    calendar::{DateTime as IcuDateTime},
};
use jiff::civil::DateTime;
use jiff_icu::{ConvertTryFrom as _};

let datetime = IcuDateTime::try_new_hebrew_datetime(5785, 5, 4, 17, 30, 0)?;
let zdt = DateTime::convert_try_from(datetime)?.in_tz("America/New_York")?;
assert_eq!(zdt.to_string(), "2025-02-02T17:30:00-05:00[America/New_York]");

# Ok::<(), Box<dyn std::error::Error>>(())
```
*/

#![no_std]
#![deny(missing_docs)]

#[cfg(any(test, feature = "std"))]
extern crate std;

#[cfg(any(test, feature = "alloc"))]
extern crate alloc;

use icu_calendar::{
    types::IsoWeekday as IcuWeekday, AsCalendar as IcuAsCalendar,
    Date as IcuDate, DateTime as IcuDateTime, Iso, Time as IcuTime,
};
use jiff::civil::{
    Date as JiffDate, DateTime as JiffDateTime, Time as JiffTime,
    Weekday as JiffWeekday,
};

use self::error::err;
pub use self::{
    error::Error,
    traits::{ConvertFrom, ConvertInto, ConvertTryFrom, ConvertTryInto},
};

mod error;
mod traits;

/// Converts from a [`icu_calendar::DateTime<Iso>`](icu_calendar::DateTime) to
/// a [`jiff::civil::DateTime`].
///
/// # Examples
///
/// ```
/// use jiff_icu::{ConvertTryFrom as _};
///
/// let icu_datetime = icu_calendar::DateTime::local_unix_epoch();
/// let jiff_datetime = jiff::civil::DateTime::convert_try_from(icu_datetime)?;
/// assert_eq!(jiff_datetime.to_string(), "1970-01-01T00:00:00");
///
/// let icu_datetime = icu_calendar::DateTime::try_new_iso_datetime(
///     2025, 1, 30, 17, 58, 30,
/// ).unwrap();
/// let jiff_datetime = jiff::civil::DateTime::convert_try_from(icu_datetime)?;
/// assert_eq!(jiff_datetime.to_string(), "2025-01-30T17:58:30");
///
/// let icu_datetime = icu_calendar::DateTime::try_new_iso_datetime(
///     -9999, 1, 1, 0, 0, 0,
/// ).unwrap();
/// let jiff_datetime = jiff::civil::DateTime::convert_try_from(icu_datetime)?;
/// assert_eq!(jiff_datetime.to_string(), "-009999-01-01T00:00:00");
///
/// let icu_datetime = icu_calendar::DateTime::try_new_iso_datetime(
///     9999, 12, 31, 23, 59, 59,
/// ).unwrap();
/// let jiff_datetime = jiff::civil::DateTime::convert_try_from(icu_datetime)?;
/// assert_eq!(jiff_datetime.to_string(), "9999-12-31T23:59:59");
///
/// let icu_datetime = icu_calendar::DateTime::try_new_iso_datetime(
///     0, 1, 30, 0, 0, 0,
/// ).unwrap();
/// let jiff_datetime = jiff::civil::DateTime::convert_try_from(icu_datetime)?;
/// assert_eq!(jiff_datetime.to_string(), "0000-01-30T00:00:00");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
impl<C: IcuAsCalendar> ConvertTryFrom<IcuDateTime<C>> for JiffDateTime {
    type Error = Error;

    fn convert_try_from(v: IcuDateTime<C>) -> Result<JiffDateTime, Error> {
        let date: JiffDate = v.date.convert_try_into()?;
        let time: JiffTime = v.time.convert_try_into()?;
        Ok(JiffDateTime::from_parts(date, time))
    }
}

/// Converts from a [`jiff::civil::DateTime`] to a
/// [`icu_calendar::DateTime<Iso>`](icu_calendar::DateTime).
///
/// # Examples
///
/// ```
/// use jiff_icu::{ConvertFrom as _};
///
/// let jiff_datetime = jiff::civil::date(2025, 1, 30).at(17, 58, 30, 0);
/// let icu_datetime = icu_calendar::DateTime::convert_from(jiff_datetime);
/// assert_eq!(
///     format!("{:?}", icu_datetime.date),
///     "Date(2025-1-30, default era, for calendar ISO)",
/// );
/// assert_eq!(
///     format!("{:?}", icu_datetime.time),
///     "Time { hour: IsoHour(17), minute: IsoMinute(58), second: IsoSecond(30), nanosecond: NanoSecond(0) }",
/// );
///
/// let jiff_datetime = jiff::civil::DateTime::MIN;
/// let icu_datetime = icu_calendar::DateTime::convert_from(jiff_datetime);
/// assert_eq!(
///     format!("{:?}", icu_datetime.date),
///     "Date(-9999-1-1, default era, for calendar ISO)",
/// );
/// assert_eq!(
///     format!("{:?}", icu_datetime.time),
///     "Time { hour: IsoHour(0), minute: IsoMinute(0), second: IsoSecond(0), nanosecond: NanoSecond(0) }",
/// );
///
/// let jiff_datetime = jiff::civil::DateTime::MAX;
/// let icu_datetime = icu_calendar::DateTime::convert_from(jiff_datetime);
/// assert_eq!(
///     format!("{:?}", icu_datetime.date),
///     "Date(9999-12-31, default era, for calendar ISO)",
/// );
/// assert_eq!(
///     format!("{:?}", icu_datetime.time),
///     "Time { hour: IsoHour(23), minute: IsoMinute(59), second: IsoSecond(59), nanosecond: NanoSecond(999999999) }",
/// );
///
/// let jiff_datetime = jiff::civil::date(0, 1, 30).at(0, 0, 0, 0);
/// let icu_datetime = icu_calendar::DateTime::convert_from(jiff_datetime);
/// assert_eq!(
///     format!("{:?}", icu_datetime.date),
///     "Date(0-1-30, default era, for calendar ISO)",
/// );
/// assert_eq!(
///     format!("{:?}", icu_datetime.time),
///     "Time { hour: IsoHour(0), minute: IsoMinute(0), second: IsoSecond(0), nanosecond: NanoSecond(0) }",
/// );
/// ```
impl ConvertFrom<JiffDateTime> for IcuDateTime<Iso> {
    fn convert_from(v: JiffDateTime) -> IcuDateTime<Iso> {
        let date: IcuDate<Iso> = v.date().convert_into();
        let time: IcuTime = v.time().convert_into();
        IcuDateTime::new(date, time)
    }
}

/// Converts from a [`icu_calendar::Date`] to a [`jiff::civil::Date`].
///
/// # Examples
///
/// ```
/// use jiff_icu::{ConvertTryFrom as _};
///
/// let icu_date = icu_calendar::Date::unix_epoch();
/// let jiff_date = jiff::civil::Date::convert_try_from(icu_date)?;
/// assert_eq!(jiff_date.to_string(), "1970-01-01");
///
/// let icu_date = icu_calendar::Date::try_new_iso_date(2025, 1, 30).unwrap();
/// let jiff_date = jiff::civil::Date::convert_try_from(icu_date)?;
/// assert_eq!(jiff_date.to_string(), "2025-01-30");
///
/// let icu_date = icu_calendar::Date::try_new_iso_date(-9999, 1, 1).unwrap();
/// let jiff_date = jiff::civil::Date::convert_try_from(icu_date)?;
/// assert_eq!(jiff_date.to_string(), "-009999-01-01");
///
/// let icu_date = icu_calendar::Date::try_new_iso_date(9999, 12, 31).unwrap();
/// let jiff_date = jiff::civil::Date::convert_try_from(icu_date)?;
/// assert_eq!(jiff_date.to_string(), "9999-12-31");
///
/// let icu_date = icu_calendar::Date::try_new_iso_date(0, 1, 30).unwrap();
/// let jiff_date = jiff::civil::Date::convert_try_from(icu_date)?;
/// assert_eq!(jiff_date.to_string(), "0000-01-30");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// This trait implementation is generic over calendars:
///
/// ```
/// use jiff_icu::{ConvertTryFrom as _};
///
/// let icu_date = icu_calendar::Date::try_new_hebrew_date(5785, 5, 4).unwrap();
/// let jiff_date = jiff::civil::Date::convert_try_from(icu_date)?;
/// assert_eq!(jiff_date.to_string(), "2025-02-02");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
impl<C: IcuAsCalendar> ConvertTryFrom<IcuDate<C>> for JiffDate {
    type Error = Error;

    fn convert_try_from(v: IcuDate<C>) -> Result<JiffDate, Error> {
        let v = v.to_iso();
        let year = v.year().number;
        let year = i16::try_from(year).map_err(|_| {
            err!("failed to convert `icu` year of {year} to `i16`")
        })?;

        let month = v.month().ordinal;
        let month = i8::try_from(month).map_err(|_| {
            err!("failed to convert `icu` month of {month} to `i8`")
        })?;

        let day = v.day_of_month().0;
        let day = i8::try_from(day).map_err(|_| {
            err!("failed to convert `icu` day of {day} to `i8`")
        })?;
        Ok(JiffDate::new(year, month, day)?)
    }
}

/// Converts from a [`jiff::civil::Date`] to a
/// [`icu_calendar::Date<Iso>`](icu_calendar::Date).
///
/// # Examples
///
/// ```
/// use jiff_icu::{ConvertFrom as _};
///
/// let jiff_date = jiff::civil::date(2025, 1, 30);
/// let icu_date = icu_calendar::Date::convert_from(jiff_date);
/// assert_eq!(
///     format!("{icu_date:?}"),
///     "Date(2025-1-30, default era, for calendar ISO)",
/// );
///
/// let jiff_date = jiff::civil::Date::MIN;
/// let icu_date = icu_calendar::Date::convert_from(jiff_date);
/// assert_eq!(
///     format!("{icu_date:?}"),
///     "Date(-9999-1-1, default era, for calendar ISO)",
/// );
///
/// let jiff_date = jiff::civil::Date::MAX;
/// let icu_date = icu_calendar::Date::convert_from(jiff_date);
/// assert_eq!(
///     format!("{icu_date:?}"),
///     "Date(9999-12-31, default era, for calendar ISO)",
/// );
///
/// let jiff_date = jiff::civil::date(0, 1, 30);
/// let icu_date = icu_calendar::Date::convert_from(jiff_date);
/// assert_eq!(
///     format!("{icu_date:?}"),
///     "Date(0-1-30, default era, for calendar ISO)",
/// );
/// ```
///
/// While this trait implementation is not generic over calendars, one can
/// convert an `icu_calendar::Date<Iso>` to a date in another calendar:
///
/// ```
/// use jiff_icu::{ConvertFrom as _};
///
/// let jiff_date = jiff::civil::date(2025, 2, 2);
/// let icu_iso_date = icu_calendar::Date::convert_from(jiff_date);
/// let icu_hebrew_date = icu_iso_date.to_calendar(icu_calendar::hebrew::Hebrew);
/// assert_eq!(
///     format!("{icu_hebrew_date:?}"),
///     "Date(5785-5-4, hebrew era, for calendar Hebrew)",
/// );
/// ```
impl ConvertFrom<JiffDate> for IcuDate<Iso> {
    fn convert_from(v: JiffDate) -> IcuDate<Iso> {
        let year = i32::from(v.year());
        let month = v.month().unsigned_abs();
        let day = v.day().unsigned_abs();
        // All Jiff civil dates are valid ICU4X dates.
        IcuDate::try_new_iso_date(year, month, day).unwrap()
    }
}

/// Converts from a [`icu_calendar::Time`] to a [`jiff::civil::Time`].
///
/// # Examples
///
/// ```
/// use jiff_icu::{ConvertTryFrom as _};
///
/// let icu_time = icu_calendar::Time::try_new(0, 0, 0, 0).unwrap();
/// let jiff_time = jiff::civil::Time::convert_try_from(icu_time)?;
/// assert_eq!(jiff_time, jiff::civil::time(0, 0, 0, 0));
///
/// let icu_time = icu_calendar::Time::try_new(24, 0, 0, 0).unwrap();
/// let jiff_time = jiff::civil::Time::convert_try_from(icu_time)?;
/// assert_eq!(jiff_time, jiff::civil::time(0, 0, 0, 0));
///
/// let icu_time = icu_calendar::Time::try_new(17, 59, 4, 0).unwrap();
/// let jiff_time = jiff::civil::Time::convert_try_from(icu_time)?;
/// assert_eq!(jiff_time, jiff::civil::time(17, 59, 4, 0));
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
impl ConvertTryFrom<IcuTime> for JiffTime {
    type Error = Error;

    fn convert_try_from(v: IcuTime) -> Result<JiffTime, Error> {
        // OK because it's guaranteed by API docs.
        let mut hour = i8::try_from(v.hour.number()).unwrap();
        if hour == 24 {
            hour = 0;
        }

        // OK because it's guaranteed by API docs.
        let minute = i8::try_from(v.minute.number()).unwrap();

        // OK because it's guaranteed by API docs.
        let second = i8::try_from(v.second.number()).unwrap();

        // OK because it's guaranteed by API docs.
        let subsec_nano = i32::try_from(v.nanosecond.number()).unwrap();

        Ok(JiffTime::new(hour, minute, second, subsec_nano)?)
    }
}

/// Converts from a [`jiff::civil::Time`] to a [`icu_calendar::Time`].
///
/// # Examples
///
/// ```
/// use jiff_icu::{ConvertFrom as _};
///
/// let jiff_time = jiff::civil::time(0, 0, 0, 0);
/// let icu_time = icu_calendar::Time::convert_from(jiff_time);
/// assert_eq!(
///     format!("{icu_time:?}"),
///     "Time { hour: IsoHour(0), minute: IsoMinute(0), second: IsoSecond(0), nanosecond: NanoSecond(0) }",
/// );
///
/// let jiff_time = jiff::civil::time(17, 59, 4, 0);
/// let icu_time = icu_calendar::Time::convert_from(jiff_time);
/// assert_eq!(
///     format!("{icu_time:?}"),
///     "Time { hour: IsoHour(17), minute: IsoMinute(59), second: IsoSecond(4), nanosecond: NanoSecond(0) }",
/// );
/// ```
impl ConvertFrom<JiffTime> for IcuTime {
    fn convert_from(v: JiffTime) -> IcuTime {
        let hour = v.hour().unsigned_abs();
        let minute = v.minute().unsigned_abs();
        let second = v.second().unsigned_abs();
        let subsec = v.subsec_nanosecond().unsigned_abs();
        // All Jiff civil times are valid ICU4X times.
        IcuTime::try_new(hour, minute, second, subsec).unwrap()
    }
}

/// Converts from a [`icu_calendar::types::IsoWeekday`] to a
/// [`jiff::civil::Weekday`].
///
/// # Examples
///
/// ```
/// use jiff_icu::{ConvertFrom as _};
///
/// let icu_weekday = icu_calendar::types::IsoWeekday::Wednesday;
/// let jiff_weekday = jiff::civil::Weekday::convert_from(icu_weekday);
/// assert_eq!(jiff_weekday, jiff::civil::Weekday::Wednesday);
/// ```
impl ConvertFrom<IcuWeekday> for JiffWeekday {
    fn convert_from(v: IcuWeekday) -> JiffWeekday {
        match v {
            IcuWeekday::Monday => JiffWeekday::Monday,
            IcuWeekday::Tuesday => JiffWeekday::Tuesday,
            IcuWeekday::Wednesday => JiffWeekday::Wednesday,
            IcuWeekday::Thursday => JiffWeekday::Thursday,
            IcuWeekday::Friday => JiffWeekday::Friday,
            IcuWeekday::Saturday => JiffWeekday::Saturday,
            IcuWeekday::Sunday => JiffWeekday::Sunday,
        }
    }
}

/// Converts from a [`jiff::civil::Weekday`] to a
/// [`icu_calendar::types::IsoWeekday`].
///
/// # Examples
///
/// ```
/// use jiff_icu::{ConvertFrom as _};
///
/// let jiff_weekday = jiff::civil::Weekday::Wednesday;
/// let icu_weekday = icu_calendar::types::IsoWeekday::convert_from(jiff_weekday);
/// assert_eq!(icu_weekday, icu_calendar::types::IsoWeekday::Wednesday);
/// ```
impl ConvertFrom<JiffWeekday> for IcuWeekday {
    fn convert_from(v: JiffWeekday) -> IcuWeekday {
        match v {
            JiffWeekday::Monday => IcuWeekday::Monday,
            JiffWeekday::Tuesday => IcuWeekday::Tuesday,
            JiffWeekday::Wednesday => IcuWeekday::Wednesday,
            JiffWeekday::Thursday => IcuWeekday::Thursday,
            JiffWeekday::Friday => IcuWeekday::Friday,
            JiffWeekday::Saturday => IcuWeekday::Saturday,
            JiffWeekday::Sunday => IcuWeekday::Sunday,
        }
    }
}

#[cfg(test)]
mod tests {
    use jiff::ToSpan;

    use super::*;

    /// This exhaustively confirms that all valid Jiff dates are also valid
    /// ICU4X dates.
    ///
    /// I believe the reverse is not true, although it's not quite clear from
    /// ICU4X's docs. (Although I haven't done an exhaustive search.)
    ///
    /// This test is ignored because it takes forever in debug mode (sigh). In
    /// release mode it is quite snappy. But I have run it. And the doc tests
    /// above check the min and max values.
    #[test]
    #[ignore]
    fn all_jiff_dates_are_valid_icu_dates() {
        for jiff_date in jiff::civil::Date::MIN.series(1.day()) {
            let icu_date: IcuDate<Iso> = jiff_date.convert_try_into().unwrap();
            let got: jiff::civil::Date = icu_date.convert_try_into().unwrap();
            assert_eq!(jiff_date, got);
        }
    }

    /// Like the above, but for civil times.
    ///
    /// We skip nanoseconds because it would take too long to exhaustively
    /// test. Without nanoseconds, this is quick enough to run in debug mode.
    #[test]
    fn all_jiff_times_are_valid_icu_times() {
        for jiff_time in jiff::civil::Time::MIN.series(1.second()) {
            let icu_time: IcuTime = jiff_time.convert_try_into().unwrap();
            let got: jiff::civil::Time = icu_time.convert_try_into().unwrap();
            assert_eq!(jiff_time, got);
        }
    }
}
