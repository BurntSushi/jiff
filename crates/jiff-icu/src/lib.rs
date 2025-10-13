/*!
This crate provides conversion routines between [`jiff`] and
[`icu`](https://docs.rs/icu/2/).

The conversion routines are implemented via conversion traits defined in this
crate. The traits mirror the [`From`], [`Into`], [`TryFrom`] and [`TryInto`]
traits from the standard library.

# Available conversions

* [`jiff::Zoned`] infallibly converts to
[`icu::time::ZonedDateTime`](icu_time::ZonedDateTime).
The reverse is unavailable.
* [`jiff::civil::DateTime`] infallibly converts to
[`icu::time::DateTime`](icu_time::DateTime).
The reverse is fallible.
* [`jiff::civil::Date`] infallibly converts to
[`icu::calendar::Date`](icu_calendar::Date).
The reverse is fallible.
* [`jiff::civil::Time`] infallibly converts to
[`icu::time::Time`](icu_time::Time).
The reverse is fallible.
* [`jiff::civil::Weekday`] infallibly converts to
[`icu::calendar::types::Weekday`](icu_calendar::types::Weekday).
The reverse is also infallible.
* [`jiff::tz::TimeZone`] infallibly converts to
[`icu::time::TimeZone`](icu_time::TimeZone). The reverse is unavailable.

# Format a zoned datetime in another locale

This example shows how one can bridge `jiff` to `icu` in order to
format a zoned datetime in a particular locale. This makes use of the
infallible [`ConvertFrom`] trait to convert a [`jiff::Zoned`] into a
[`icu::time::ZonedDateTime`](icu_time::ZonedDateTime). In order to get `icu` to
emit the time zone information, we need to add a zone marker to our fieldset:

```
use icu::{
    calendar::Iso,
    time::ZonedDateTime,
    datetime::{fieldsets, DateTimeFormatter},
    locale::locale,
};
use jiff::Zoned;
use jiff_icu::{ConvertFrom as _};

let zdt: Zoned = "2024-09-10T23:37:20-04[America/New_York]".parse()?;
let icu_zdt = ZonedDateTime::<Iso, _>::convert_from(&zdt);

// Format for the en-GB locale:
let formatter = DateTimeFormatter::try_new(
    locale!("en-GB").into(),
    fieldsets::YMDET::medium().with_zone(fieldsets::zone::SpecificLong),
)?;
assert_eq!(
    formatter.format(&icu_zdt).to_string(),
    "Tue, 10 Sept 2024, 23:37:20 Eastern Daylight Time",
);

// Or in the en-US locale:
let formatter = DateTimeFormatter::try_new(
    locale!("en-US").into(),
    fieldsets::YMDET::medium().with_zone(fieldsets::zone::SpecificShort),
)?;
assert_eq!(
    formatter.format(&icu_zdt).to_string(),
    "Tue, Sep 10, 2024, 11:37:20 PM EDT",
);

// Or in the "unknown" locale:
let formatter = DateTimeFormatter::try_new(
    icu::locale::Locale::UNKNOWN.into(),
    fieldsets::YMDET::medium().with_zone(fieldsets::zone::SpecificShort),
)?;
assert_eq!(
    formatter.format(&icu_zdt).to_string(),
    "2024 M09 10, Tue 23:37:20 GMT-4",
);

# Ok::<(), Box<dyn std::error::Error>>(())
```

# Format a civil datetime in another locale

This example shows how one can bridge `jiff` to `icu` in order to format a
datetime in a particular locale. This makes use of the infallible
[`ConvertFrom`] trait to convert a [`jiff::civil::DateTime`] into a
[`icu::time::DateTime`](icu_time::DateTime).

```
use icu::{
    time::DateTime,
    datetime::{fieldsets, DateTimeFormatter},
    locale::locale,
};
use jiff::Zoned;
use jiff_icu::{ConvertFrom as _};

let zdt: Zoned = "2024-09-10T23:37:20-04[America/New_York]".parse()?;
let icu_datetime = DateTime::convert_from(zdt.datetime());

// Format for the en-GB locale:
let formatter = DateTimeFormatter::try_new(
    locale!("en-GB").into(),
    fieldsets::YMDET::medium(),
)?;
assert_eq!(
    formatter.format(&icu_datetime).to_string(),
    "Tue, 10 Sept 2024, 23:37:20",
);

// Or in the en-US locale:
let formatter = DateTimeFormatter::try_new(
    locale!("en-US").into(),
    fieldsets::YMDET::medium(),
)?;
assert_eq!(
    formatter.format(&icu_datetime).to_string(),
    "Tue, Sep 10, 2024, 11:37:20 PM",
);

# Ok::<(), Box<dyn std::error::Error>>(())
```

# Convert to another calendar

While Jiff only supports the Gregorian calendar (technically the ISO
8601 calendar), ICU4X supports [many calendars](icu_calendar). This
example shows how to convert a date in the Hebrew calendar to a Jiff
date. This makes use of the fallible [`ConvertTryFrom`] trait to
convert a [`icu::time::DateTime`](icu_time::DateTime) into a
[`jiff::civil::DateTime`]:

```
use icu::{
    calendar::Date as IcuDate,
    time::{DateTime as IcuDateTime, Time as IcuTime},
};
use jiff::civil::DateTime;
use jiff_icu::{ConvertTryFrom as _};

let datetime = IcuDateTime {
    date: IcuDate::try_new_hebrew(5785, 5, 4)?,
    time: IcuTime::try_new(17, 30, 0, 0)?,
};
let zdt = DateTime::convert_try_from(datetime)?.in_tz("America/New_York")?;
assert_eq!(zdt.to_string(), "2025-02-02T17:30:00-05:00[America/New_York]");

# Ok::<(), Box<dyn std::error::Error>>(())
```
*/

#![no_std]
#![deny(missing_docs)]
// This adds Cargo feature annotations to items in the rustdoc output. Which is
// sadly hugely beneficial for this crate due to the number of features.
#![cfg_attr(docsrs_jiff, feature(doc_cfg))]

#[cfg(any(test, feature = "std"))]
extern crate std;

#[cfg(any(test, feature = "alloc"))]
extern crate alloc;

use icu_calendar::{
    types::Weekday as IcuWeekday, AsCalendar as IcuAsCalendar,
    Date as IcuDate, Iso,
};
#[cfg(feature = "time")]
use icu_time::{
    zone::UtcOffset as IcuUtcOffset, DateTime as IcuDateTime, Time as IcuTime,
};
#[cfg(feature = "zoned")]
use icu_time::{
    zone::{models::Full, TimeZoneVariant},
    TimeZone as IcuTimeZone, TimeZoneInfo as IcuTimeZoneInfo,
    ZonedDateTime as IcuZonedDateTime,
};

use jiff::civil::{Date as JiffDate, Weekday as JiffWeekday};
#[cfg(feature = "time")]
use jiff::{
    civil::{DateTime as JiffDateTime, Time as JiffTime},
    tz::Offset as JiffOffset,
};
#[cfg(feature = "zoned")]
use jiff::{tz::TimeZone as JiffTimeZone, Zoned as JiffZoned};

use self::error::err;
pub use self::{
    error::Error,
    traits::{ConvertFrom, ConvertInto, ConvertTryFrom, ConvertTryInto},
};

mod error;
mod traits;

/// Converts from a [`icu_time::DateTime<Iso>`](icu_time::DateTime) to
/// a [`jiff::civil::DateTime`].
///
/// # Examples
///
/// ```
/// use jiff_icu::{ConvertTryFrom as _};
///
/// let icu_datetime = icu_time::DateTime {
///     date: icu_calendar::Date::try_new_iso(1970, 1, 1).unwrap(),
///     time: icu_time::Time::try_new(0, 0, 0, 0).unwrap(),
/// };
/// let jiff_datetime = jiff::civil::DateTime::convert_try_from(icu_datetime)?;
/// assert_eq!(jiff_datetime.to_string(), "1970-01-01T00:00:00");
///
/// let icu_datetime = icu_time::DateTime {
///     date: icu_calendar::Date::try_new_iso(2025, 1, 30).unwrap(),
///     time: icu_time::Time::try_new(17, 58, 30, 0).unwrap(),
/// };
/// let jiff_datetime = jiff::civil::DateTime::convert_try_from(icu_datetime)?;
/// assert_eq!(jiff_datetime.to_string(), "2025-01-30T17:58:30");
///
/// let icu_datetime = icu_time::DateTime {
///     date: icu_calendar::Date::try_new_iso(-9999, 1, 1).unwrap(),
///     time: icu_time::Time::try_new(0, 0, 0, 0).unwrap(),
/// };
/// let jiff_datetime = jiff::civil::DateTime::convert_try_from(icu_datetime)?;
/// assert_eq!(jiff_datetime.to_string(), "-009999-01-01T00:00:00");
///
/// let icu_datetime = icu_time::DateTime {
///     date: icu_calendar::Date::try_new_iso(9999, 12, 31).unwrap(),
///     time: icu_time::Time::try_new(23, 59, 59, 999_999_999).unwrap(),
/// };
/// let jiff_datetime = jiff::civil::DateTime::convert_try_from(icu_datetime)?;
/// assert_eq!(jiff_datetime.to_string(), "9999-12-31T23:59:59.999999999");
///
/// let icu_datetime = icu_time::DateTime {
///     date: icu_calendar::Date::try_new_iso(0, 1, 30).unwrap(),
///     time: icu_time::Time::try_new(0, 0, 0, 0).unwrap(),
/// };
/// let jiff_datetime = jiff::civil::DateTime::convert_try_from(icu_datetime)?;
/// assert_eq!(jiff_datetime.to_string(), "0000-01-30T00:00:00");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[cfg(feature = "time")]
impl<C: IcuAsCalendar> ConvertTryFrom<IcuDateTime<C>> for JiffDateTime {
    type Error = Error;

    fn convert_try_from(v: IcuDateTime<C>) -> Result<JiffDateTime, Error> {
        let date: JiffDate = v.date.convert_try_into()?;
        let time: JiffTime = v.time.convert_try_into()?;
        Ok(JiffDateTime::from_parts(date, time))
    }
}

/// Converts from a [`jiff::civil::DateTime`] to a
/// [`icu_time::DateTime<Iso>`](icu_time::DateTime).
///
/// # Examples
///
/// ```
/// use jiff_icu::{ConvertFrom as _};
///
/// let jiff_datetime = jiff::civil::date(2025, 1, 30).at(17, 58, 30, 0);
/// let icu_datetime = icu_time::DateTime::convert_from(jiff_datetime);
/// assert_eq!(
///     format!("{:?}", icu_datetime.date),
///     "Date(2025-1-30, default era, for calendar ISO)",
/// );
/// assert_eq!(
///     format!("{:?}", icu_datetime.time),
///     "Time { hour: Hour(17), minute: Minute(58), second: Second(30), subsecond: Nanosecond(0) }",
/// );
///
/// let jiff_datetime = jiff::civil::DateTime::MIN;
/// let icu_datetime = icu_time::DateTime::convert_from(jiff_datetime);
/// assert_eq!(
///     format!("{:?}", icu_datetime.date),
///     "Date(-9999-1-1, default era, for calendar ISO)",
/// );
/// assert_eq!(
///     format!("{:?}", icu_datetime.time),
///     "Time { hour: Hour(0), minute: Minute(0), second: Second(0), subsecond: Nanosecond(0) }",
/// );
///
/// let jiff_datetime = jiff::civil::DateTime::MAX;
/// let icu_datetime = icu_time::DateTime::convert_from(jiff_datetime);
/// assert_eq!(
///     format!("{:?}", icu_datetime.date),
///     "Date(9999-12-31, default era, for calendar ISO)",
/// );
/// assert_eq!(
///     format!("{:?}", icu_datetime.time),
///     "Time { hour: Hour(23), minute: Minute(59), second: Second(59), subsecond: Nanosecond(999999999) }",
/// );
///
/// let jiff_datetime = jiff::civil::date(0, 1, 30).at(0, 0, 0, 0);
/// let icu_datetime = icu_time::DateTime::convert_from(jiff_datetime);
/// assert_eq!(
///     format!("{:?}", icu_datetime.date),
///     "Date(0-1-30, default era, for calendar ISO)",
/// );
/// assert_eq!(
///     format!("{:?}", icu_datetime.time),
///     "Time { hour: Hour(0), minute: Minute(0), second: Second(0), subsecond: Nanosecond(0) }",
/// );
/// ```
#[cfg(feature = "time")]
impl ConvertFrom<JiffDateTime> for IcuDateTime<Iso> {
    fn convert_from(v: JiffDateTime) -> IcuDateTime<Iso> {
        let date: IcuDate<Iso> = v.date().convert_into();
        let time: IcuTime = v.time().convert_into();
        IcuDateTime { date, time }
    }
}

/// Converts from a [`icu_calendar::Date`] to a [`jiff::civil::Date`].
///
/// # Examples
///
/// ```
/// use jiff_icu::{ConvertTryFrom as _};
///
/// let icu_date = icu_calendar::Date::try_new_iso(1970, 1, 1).unwrap();
/// let jiff_date = jiff::civil::Date::convert_try_from(icu_date)?;
/// assert_eq!(jiff_date.to_string(), "1970-01-01");
///
/// let icu_date = icu_calendar::Date::try_new_iso(2025, 1, 30).unwrap();
/// let jiff_date = jiff::civil::Date::convert_try_from(icu_date)?;
/// assert_eq!(jiff_date.to_string(), "2025-01-30");
///
/// let icu_date = icu_calendar::Date::try_new_iso(-9999, 1, 1).unwrap();
/// let jiff_date = jiff::civil::Date::convert_try_from(icu_date)?;
/// assert_eq!(jiff_date.to_string(), "-009999-01-01");
///
/// let icu_date = icu_calendar::Date::try_new_iso(9999, 12, 31).unwrap();
/// let jiff_date = jiff::civil::Date::convert_try_from(icu_date)?;
/// assert_eq!(jiff_date.to_string(), "9999-12-31");
///
/// let icu_date = icu_calendar::Date::try_new_iso(0, 1, 30).unwrap();
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
/// let icu_date = icu_calendar::Date::try_new_hebrew(5785, 5, 4).unwrap();
/// let jiff_date = jiff::civil::Date::convert_try_from(icu_date)?;
/// assert_eq!(jiff_date.to_string(), "2025-02-02");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
impl<C: IcuAsCalendar> ConvertTryFrom<IcuDate<C>> for JiffDate {
    type Error = Error;

    fn convert_try_from(v: IcuDate<C>) -> Result<JiffDate, Error> {
        let v = v.to_iso();
        let year = v.extended_year();
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
/// let icu_hebrew_date = icu_iso_date.to_calendar(icu_calendar::cal::Hebrew);
/// assert_eq!(
///     format!("{icu_hebrew_date:?}"),
///     "Date(5785-5-4, am era, for calendar Hebrew)",
/// );
/// ```
impl ConvertFrom<JiffDate> for IcuDate<Iso> {
    fn convert_from(v: JiffDate) -> IcuDate<Iso> {
        let year = i32::from(v.year());
        let month = v.month().unsigned_abs();
        let day = v.day().unsigned_abs();
        // All Jiff civil dates are valid ICU4X dates.
        IcuDate::try_new_iso(year, month, day).unwrap()
    }
}

/// Converts from a [`icu_time::Time`] to a [`jiff::civil::Time`].
///
/// # Examples
///
/// ```
/// use jiff_icu::{ConvertTryFrom as _};
///
/// let icu_time = icu_time::Time::try_new(0, 0, 0, 0).unwrap();
/// let jiff_time = jiff::civil::Time::convert_try_from(icu_time)?;
/// assert_eq!(jiff_time, jiff::civil::time(0, 0, 0, 0));
///
/// let icu_time = icu_time::Time::try_new(23, 59, 59, 999_999_999).unwrap();
/// let jiff_time = jiff::civil::Time::convert_try_from(icu_time)?;
/// assert_eq!(jiff_time, jiff::civil::time(23, 59, 59, 999_999_999));
///
/// let icu_time = icu_time::Time::try_new(17, 59, 4, 0).unwrap();
/// let jiff_time = jiff::civil::Time::convert_try_from(icu_time)?;
/// assert_eq!(jiff_time, jiff::civil::time(17, 59, 4, 0));
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[cfg(feature = "time")]
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
        let subsec_nano = i32::try_from(v.subsecond.number()).unwrap();

        Ok(JiffTime::new(hour, minute, second, subsec_nano)?)
    }
}

/// Converts from a [`jiff::civil::Time`] to a [`icu_time::Time`].
///
/// # Examples
///
/// ```
/// use jiff_icu::{ConvertFrom as _};
///
/// let jiff_time = jiff::civil::time(0, 0, 0, 0);
/// let icu_time = icu_time::Time::convert_from(jiff_time);
/// assert_eq!(
///     format!("{icu_time:?}"),
///     "Time { hour: Hour(0), minute: Minute(0), second: Second(0), subsecond: Nanosecond(0) }",
/// );
///
/// let jiff_time = jiff::civil::time(17, 59, 4, 0);
/// let icu_time = icu_time::Time::convert_from(jiff_time);
/// assert_eq!(
///     format!("{icu_time:?}"),
///     "Time { hour: Hour(17), minute: Minute(59), second: Second(4), subsecond: Nanosecond(0) }",
/// );
/// ```
#[cfg(feature = "time")]
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

/// Converts from a [`icu_calendar::types::Weekday`] to a
/// [`jiff::civil::Weekday`].
///
/// # Examples
///
/// ```
/// use jiff_icu::{ConvertFrom as _};
///
/// let icu_weekday = icu_calendar::types::Weekday::Wednesday;
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
/// [`icu_calendar::types::Weekday`].
///
/// # Examples
///
/// ```
/// use jiff_icu::{ConvertFrom as _};
///
/// let jiff_weekday = jiff::civil::Weekday::Wednesday;
/// let icu_weekday = icu_calendar::types::Weekday::convert_from(jiff_weekday);
/// assert_eq!(icu_weekday, icu_calendar::types::Weekday::Wednesday);
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

/// Converts from a [`jiff::tz::Offset`] to a [`icu_time::zone::UtcOffset`].
///
/// # Examples
///
/// ```
/// use jiff_icu::{ConvertTryFrom as _};
///
/// let jiff_offset = jiff::tz::Offset::from_seconds(
///     5 * 60 * 60 + 30 * 60,
/// ).unwrap();
/// let icu_tz = icu_time::zone::UtcOffset::convert_try_from(jiff_offset)?;
/// assert_eq!(
///     format!("{icu_tz:?}"),
///     "UtcOffset(19800)",
/// );
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[cfg(feature = "time")]
impl ConvertTryFrom<JiffOffset> for IcuUtcOffset {
    type Error = Error;

    fn convert_try_from(v: JiffOffset) -> Result<IcuUtcOffset, Error> {
        // I considered just rounding to the nearest eighth of a second,
        // but Jiff's `Offset` supports a larger range than ICU4X's
        // `UtcOffset`. In practice, this generally shouldn't matter, since
        // all extant offsets will fit in ICU4X's `UtcOffset` anyway. But it's
        // kinda hard to get a reasonable value in the case of failure.
        IcuUtcOffset::try_from_seconds(v.seconds()).map_err(|err| {
            err!(
                "failed to convert Jiff UTC offset of \
                 `{v}` to ICU4X offset: {err}",
            )
        })
    }
}

/// Converts from a [`jiff::tz::TimeZone`] to a [`icu_time::TimeZone`].
///
/// # Examples
///
/// ```
/// use jiff_icu::{ConvertFrom as _};
///
/// let jiff_tz = jiff::tz::TimeZone::get("America/New_York")?;
/// let icu_tz = icu_time::TimeZone::convert_from(jiff_tz);
/// assert_eq!(
///     format!("{icu_tz:?}"),
///     "TimeZone(Subtag(\"usnyc\"))",
/// );
///
/// let jiff_tz = jiff::tz::TimeZone::get("us/eastern")?;
/// let icu_tz = icu_time::TimeZone::convert_from(jiff_tz);
/// assert_eq!(
///     format!("{icu_tz:?}"),
///     "TimeZone(Subtag(\"usnyc\"))",
/// );
///
/// // If there's no IANA identifier for the Jiff time zone, then
/// // this automatically results in an "unknown" ICU4X time zone:
/// let jiff_tz = jiff::tz::TimeZone::fixed(jiff::tz::offset(-5));
/// let icu_tz = icu_time::TimeZone::convert_from(jiff_tz);
/// assert_eq!(
///     format!("{icu_tz:?}"),
///     "TimeZone(Subtag(\"unk\"))",
/// );
///
/// // An explicitly unknown Jiff time zone is equivalent to an
/// // unknown ICU4X time zone:
/// let jiff_tz = jiff::tz::TimeZone::unknown();
/// let icu_tz = icu_time::TimeZone::convert_from(jiff_tz);
/// assert_eq!(
///     format!("{icu_tz:?}"),
///     "TimeZone(Subtag(\"unk\"))",
/// );
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[cfg(feature = "zoned")]
impl ConvertFrom<JiffTimeZone> for IcuTimeZone {
    fn convert_from(v: JiffTimeZone) -> IcuTimeZone {
        IcuTimeZone::convert_from(&v)
    }
}

/// Converts from a [`&jiff::tz::TimeZone`](jiff::tz::TimeZone) to a
/// [`icu_time::TimeZone`].
#[cfg(feature = "zoned")]
impl<'a> ConvertFrom<&'a JiffTimeZone> for IcuTimeZone {
    fn convert_from(v: &'a JiffTimeZone) -> IcuTimeZone {
        let Some(iana_name) = v.iana_name() else {
            return IcuTimeZone::UNKNOWN;
        };
        icu_time::zone::iana::IanaParser::new().parse(iana_name)
    }
}

/// Converts from a [`jiff::Zoned`] to a
/// [`icu_time::ZonedDateTime<Iso, TimeZoneInfo<Full>>`](icu_time::ZonedDateTime).
///
/// # Examples
///
/// ```
/// use jiff_icu::{ConvertFrom as _};
///
/// let jiff_zdt = jiff::civil::date(2025, 1, 30)
///     .at(17, 58, 30, 0)
///     .in_tz("America/New_York")?;
/// let icu_zdt = icu_time::ZonedDateTime::convert_from(&jiff_zdt);
/// assert_eq!(
///     format!("{:?}", icu_zdt.date),
///     "Date(2025-1-30, default era, for calendar ISO)",
/// );
/// assert_eq!(
///     format!("{:?}", icu_zdt.time),
///     "Time { hour: Hour(17), minute: Minute(58), second: Second(30), subsecond: Nanosecond(0) }",
/// );
/// assert_eq!(
///     format!("{:?}", (icu_zdt.zone.id(), icu_zdt.zone.offset())),
///     "(TimeZone(Subtag(\"usnyc\")), Some(UtcOffset(-18000)))",
/// );
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[cfg(feature = "zoned")]
impl<'a> ConvertFrom<&'a JiffZoned>
    for IcuZonedDateTime<Iso, IcuTimeZoneInfo<Full>>
{
    fn convert_from(
        v: &'a JiffZoned,
    ) -> IcuZonedDateTime<Iso, IcuTimeZoneInfo<Full>> {
        let date = IcuDate::convert_from(v.date());
        let time = IcuTime::convert_from(v.time());
        let datetime = IcuDateTime { date, time };

        let tz = IcuTimeZone::convert_from(v.time_zone());
        let offset = IcuUtcOffset::convert_try_from(v.offset()).ok();
        let dst = v.time_zone().to_offset_info(v.timestamp()).dst().is_dst();
        let tz_info_base = tz.with_offset(offset);
        let tz_info_at = tz_info_base.at_date_time_iso(datetime);
        let zone = tz_info_at.with_variant(if dst {
            TimeZoneVariant::Daylight
        } else {
            TimeZoneVariant::Standard
        });
        IcuZonedDateTime { date, time, zone }
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
    #[cfg(feature = "time")]
    #[test]
    fn all_jiff_times_are_valid_icu_times() {
        for jiff_time in jiff::civil::Time::MIN.series(1.second()) {
            let icu_time: IcuTime = jiff_time.convert_try_into().unwrap();
            let got: jiff::civil::Time = icu_time.convert_try_into().unwrap();
            assert_eq!(jiff_time, got);
        }
    }
}
