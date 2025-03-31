/*!
Traits for converting from `jiff` types to `chrono` and `time` types.

These traits are mostly based on the design (at time of writing, 2025-02-15)
of `jiff-icu`. But we don't really add any polish. And don't currently provide
a way to convert from `chrono` or `time` types back to `jiff`. We also don't
bother with fallible conversions. Since this is only an internal API for use
in benchmarks, we just panic if the conversion fails.

I wrote this module because I was tired of looking up the `chrono` and `time`
APIs for constructing datetimes. `time`'s is mostly sensible, but `chrono`'s
is just an inconsistent mess. This way, I can just make the Jiff types and then
convert them.

Note that these conversions are never included in the benchmark measurement
itself. Just in the setup. If they are being measured and the benchmark isn't
specifically intended to measure conversions (none such benchmarks exist at
time of writing, 2025-02-15), then that's a bug in the benchmark.
*/

/// Adds infallible conversions between crates that mirrors [`From`].
pub(crate) trait ConvertFrom<F>: Sized {
    /// Infallibly converts a value of type `F` to a value of type `Self`.
    fn convert_from(value: F) -> Self;
}

/// Adds infallible conversions between crates that mirrors [`Into`].
pub(crate) trait ConvertInto<T>: Sized {
    /// Infallibly converts a value of type `Self` to a value of type `T`.
    fn convert_into(self) -> T;
}

impl<F, T: ConvertFrom<F>> ConvertInto<T> for F {
    fn convert_into(self) -> T {
        T::convert_from(self)
    }
}

impl ConvertFrom<jiff::Zoned> for chrono::DateTime<chrono::FixedOffset> {
    fn convert_from(x: jiff::Zoned) -> chrono::DateTime<chrono::FixedOffset> {
        // We specifically avoid `x.offset()` here, since we only want this
        // conversion to succeed when our time zone is itself a fixed offset.
        let offset = chrono::FixedOffset::convert_from(
            x.time_zone().to_fixed_offset().unwrap(),
        );
        chrono::DateTime::convert_from(x.timestamp()).with_timezone(&offset)
    }
}

impl ConvertFrom<jiff::Timestamp> for chrono::DateTime<chrono::Utc> {
    fn convert_from(x: jiff::Timestamp) -> chrono::DateTime<chrono::Utc> {
        chrono::DateTime::from_timestamp(
            x.as_second(),
            x.subsec_nanosecond().unsigned_abs(),
        )
        .unwrap()
    }
}

impl ConvertFrom<jiff::tz::Offset> for chrono::FixedOffset {
    fn convert_from(x: jiff::tz::Offset) -> chrono::FixedOffset {
        chrono::FixedOffset::east_opt(x.seconds()).unwrap()
    }
}

impl ConvertFrom<jiff::civil::DateTime> for chrono::NaiveDateTime {
    fn convert_from(x: jiff::civil::DateTime) -> chrono::NaiveDateTime {
        chrono::NaiveDateTime::new(
            x.date().convert_into(),
            x.time().convert_into(),
        )
    }
}

impl ConvertFrom<jiff::civil::Date> for chrono::NaiveDate {
    fn convert_from(x: jiff::civil::Date) -> chrono::NaiveDate {
        chrono::NaiveDate::from_ymd_opt(
            x.year().into(),
            x.month().unsigned_abs().into(),
            x.day().unsigned_abs().into(),
        )
        .unwrap()
    }
}

impl ConvertFrom<jiff::civil::Time> for chrono::NaiveTime {
    fn convert_from(x: jiff::civil::Time) -> chrono::NaiveTime {
        chrono::NaiveTime::from_hms_nano_opt(
            x.hour().unsigned_abs().into(),
            x.minute().unsigned_abs().into(),
            x.second().unsigned_abs().into(),
            x.subsec_nanosecond().unsigned_abs().into(),
        )
        .unwrap()
    }
}

impl ConvertFrom<jiff::Zoned> for time::OffsetDateTime {
    fn convert_from(x: jiff::Zoned) -> time::OffsetDateTime {
        // We specifically avoid `x.offset()` here, since we only want this
        // conversion to succeed when our time zone is itself a fixed offset.
        let offset = x.time_zone().to_fixed_offset().unwrap();
        time::OffsetDateTime::convert_from(x.timestamp())
            .to_offset(offset.convert_into())
    }
}

impl ConvertFrom<jiff::Timestamp> for time::OffsetDateTime {
    fn convert_from(x: jiff::Timestamp) -> time::OffsetDateTime {
        time::OffsetDateTime::from_unix_timestamp_nanos(x.as_nanosecond())
            .unwrap()
    }
}

impl ConvertFrom<jiff::Timestamp> for time::UtcDateTime {
    fn convert_from(x: jiff::Timestamp) -> time::UtcDateTime {
        time::UtcDateTime::from_unix_timestamp_nanos(x.as_nanosecond())
            .unwrap()
    }
}

impl ConvertFrom<jiff::tz::Offset> for time::UtcOffset {
    fn convert_from(x: jiff::tz::Offset) -> time::UtcOffset {
        time::UtcOffset::from_whole_seconds(x.seconds()).unwrap()
    }
}

impl ConvertFrom<jiff::civil::DateTime> for time::PrimitiveDateTime {
    fn convert_from(x: jiff::civil::DateTime) -> time::PrimitiveDateTime {
        time::PrimitiveDateTime::new(
            x.date().convert_into(),
            x.time().convert_into(),
        )
    }
}

impl ConvertFrom<jiff::civil::Date> for time::Date {
    fn convert_from(x: jiff::civil::Date) -> time::Date {
        time::Date::from_calendar_date(
            x.year().into(),
            x.month().unsigned_abs().try_into().unwrap(),
            x.day().unsigned_abs(),
        )
        .unwrap()
    }
}

impl ConvertFrom<jiff::civil::Time> for time::Time {
    fn convert_from(x: jiff::civil::Time) -> time::Time {
        time::Time::from_hms_nano(
            x.hour().unsigned_abs().into(),
            x.minute().unsigned_abs().into(),
            x.second().unsigned_abs().into(),
            x.subsec_nanosecond().unsigned_abs().into(),
        )
        .unwrap()
    }
}
