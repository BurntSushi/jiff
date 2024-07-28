use crate::{
    civil::{Date, DateTime, Time},
    error::Error,
    fmt::{util::DecimalFormatter, Write, WriteExt},
    span::Span,
    tz::{Offset, TimeZone},
    util::{rangeint::RFrom, t},
    Timestamp, Zoned,
};

#[derive(Clone, Debug)]
pub(super) struct DateTimePrinter {
    lowercase: bool,
    separator: u8,
    rfc9557: bool,
}

impl DateTimePrinter {
    pub(super) const fn new() -> DateTimePrinter {
        DateTimePrinter { lowercase: false, separator: b'T', rfc9557: true }
    }

    pub(super) const fn lowercase(self, yes: bool) -> DateTimePrinter {
        DateTimePrinter { lowercase: yes, ..self }
    }

    pub(super) const fn separator(self, ascii_char: u8) -> DateTimePrinter {
        assert!(ascii_char.is_ascii(), "RFC3339 separator must be ASCII");
        DateTimePrinter { separator: ascii_char, ..self }
    }

    pub(super) fn print_zoned<W: Write>(
        &self,
        zdt: &Zoned,
        mut wtr: W,
    ) -> Result<(), Error> {
        let timestamp = zdt.timestamp();
        let tz = zdt.time_zone();
        let (offset, _, _) = tz.to_offset(timestamp);
        let dt = offset.to_datetime(timestamp);
        self.print_datetime(&dt, &mut wtr)?;
        self.print_offset(&offset, &mut wtr)?;
        self.print_time_zone(&tz, &offset, &mut wtr)?;
        Ok(())
    }

    pub(super) fn print_timestamp<W: Write>(
        &self,
        timestamp: &Timestamp,
        mut wtr: W,
    ) -> Result<(), Error> {
        let dt = TimeZone::UTC.to_datetime(*timestamp);
        self.print_datetime(&dt, &mut wtr)?;
        self.print_zulu(&mut wtr)?;
        Ok(())
    }

    /// Formats the given datetime into the writer given.
    pub(super) fn print_datetime<W: Write>(
        &self,
        dt: &DateTime,
        mut wtr: W,
    ) -> Result<(), Error> {
        self.print_date(&dt.date(), &mut wtr)?;
        wtr.write_char(char::from(if self.lowercase {
            self.separator.to_ascii_lowercase()
        } else {
            self.separator
        }))?;
        self.print_time(&dt.time(), &mut wtr)?;
        Ok(())
    }

    /// Formats the given date into the writer given.
    pub(super) fn print_date<W: Write>(
        &self,
        date: &Date,
        mut wtr: W,
    ) -> Result<(), Error> {
        static FMT_YEAR_POSITIVE: DecimalFormatter =
            DecimalFormatter::new().padding(4);
        static FMT_YEAR_NEGATIVE: DecimalFormatter =
            DecimalFormatter::new().padding(6);
        static FMT_TWO: DecimalFormatter = DecimalFormatter::new().padding(2);

        if date.year() >= 0 {
            wtr.write_int(&FMT_YEAR_POSITIVE, date.year())?;
        } else {
            wtr.write_int(&FMT_YEAR_NEGATIVE, date.year())?;
        }
        wtr.write_str("-")?;
        wtr.write_int(&FMT_TWO, date.month())?;
        wtr.write_str("-")?;
        wtr.write_int(&FMT_TWO, date.day())?;
        Ok(())
    }

    /// Formats the given time into the writer given.
    pub(super) fn print_time<W: Write>(
        &self,
        time: &Time,
        mut wtr: W,
    ) -> Result<(), Error> {
        static FMT_TWO: DecimalFormatter = DecimalFormatter::new().padding(2);
        static FMT_FRACTION: DecimalFormatter =
            DecimalFormatter::new().fractional(0, 9);

        wtr.write_int(&FMT_TWO, time.hour())?;
        wtr.write_str(":")?;
        wtr.write_int(&FMT_TWO, time.minute())?;
        wtr.write_str(":")?;
        wtr.write_int(&FMT_TWO, time.second())?;
        let fractional_nanosecond = time.subsec_nanosecond();
        if fractional_nanosecond != 0 {
            wtr.write_str(".")?;
            wtr.write_int(&FMT_FRACTION, fractional_nanosecond)?;
        }
        Ok(())
    }

    /// Formats the given offset into the writer given.
    fn print_offset<W: Write>(
        &self,
        offset: &Offset,
        mut wtr: W,
    ) -> Result<(), Error> {
        static FMT_TWO: DecimalFormatter = DecimalFormatter::new().padding(2);

        wtr.write_str(if offset.is_negative() { "-" } else { "+" })?;
        let mut hours = offset.part_hours_ranged().abs().get();
        let mut minutes = offset.part_minutes_ranged().abs().get();
        // RFC 3339 requires that time zone offsets are an integral number
        // of minutes. While rounding based on seconds doesn't seem clearly
        // indicated, the `1937-01-01T12:00:27.87+00:20` example seems
        // to suggest that the number of minutes should be "as close as
        // possible" to the actual offset. So we just do basic rounding
        // here.
        if offset.part_seconds_ranged().abs() >= 30 {
            if minutes == 59 {
                hours = hours.saturating_add(1);
                minutes = 0;
            } else {
                minutes = minutes.saturating_add(1);
            }
        }
        wtr.write_int(&FMT_TWO, hours)?;
        wtr.write_str(":")?;
        wtr.write_int(&FMT_TWO, minutes)?;
        Ok(())
    }

    /// Prints the "zulu" indicator.
    ///
    /// This should only be used when the offset is not known. For example,
    /// when printing a `Timestamp`.
    fn print_zulu<W: Write>(&self, mut wtr: W) -> Result<(), Error> {
        wtr.write_str(if self.lowercase { "z" } else { "Z" })
    }

    /// Formats the given time zone name into the writer given.
    ///
    /// This is a no-op when RFC 9557 support isn't enabled. And when the given
    /// time zone is not an IANA time zone name, then the offset is printed
    /// instead. (This means the offset will be printed twice, which is indeed
    /// an intended behavior of RFC 9557 for cases where a time zone name is
    /// not used or unavailable.)
    fn print_time_zone<W: Write>(
        &self,
        time_zone: &TimeZone,
        offset: &Offset,
        mut wtr: W,
    ) -> Result<(), Error> {
        if !self.rfc9557 {
            return Ok(());
        }
        wtr.write_str("[")?;
        if let Some(iana_name) = time_zone.iana_name() {
            wtr.write_str(iana_name)?;
        } else {
            self.print_offset(offset, &mut wtr)?;
        }
        wtr.write_str("]")?;
        Ok(())
    }
}

impl Default for DateTimePrinter {
    fn default() -> DateTimePrinter {
        DateTimePrinter::new()
    }
}

/// A printer for Temporal spans.
///
/// Note that in Temporal, a "span" is called a "duration."
#[derive(Debug)]
pub(super) struct SpanPrinter {
    /// There are currently no configuration options for this printer.
    _priv: (),
}

impl SpanPrinter {
    /// Create a new Temporal span printer with the default configuration.
    pub(super) const fn new() -> SpanPrinter {
        SpanPrinter { _priv: () }
    }

    /// Print the given span to the writer given.
    ///
    /// This only returns an error when the given writer returns an error.
    pub(super) fn print_span<W: Write>(
        &self,
        span: &Span,
        mut wtr: W,
    ) -> Result<(), Error> {
        static FMT_INT: DecimalFormatter = DecimalFormatter::new();
        static FMT_FRACTION: DecimalFormatter =
            DecimalFormatter::new().fractional(0, 9);

        if span.is_negative() {
            wtr.write_str("-")?;
        }
        wtr.write_str("P")?;

        let mut non_zero_greater_than_second = false;
        if span.get_years_ranged() != 0 {
            wtr.write_int(&FMT_INT, span.get_years_ranged().get().abs())?;
            wtr.write_str("y")?;
            non_zero_greater_than_second = true;
        }
        if span.get_months_ranged() != 0 {
            wtr.write_int(&FMT_INT, span.get_months_ranged().get().abs())?;
            wtr.write_str("m")?;
            non_zero_greater_than_second = true;
        }
        if span.get_weeks_ranged() != 0 {
            wtr.write_int(&FMT_INT, span.get_weeks_ranged().get().abs())?;
            wtr.write_str("w")?;
            non_zero_greater_than_second = true;
        }
        if span.get_days_ranged() != 0 {
            wtr.write_int(&FMT_INT, span.get_days_ranged().get().abs())?;
            wtr.write_str("d")?;
            non_zero_greater_than_second = true;
        }

        let mut printed_time_prefix = false;
        if span.get_hours_ranged() != 0 {
            if !printed_time_prefix {
                wtr.write_str("T")?;
                printed_time_prefix = true;
            }
            wtr.write_int(&FMT_INT, span.get_hours_ranged().get().abs())?;
            wtr.write_str("h")?;
            non_zero_greater_than_second = true;
        }
        if span.get_minutes_ranged() != 0 {
            if !printed_time_prefix {
                wtr.write_str("T")?;
                printed_time_prefix = true;
            }
            wtr.write_int(&FMT_INT, span.get_minutes_ranged().get().abs())?;
            wtr.write_str("m")?;
            non_zero_greater_than_second = true;
        }

        // ISO 8601 (and Temporal) don't support writing out milliseconds,
        // microseconds or nanoseconds as separate components like for all
        // the other units. Instead, they must be incorporated as fractional
        // seconds. But we only want to do that work if we need to.
        let (seconds, millis, micros, nanos) = (
            span.get_seconds_ranged().abs(),
            span.get_milliseconds_ranged().abs(),
            span.get_microseconds_ranged().abs(),
            span.get_nanoseconds_ranged().abs(),
        );
        if (seconds != 0 || !non_zero_greater_than_second)
            && millis == 0
            && micros == 0
            && nanos == 0
        {
            if !printed_time_prefix {
                wtr.write_str("T")?;
            }
            wtr.write_int(&FMT_INT, seconds.get())?;
            wtr.write_str("s")?;
        } else if millis != 0 || micros != 0 || nanos != 0 {
            if !printed_time_prefix {
                wtr.write_str("T")?;
            }
            // We want to combine our seconds, milliseconds, microseconds and
            // nanoseconds into one single value in terms of nanoseconds. Then
            // we can "balance" that out so that we have a number of seconds
            // and a number of nanoseconds not greater than 1 second. (Which is
            // our fraction.)
            let combined_as_nanos =
                t::SpanSecondsOrLowerNanoseconds::rfrom(nanos)
                    + (t::SpanSecondsOrLowerNanoseconds::rfrom(micros)
                        * t::NANOS_PER_MICRO)
                    + (t::SpanSecondsOrLowerNanoseconds::rfrom(millis)
                        * t::NANOS_PER_MILLI)
                    + (t::SpanSecondsOrLowerNanoseconds::rfrom(seconds)
                        * t::NANOS_PER_SECOND);
            let fraction_second = t::SpanSecondsOrLower::rfrom(
                combined_as_nanos / t::NANOS_PER_SECOND,
            );
            let fraction_nano = t::SubsecNanosecond::rfrom(
                combined_as_nanos % t::NANOS_PER_SECOND,
            );
            wtr.write_int(&FMT_INT, fraction_second.get())?;
            if fraction_nano != 0 {
                wtr.write_str(".")?;
                wtr.write_int(&FMT_FRACTION, fraction_nano.get())?;
            }
            wtr.write_str("s")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use alloc::string::String;

    use crate::{civil::date, span::ToSpan};

    use super::*;

    #[test]
    fn print_zoned() {
        if crate::tz::db().is_definitively_empty() {
            return;
        }

        let dt = date(2024, 3, 10).at(5, 34, 45, 0);
        let zoned: Zoned = dt.intz("America/New_York").unwrap();
        let mut buf = String::new();
        DateTimePrinter::new().print_zoned(&zoned, &mut buf).unwrap();
        assert_eq!(buf, "2024-03-10T05:34:45-04:00[America/New_York]");

        let dt = date(2024, 3, 10).at(5, 34, 45, 0);
        let zoned: Zoned = dt.intz("America/New_York").unwrap();
        let zoned = zoned.with_time_zone(TimeZone::UTC);
        let mut buf = String::new();
        DateTimePrinter::new().print_zoned(&zoned, &mut buf).unwrap();
        assert_eq!(buf, "2024-03-10T09:34:45+00:00[UTC]");
    }

    #[test]
    fn print_timestamp() {
        if crate::tz::db().is_definitively_empty() {
            return;
        }

        let dt = date(2024, 3, 10).at(5, 34, 45, 0);
        let zoned: Zoned = dt.intz("America/New_York").unwrap();
        let mut buf = String::new();
        DateTimePrinter::new()
            .print_timestamp(&zoned.timestamp(), &mut buf)
            .unwrap();
        assert_eq!(buf, "2024-03-10T09:34:45Z");

        let dt = date(-2024, 3, 10).at(5, 34, 45, 0);
        let zoned: Zoned = dt.intz("America/New_York").unwrap();
        let mut buf = String::new();
        DateTimePrinter::new()
            .print_timestamp(&zoned.timestamp(), &mut buf)
            .unwrap();
        assert_eq!(buf, "-002024-03-10T10:30:47Z");
    }

    #[test]
    fn print_span_basic() {
        let p = |span: Span| -> String {
            let mut buf = String::new();
            SpanPrinter::new().print_span(&span, &mut buf).unwrap();
            buf
        };

        insta::assert_snapshot!(p(Span::new()), @"PT0s");
        insta::assert_snapshot!(p(1.second()), @"PT1s");
        insta::assert_snapshot!(p(-1.second()), @"-PT1s");
        insta::assert_snapshot!(p(
            1.second().milliseconds(1).microseconds(1).nanoseconds(1),
        ), @"PT1.001001001s");
        insta::assert_snapshot!(p(
            0.second().milliseconds(999).microseconds(999).nanoseconds(999),
        ), @"PT0.999999999s");
        insta::assert_snapshot!(p(
            1.year().months(1).weeks(1).days(1)
            .hours(1).minutes(1).seconds(1)
            .milliseconds(1).microseconds(1).nanoseconds(1),
        ), @"P1y1m1w1dT1h1m1.001001001s");
        insta::assert_snapshot!(p(
            -1.year().months(1).weeks(1).days(1)
            .hours(1).minutes(1).seconds(1)
            .milliseconds(1).microseconds(1).nanoseconds(1),
        ), @"-P1y1m1w1dT1h1m1.001001001s");
    }

    #[test]
    fn print_span_subsecond_positive() {
        let p = |span: Span| -> String {
            let mut buf = String::new();
            SpanPrinter::new().print_span(&span, &mut buf).unwrap();
            buf
        };

        // These are all sub-second trickery tests.
        insta::assert_snapshot!(p(
            0.second().milliseconds(1000).microseconds(1000).nanoseconds(1000),
        ), @"PT1.001001s");
        insta::assert_snapshot!(p(
            1.second().milliseconds(1000).microseconds(1000).nanoseconds(1000),
        ), @"PT2.001001s");
        insta::assert_snapshot!(p(
            0.second()
            .milliseconds(t::SpanMilliseconds::MAX_REPR),
        ), @"PT631107417600s");
        insta::assert_snapshot!(p(
            0.second()
            .microseconds(t::SpanMicroseconds::MAX_REPR),
        ), @"PT631107417600s");
        insta::assert_snapshot!(p(
            0.second()
            .nanoseconds(t::SpanNanoseconds::MAX_REPR),
        ), @"PT9223372036.854775807s");

        insta::assert_snapshot!(p(
            0.second()
            .milliseconds(t::SpanMilliseconds::MAX_REPR)
            .microseconds(999_999),
        ), @"PT631107417600.999999s");
        // This is 1 microsecond more than the maximum number of seconds
        // representable in a span.
        insta::assert_snapshot!(p(
            0.second()
            .milliseconds(t::SpanMilliseconds::MAX_REPR)
            .microseconds(1_000_000),
        ), @"PT631107417601s");
        insta::assert_snapshot!(p(
            0.second()
            .milliseconds(t::SpanMilliseconds::MAX_REPR)
            .microseconds(1_000_001),
        ), @"PT631107417601.000001s");
        // This is 1 nanosecond more than the maximum number of seconds
        // representable in a span.
        insta::assert_snapshot!(p(
            0.second()
            .milliseconds(t::SpanMilliseconds::MAX_REPR)
            .nanoseconds(1_000_000_000),
        ), @"PT631107417601s");
        insta::assert_snapshot!(p(
            0.second()
            .milliseconds(t::SpanMilliseconds::MAX_REPR)
            .nanoseconds(1_000_000_001),
        ), @"PT631107417601.000000001s");

        // The max millis, micros and nanos, combined.
        insta::assert_snapshot!(p(
            0.second()
            .milliseconds(t::SpanMilliseconds::MAX_REPR)
            .microseconds(t::SpanMicroseconds::MAX_REPR)
            .nanoseconds(t::SpanNanoseconds::MAX_REPR),
        ), @"PT1271438207236.854775807s");
        // The max seconds, millis, micros and nanos, combined.
        insta::assert_snapshot!(p(
            Span::new()
            .seconds(t::SpanSeconds::MAX_REPR)
            .milliseconds(t::SpanMilliseconds::MAX_REPR)
            .microseconds(t::SpanMicroseconds::MAX_REPR)
            .nanoseconds(t::SpanNanoseconds::MAX_REPR),
        ), @"PT1902545624836.854775807s");
    }

    #[test]
    fn print_span_subsecond_negative() {
        let p = |span: Span| -> String {
            let mut buf = String::new();
            SpanPrinter::new().print_span(&span, &mut buf).unwrap();
            buf
        };

        // These are all sub-second trickery tests.
        insta::assert_snapshot!(p(
            -0.second().milliseconds(1000).microseconds(1000).nanoseconds(1000),
        ), @"-PT1.001001s");
        insta::assert_snapshot!(p(
            -1.second().milliseconds(1000).microseconds(1000).nanoseconds(1000),
        ), @"-PT2.001001s");
        insta::assert_snapshot!(p(
            0.second()
            .milliseconds(t::SpanMilliseconds::MIN_REPR),
        ), @"-PT631107417600s");
        insta::assert_snapshot!(p(
            0.second()
            .microseconds(t::SpanMicroseconds::MIN_REPR),
        ), @"-PT631107417600s");
        insta::assert_snapshot!(p(
            0.second()
            .nanoseconds(t::SpanNanoseconds::MIN_REPR),
        ), @"-PT9223372036.854775807s");

        insta::assert_snapshot!(p(
            0.second()
            .milliseconds(t::SpanMilliseconds::MIN_REPR)
            .microseconds(999_999),
        ), @"-PT631107417600.999999s");
        // This is 1 microsecond more than the maximum number of seconds
        // representable in a span.
        insta::assert_snapshot!(p(
            0.second()
            .milliseconds(t::SpanMilliseconds::MIN_REPR)
            .microseconds(1_000_000),
        ), @"-PT631107417601s");
        insta::assert_snapshot!(p(
            0.second()
            .milliseconds(t::SpanMilliseconds::MIN_REPR)
            .microseconds(1_000_001),
        ), @"-PT631107417601.000001s");
        // This is 1 nanosecond more than the maximum number of seconds
        // representable in a span.
        insta::assert_snapshot!(p(
            0.second()
            .milliseconds(t::SpanMilliseconds::MIN_REPR)
            .nanoseconds(1_000_000_000),
        ), @"-PT631107417601s");
        insta::assert_snapshot!(p(
            0.second()
            .milliseconds(t::SpanMilliseconds::MIN_REPR)
            .nanoseconds(1_000_000_001),
        ), @"-PT631107417601.000000001s");

        // The max millis, micros and nanos, combined.
        insta::assert_snapshot!(p(
            0.second()
            .milliseconds(t::SpanMilliseconds::MIN_REPR)
            .microseconds(t::SpanMicroseconds::MIN_REPR)
            .nanoseconds(t::SpanNanoseconds::MIN_REPR),
        ), @"-PT1271438207236.854775807s");
        // The max seconds, millis, micros and nanos, combined.
        insta::assert_snapshot!(p(
            Span::new()
            .seconds(t::SpanSeconds::MIN_REPR)
            .milliseconds(t::SpanMilliseconds::MIN_REPR)
            .microseconds(t::SpanMicroseconds::MIN_REPR)
            .nanoseconds(t::SpanNanoseconds::MIN_REPR),
        ), @"-PT1902545624836.854775807s");
    }
}
