use std::hint::black_box as bb;

use criterion::Criterion;
use jiff::{
    civil,
    tz::{Offset, TimeZone},
    Timestamp,
};

use crate::{benchmark, convert::ConvertFrom};

pub(super) fn define(c: &mut Criterion) {
    print_civil_datetime(c);
    print_display(c);
    print_friendly(c);
    print_iso8601_duration(c);
    print_rfc2822(c);
    print_rfc3339(c);
    print_rfc9557(c);
    print_strftime(c);
}

/// Measures the time it takes to print a civil datetime in ISO 8601 format.
///
/// This attempts to use the fastest possible API for the corresponding crate.
fn print_civil_datetime(c: &mut Criterion) {
    const NAME: &str = "print/civil_datetime";
    const EXPECTED: &str = "2024-06-30T09:46:00";
    const DATETIME: civil::DateTime = civil::date(2024, 6, 30).at(9, 46, 0, 0);

    {
        let dt = DATETIME;
        let mut buf = String::new();
        benchmark(c, format!("{NAME}/jiff"), |b| {
            b.iter(|| {
                static PRINTER: jiff::fmt::temporal::DateTimePrinter =
                    jiff::fmt::temporal::DateTimePrinter::new();
                buf.clear();
                PRINTER.print_datetime(bb(&dt), &mut buf).unwrap();
                assert_eq!(buf, EXPECTED);
            })
        });
    }

    // This is a sanity check to make sure we aren't doing anything dumb.
    // At time of writing (2025-02-14), both `jiff` and `time` are faster
    // than this. But `chrono` is a fair bit slower... Hmmmmmm.
    {
        let dt = DATETIME;
        let mut buf = String::new();
        benchmark(c, format!("{NAME}/stdfmt"), |b| {
            b.iter(|| {
                use std::fmt::Write;

                buf.clear();
                write!(
                    buf,
                    "{:04}-{:02}-{:02}T{:02}:{:02}:{:02}",
                    dt.year(),
                    dt.month(),
                    dt.day(),
                    dt.hour(),
                    dt.minute(),
                    dt.second(),
                )
                .unwrap();
                assert_eq!(buf, EXPECTED);
            })
        });
    }

    {
        let dt = chrono::NaiveDateTime::convert_from(DATETIME);
        let format =
            chrono::format::strftime::StrftimeItems::new("%Y-%m-%dT%H:%M:%S");
        benchmark(c, format!("{NAME}/chrono"), |b| {
            b.iter(|| {
                // I looked around in `chrono::format` for a potentially
                // faster API (i.e., one that permits amortizing allocs, like
                // Jiff does), but I couldn't find one.
                let got = dt.format_with_items(format.clone()).to_string();
                assert_eq!(got, EXPECTED);
            })
        });
    }

    {
        let dt = time::PrimitiveDateTime::convert_from(DATETIME);
        let format = time::format_description::well_known::Iso8601::DATE_TIME;
        let mut buf = vec![];
        benchmark(c, format!("{NAME}/time"), |b| {
            b.iter(|| {
                buf.clear();
                let _ = dt.format_into(&mut buf, &format).unwrap();
                // wat, why is it writing out 9 digits of precision here?
                // I get making that opt-in, but this IMO should not be the
                // default paved path for ISO 8601 formatting.
                assert_eq!(buf, b"2024-06-30T09:46:00.000000000");
            })
        });
    }
}

/// Measures the time it takes to do `value.to_string()` on all of Jiff's
/// primary data types.
///
/// We don't bother with other crate benchmarks here. We have enough coverage
/// for those in other micro-benchmarks. We also don't bother trying to get
/// cute and reuse buffers. While perhaps useful to measure, I expect that
/// just a simple `zdt.to_string()` (for example) is likely to be quite common
/// on its own. So let's just focus on that.
fn print_display(c: &mut Criterion) {
    const NAME: &str = "print/display";

    {
        const EXPECTED: &str = "2025-12-27T17:46:02-05:00[America/New_York]";
        let zdt = civil::date(2025, 12, 27)
            .at(17, 46, 2, 0)
            .in_tz("America/New_York")
            .unwrap();
        benchmark(c, format!("{NAME}/zoned/jiff"), |b| {
            b.iter(|| {
                assert_eq!(bb(&zdt).to_string(), EXPECTED);
            })
        });
    }

    {
        const EXPECTED: &str = "2025-12-27T22:46:02Z";
        let ts = civil::date(2025, 12, 27)
            .at(17, 46, 2, 0)
            .in_tz("America/New_York")
            .unwrap()
            .timestamp();
        benchmark(c, format!("{NAME}/timestamp/jiff"), |b| {
            b.iter(|| {
                assert_eq!(bb(&ts).to_string(), EXPECTED);
            })
        });
    }

    {
        const EXPECTED: &str = "2025-12-27T17:46:02";
        let dt = civil::date(2025, 12, 27).at(17, 46, 2, 0);
        benchmark(c, format!("{NAME}/datetime/jiff"), |b| {
            b.iter(|| {
                assert_eq!(bb(&dt).to_string(), EXPECTED);
            })
        });
    }

    {
        const EXPECTED: &str = "2025-12-27";
        let date = civil::date(2025, 12, 27);
        benchmark(c, format!("{NAME}/date/jiff"), |b| {
            b.iter(|| {
                assert_eq!(bb(&date).to_string(), EXPECTED);
            })
        });
    }

    {
        const EXPECTED: &str = "17:46:02";
        let time = civil::time(17, 46, 2, 0);
        benchmark(c, format!("{NAME}/time/jiff"), |b| {
            b.iter(|| {
                assert_eq!(bb(&time).to_string(), EXPECTED);
            })
        });
    }

    {
        const EXPECTED: &str = "P5DT1H";
        let span = jiff::Span::new().days(5).hours(1);
        benchmark(c, format!("{NAME}/span/iso8601/jiff"), |b| {
            b.iter(|| {
                assert_eq!(bb(&span).to_string(), EXPECTED);
            })
        });
    }

    {
        const EXPECTED: &str = "5d 1h";
        let span = jiff::Span::new().days(5).hours(1);
        benchmark(c, format!("{NAME}/span/friendly/jiff"), |b| {
            b.iter(|| {
                assert_eq!(format!("{:#}", bb(&span)), EXPECTED);
            })
        });
    }

    {
        const EXPECTED: &str = "PT5H1M";
        let span = jiff::SignedDuration::new(5 * 60 * 60 + 1 * 60, 0);
        benchmark(c, format!("{NAME}/duration/iso8601/jiff"), |b| {
            b.iter(|| {
                assert_eq!(bb(&span).to_string(), EXPECTED);
            })
        });
    }

    {
        const EXPECTED: &str = "5h 1m";
        let span = jiff::SignedDuration::new(5 * 60 * 60 + 1 * 60, 0);
        benchmark(c, format!("{NAME}/duration/friendly/jiff"), |b| {
            b.iter(|| {
                assert_eq!(format!("{:#}", bb(&span)), EXPECTED);
            })
        });
    }
}

/// Measures the time it takes to print a "friendly" duration from both a
/// `jiff::Span` and a `jiff::SignedDuration`.
///
/// I "invented" this format in Jiff, and as of 2025-12-27, I believe Jiff
/// contains the only implementation thus far.
fn print_friendly(c: &mut Criterion) {
    use jiff::ToSpan;
    use std::time::Duration;

    const NAME: &str = "print/friendly";
    const TINY: &str = "2s";
    const SHORT: &str = "2h 30m";
    const MEDIUM: &str = "2d 5h 30m";
    const MEDIUM_HUMANTIME: &str = "2days 5h 30m";
    const LONG_JIFF: &str = "2y 1mo 15d 5h 59m 1s";
    const LONG_HUMANTIME: &str = "2years 1month 15days 5h 59m 1s";
    const LONGER: &str = "2y 1mo 15d 5h 59m 1s";
    const LONGER_HUMANTIME: &str = "2years 1month 15days 5h 59m 1s";
    const LONGEST: &str = "2y 1mo 15d 5h 59m 1s 123ms 456µs 789ns";
    const LONGEST_HUMANTIME: &str =
        "2years 1month 15days 5h 59m 1s 123ms 456us 789ns";
    // The longest duration parsable by Jiff and humantime that doesn't
    // involve units whose duration can change. This lets us benchmark print
    // a `SignedDuration`, which is more of an apples-to-apples comparison to
    // humantime.
    const LONGEST_TIME: &str = "5h 59m 1s 123ms 456µs 789ns";
    const LONGEST_TIME_HUMANTIME: &str = "5h 59m 1s 123ms 456us 789ns";

    let mut buf = String::with_capacity(1024);

    let benches = [
        ("tiny", TINY, 2.seconds()),
        ("short", SHORT, 2.hours().minutes(30)),
        ("medium", MEDIUM, 2.days().hours(5).minutes(30)),
        (
            "long",
            LONG_JIFF,
            2.years().months(1).days(15).hours(5).minutes(59).seconds(1),
        ),
        (
            "longer",
            LONGER,
            2.years().months(1).days(15).hours(5).minutes(59).seconds(1),
        ),
        (
            "longest",
            LONGEST,
            2.years()
                .months(1)
                .days(15)
                .hours(5)
                .minutes(59)
                .seconds(1)
                .milliseconds(123)
                .microseconds(456)
                .nanoseconds(789),
        ),
        (
            "longest-time",
            LONGEST_TIME,
            5.hours()
                .minutes(59)
                .seconds(1)
                .milliseconds(123)
                .microseconds(456)
                .nanoseconds(789),
        ),
    ];
    for (kind, expected, value) in benches {
        benchmark(c, format!("{NAME}/{kind}/span/buffer/jiff"), |b| {
            b.iter(|| {
                static PRINTER: jiff::fmt::friendly::SpanPrinter =
                    jiff::fmt::friendly::SpanPrinter::new();
                buf.clear();
                PRINTER.print_span(&value, &mut buf).unwrap();
                assert_eq!(buf, expected);
            })
        });
        benchmark(c, format!("{NAME}/{kind}/span/to_string/jiff"), |b| {
            b.iter(|| {
                static PRINTER: jiff::fmt::friendly::SpanPrinter =
                    jiff::fmt::friendly::SpanPrinter::new();
                let string = PRINTER.span_to_string(&value);
                assert_eq!(string, expected);
            })
        });
    }

    let benches = [
        ("tiny", TINY, jiff::SignedDuration::new(2, 0)),
        ("short", SHORT, jiff::SignedDuration::new(2 * 60 * 60 + 30 * 60, 0)),
        (
            "longest-time",
            LONGEST_TIME,
            jiff::SignedDuration::new(5 * 3600 + 59 * 60 + 1, 123_456_789),
        ),
    ];
    for (kind, expected, value) in benches {
        benchmark(c, format!("{NAME}/{kind}/duration/buffer/jiff"), |b| {
            b.iter(|| {
                static PRINTER: jiff::fmt::friendly::SpanPrinter =
                    jiff::fmt::friendly::SpanPrinter::new();
                buf.clear();
                PRINTER.print_duration(&value, &mut buf).unwrap();
                assert_eq!(buf, expected);
            })
        });
        benchmark(c, format!("{NAME}/{kind}/duration/to_string/jiff"), |b| {
            b.iter(|| {
                static PRINTER: jiff::fmt::friendly::SpanPrinter =
                    jiff::fmt::friendly::SpanPrinter::new();
                let string = PRINTER.duration_to_string(&value);
                assert_eq!(string, expected);
            })
        });
    }

    let benches = [
        ("tiny", TINY, Duration::new(2, 0)),
        ("short", SHORT, Duration::new(2 * 60 * 60 + 30 * 60, 0)),
        (
            "medium",
            MEDIUM_HUMANTIME,
            Duration::new(2 * 24 * 60 * 60 + 5 * 60 * 60 + 30 * 60, 0),
        ),
        (
            "long",
            LONG_HUMANTIME,
            // humantime uses a fixed number of seconds to represent years
            // and months. That is, 365.25d and 30.44d, respectively, where
            // a day is 86400 seconds.
            Duration::new(
                2 * 31_557_600
                    + 1 * 2_630_016
                    + 15 * 86400
                    + 5 * 3600
                    + 59 * 60
                    + 1,
                0,
            ),
        ),
        (
            "longer",
            LONGER_HUMANTIME,
            // humantime uses a fixed number of seconds to represent years
            // and months. That is, 365.25d and 30.44d, respectively, where
            // a day is 86400 seconds.
            Duration::new(
                2 * 31_557_600
                    + 1 * 2_630_016
                    + 15 * 86400
                    + 5 * 3600
                    + 59 * 60
                    + 1,
                0,
            ),
        ),
        (
            "longest",
            LONGEST_HUMANTIME,
            // humantime uses a fixed number of seconds to represent years
            // and months. That is, 365.25d and 30.44d, respectively, where
            // a day is 86400 seconds.
            Duration::new(
                2 * 31_557_600
                    + 1 * 2_630_016
                    + 15 * 86400
                    + 5 * 3600
                    + 59 * 60
                    + 1,
                123_456_789,
            ),
        ),
        (
            "longest-time",
            LONGEST_TIME_HUMANTIME,
            Duration::new(5 * 3600 + 59 * 60 + 1, 123_456_789),
        ),
    ];
    for (kind, expected, value) in benches {
        benchmark(
            c,
            format!("{NAME}/{kind}/duration/buffer/humantime"),
            |b| {
                b.iter(|| {
                    use std::fmt::Write;

                    buf.clear();
                    let display = humantime::format_duration(value);
                    write!(buf, "{display}").unwrap();
                    assert_eq!(buf, expected);
                })
            },
        );
        benchmark(
            c,
            format!("{NAME}/{kind}/duration/to_string/humantime"),
            |b| {
                b.iter(|| {
                    let string = humantime::format_duration(value).to_string();
                    assert_eq!(string, expected);
                })
            },
        );
    }
}

/// Measures the time it takes to print an ISO 8601 duration from both a
/// `jiff::Span` and a `jiff::SignedDuration`.
///
/// Neither `time` nor `chrono` support ISO 8601 last time I checked.
/// (Actually, it looks like `chrono` can print ISO 8601 durations via the
/// `Display` impl on its `TimeDelta` type. So we benchmark it. But... it can't
/// parse them? Weird.)
fn print_iso8601_duration(c: &mut Criterion) {
    use jiff::ToSpan;

    const NAME: &str = "print/iso8601_duration";
    const TINY: &str = "PT2S";
    const SHORT: &str = "PT2H30M";
    const MEDIUM: &str = "P2DT5H30M";
    const LONG: &str = "P2Y1M15DT5H59M1S";
    const LONG_TIME: &str = "PT5H59M1.123456789S";

    let mut buf = String::with_capacity(1024);

    let benches = [
        ("tiny", TINY, 2.seconds()),
        ("short", SHORT, 2.hours().minutes(30)),
        ("medium", MEDIUM, 2.days().hours(5).minutes(30)),
        (
            "long",
            LONG,
            2.years().months(1).days(15).hours(5).minutes(59).seconds(1),
        ),
        (
            "long-time",
            LONG_TIME,
            5.hours()
                .minutes(59)
                .seconds(1)
                .milliseconds(123)
                .microseconds(456)
                .nanoseconds(789),
        ),
    ];
    for (kind, expected, value) in benches {
        benchmark(c, format!("{NAME}/{kind}/span/buffer/jiff"), |b| {
            b.iter(|| {
                static PRINTER: jiff::fmt::temporal::SpanPrinter =
                    jiff::fmt::temporal::SpanPrinter::new();
                buf.clear();
                PRINTER.print_span(&value, &mut buf).unwrap();
                assert_eq!(buf, expected);
            })
        });
        benchmark(c, format!("{NAME}/{kind}/span/to_string/jiff"), |b| {
            b.iter(|| {
                static PRINTER: jiff::fmt::temporal::SpanPrinter =
                    jiff::fmt::temporal::SpanPrinter::new();
                let string = PRINTER.span_to_string(&value);
                assert_eq!(string, expected);
            })
        });
    }

    let benches = [
        ("tiny", TINY, jiff::SignedDuration::new(2, 0)),
        ("short", SHORT, jiff::SignedDuration::new(2 * 60 * 60 + 30 * 60, 0)),
        (
            "long-time",
            LONG_TIME,
            jiff::SignedDuration::new(5 * 3600 + 59 * 60 + 1, 123_456_789),
        ),
    ];
    for (kind, expected, value) in benches {
        benchmark(c, format!("{NAME}/{kind}/duration/buffer/jiff"), |b| {
            b.iter(|| {
                static PRINTER: jiff::fmt::temporal::SpanPrinter =
                    jiff::fmt::temporal::SpanPrinter::new();
                buf.clear();
                PRINTER.print_duration(&value, &mut buf).unwrap();
                assert_eq!(buf, expected);
            })
        });
        benchmark(c, format!("{NAME}/{kind}/duration/to_string/jiff"), |b| {
            b.iter(|| {
                static PRINTER: jiff::fmt::temporal::SpanPrinter =
                    jiff::fmt::temporal::SpanPrinter::new();
                let string = PRINTER.duration_to_string(&value);
                assert_eq!(string, expected);
            })
        });
    }

    // We benchmark Chrono here. It doesn't do any sort of balancing. It
    // just dumps the seconds (and fractional seconds). So we need to assert
    // slightly different expected values.
    let benches = [
        ("tiny", TINY, jiff::SignedDuration::new(2, 0)),
        (
            "short",
            "PT9000S",
            jiff::SignedDuration::new(2 * 60 * 60 + 30 * 60, 0),
        ),
        (
            "long-time",
            "PT21541.123456789S",
            jiff::SignedDuration::new(5 * 3600 + 59 * 60 + 1, 123_456_789),
        ),
    ];
    for (kind, expected, value) in benches {
        let value = chrono::TimeDelta::convert_from(value);
        benchmark(c, format!("{NAME}/{kind}/duration/buffer/chrono"), |b| {
            b.iter(|| {
                use std::fmt::Write;

                // N.B. `chrono` doesn't have any other APIs for this as far
                // as I can tell. The ISO 8601 printing logic is embedded
                // directly into the `Display` impl on `chrono::TimeDelta`.
                // We use `write!` here to try and avoid the alloc.
                buf.clear();
                write!(buf, "{value}").unwrap();
                assert_eq!(buf, expected);
            })
        });
        benchmark(
            c,
            format!("{NAME}/{kind}/duration/to_string/chrono"),
            |b| {
                b.iter(|| {
                    let string = value.to_string();
                    assert_eq!(string, expected);
                })
            },
        );
    }
}

/// Measures the time it takes to print a `Zoned` in the RFC 2822 format.
fn print_rfc2822(c: &mut Criterion) {
    const NAME: &str = "print/rfc2822";
    const TZ: TimeZone = TimeZone::fixed(Offset::constant(-4));
    const EXPECTED: &str = "Sat, 13 Jul 2024 17:24:59 -0400";
    const START: Timestamp = Timestamp::constant(1720905899, 0);

    let start = START.to_zoned(TZ.clone());
    let mut buf = String::with_capacity(1024);

    {
        let zdt = &start;
        benchmark(c, format!("{NAME}/buffer/jiff"), |b| {
            b.iter(|| {
                static PRINTER: jiff::fmt::rfc2822::DateTimePrinter =
                    jiff::fmt::rfc2822::DateTimePrinter::new();
                buf.clear();
                PRINTER.print_zoned(bb(&zdt), &mut buf).unwrap();
                assert_eq!(buf, EXPECTED);
            })
        });
    }

    {
        let zdt = &start;
        benchmark(c, format!("{NAME}/to_string/jiff"), |b| {
            b.iter(|| {
                static PRINTER: jiff::fmt::rfc2822::DateTimePrinter =
                    jiff::fmt::rfc2822::DateTimePrinter::new();
                let got = PRINTER.zoned_to_string(bb(&zdt)).unwrap();
                assert_eq!(got, EXPECTED);
            })
        });
    }

    {
        let dt = chrono::DateTime::convert_from(start.clone());
        let items =
            [chrono::format::Item::Fixed(chrono::format::Fixed::RFC2822)];
        benchmark(c, format!("{NAME}/buffer/chrono"), |b| {
            b.iter(|| {
                buf.clear();
                bb(dt)
                    .format_with_items(items.as_slice().iter())
                    .write_to(&mut buf)
                    .unwrap();
                assert_eq!(buf, EXPECTED);
            })
        });
    }

    {
        let dt = chrono::DateTime::convert_from(start.clone());
        let items =
            [chrono::format::Item::Fixed(chrono::format::Fixed::RFC2822)];
        benchmark(c, format!("{NAME}/to_string/chrono"), |b| {
            b.iter(|| {
                let got = bb(dt)
                    .format_with_items(items.as_slice().iter())
                    .to_string();
                assert_eq!(got, EXPECTED);
            })
        });
    }

    {
        let dt = time::OffsetDateTime::convert_from(start.clone());
        let format = time::format_description::well_known::Rfc2822;
        let mut buf = Vec::with_capacity(1024);
        benchmark(c, format!("{NAME}/buffer/time"), |b| {
            b.iter(|| {
                buf.clear();
                let _ = dt.format_into(&mut buf, &format).unwrap();
                assert_eq!(buf, EXPECTED.as_bytes());
            })
        });
    }

    {
        let dt = time::OffsetDateTime::convert_from(start.clone());
        let format = time::format_description::well_known::Rfc2822;
        benchmark(c, format!("{NAME}/to_string/time"), |b| {
            b.iter(|| {
                let got = dt.format(&format).unwrap();
                assert_eq!(got, EXPECTED);
            })
        });
    }
}

/// Measures the time it takes to print a `Zoned` in the RFC 3339 format.
fn print_rfc3339(c: &mut Criterion) {
    const NAME: &str = "print/rfc3339";
    const TZ: TimeZone = TimeZone::fixed(Offset::constant(-5));
    const EXPECTED: &str = "2025-12-27T19:46:02-05:00";
    const START: Timestamp = Timestamp::constant(1766882762, 0);

    let start = START.to_zoned(TZ.clone());
    let mut buf = String::with_capacity(1024);

    {
        let zdt = &start;
        benchmark(c, format!("{NAME}/buffer/jiff"), |b| {
            b.iter(|| {
                static PRINTER: jiff::fmt::temporal::DateTimePrinter =
                    jiff::fmt::temporal::DateTimePrinter::new();
                buf.clear();
                PRINTER
                    .print_timestamp_with_offset(
                        bb(&zdt.timestamp()),
                        bb(zdt.offset()),
                        &mut buf,
                    )
                    .unwrap();
                assert_eq!(buf, EXPECTED);
            })
        });
    }

    {
        let zdt = &start;
        benchmark(c, format!("{NAME}/to_string/jiff"), |b| {
            b.iter(|| {
                static PRINTER: jiff::fmt::temporal::DateTimePrinter =
                    jiff::fmt::temporal::DateTimePrinter::new();
                let got = PRINTER.timestamp_with_offset_to_string(
                    bb(&zdt.timestamp()),
                    bb(zdt.offset()),
                );
                assert_eq!(got, EXPECTED);
            })
        });
    }

    {
        let dt = chrono::DateTime::convert_from(start.clone());
        let items =
            [chrono::format::Item::Fixed(chrono::format::Fixed::RFC3339)];
        benchmark(c, format!("{NAME}/buffer/chrono"), |b| {
            b.iter(|| {
                buf.clear();
                bb(dt)
                    .format_with_items(items.as_slice().iter())
                    .write_to(&mut buf)
                    .unwrap();
                assert_eq!(buf, EXPECTED);
            })
        });
    }

    {
        let dt = chrono::DateTime::convert_from(start.clone());
        let items =
            [chrono::format::Item::Fixed(chrono::format::Fixed::RFC3339)];
        benchmark(c, format!("{NAME}/to_string/chrono"), |b| {
            b.iter(|| {
                let got = bb(dt)
                    .format_with_items(items.as_slice().iter())
                    .to_string();
                assert_eq!(got, EXPECTED);
            })
        });
    }

    {
        let dt = time::OffsetDateTime::convert_from(start.clone());
        let format = time::format_description::well_known::Rfc3339;
        let mut buf = Vec::with_capacity(1024);
        benchmark(c, format!("{NAME}/buffer/time"), |b| {
            b.iter(|| {
                buf.clear();
                let _ = dt.format_into(&mut buf, &format).unwrap();
                assert_eq!(buf, EXPECTED.as_bytes());
            })
        });
    }

    {
        let dt = time::OffsetDateTime::convert_from(start.clone());
        let format = time::format_description::well_known::Rfc3339;
        benchmark(c, format!("{NAME}/to_string/time"), |b| {
            b.iter(|| {
                let got = dt.format(&format).unwrap();
                assert_eq!(got, EXPECTED);
            })
        });
    }
}

/// Measures the time it takes to print a `Zoned` in the RFC 3339 format.
fn print_rfc9557(c: &mut Criterion) {
    const NAME: &str = "print/rfc9557";
    const TZ: &str = "America/New_York";
    const EXPECTED: &str = "2025-12-27T19:46:02-05:00[America/New_York]";
    const START: Timestamp = Timestamp::constant(1766882762, 0);

    let tz = TimeZone::get(TZ).unwrap();
    let start = START.to_zoned(tz.clone());
    let mut buf = String::with_capacity(1024);

    {
        let zdt = &start;
        benchmark(c, format!("{NAME}/buffer/jiff"), |b| {
            b.iter(|| {
                static PRINTER: jiff::fmt::temporal::DateTimePrinter =
                    jiff::fmt::temporal::DateTimePrinter::new();
                buf.clear();
                PRINTER.print_zoned(bb(zdt), &mut buf).unwrap();
                assert_eq!(buf, EXPECTED);
            })
        });
    }

    {
        let zdt = &start;
        benchmark(c, format!("{NAME}/to_string/jiff"), |b| {
            b.iter(|| {
                static PRINTER: jiff::fmt::temporal::DateTimePrinter =
                    jiff::fmt::temporal::DateTimePrinter::new();
                let got = PRINTER.zoned_to_string(bb(&zdt));
                assert_eq!(got, EXPECTED);
            })
        });
    }

    // N.B. As of 2025-12-27, neither `chrono` nor `time` support RFC 9557.
}

/// Measures the time it takes to print a datetime via `strftime`.
///
/// This tries to use the fastest possible API instead of the most convenient.
/// Specifically, this means using APIs that avoid allocating a new `String`
/// for every call.
fn print_strftime(c: &mut Criterion) {
    const NAME: &str = "print/strftime";
    const EXPECTED: &str = "Mon Jul 15 04:24:59 PM -0400 2024";
    const DATETIME: civil::DateTime =
        civil::date(2024, 7, 15).at(16, 24, 59, 0);
    const FMT: &str = "%a %b %e %I:%M:%S %p %z %Y";
    const TZ: jiff::tz::TimeZone =
        jiff::tz::TimeZone::fixed(jiff::tz::offset(-4));
    // `time` doesn't have strtime-like APIs, but does provide its own
    // custom formatting machinery. So we just use that since it's solving
    // roughly the same problem as strftime.
    //
    // NOTE: At time of writing (2025-04-28), `time` actually does have
    // `strftime`-style APIs, but I decided to just copy this from the existing
    // `strptime` benchmark for now. (Which was written before `time` had a
    // `strptime`-style API.)
    const TIME_FMT: &[time::format_description::BorrowedFormatItem] = time::macros::format_description!(
        "[weekday repr:short case_sensitive:false] \
         [month repr:short case_sensitive:false] \
         [day] \
         [hour repr:12]:[minute]:[second] \
         [period] \
         [offset_hour sign:mandatory][offset_minute] \
         [year]"
    );
    let zdt = DATETIME.to_zoned(TZ.clone()).unwrap();
    let mut buf = String::with_capacity(1024);

    {
        benchmark(c, format!("{NAME}/oneshot/jiff"), |b| {
            b.iter(|| {
                buf.clear();
                let tm = jiff::fmt::strtime::BrokenDownTime::from(&zdt);
                tm.format(bb(FMT), &mut buf).unwrap();
                assert_eq!(buf, EXPECTED);
            })
        });
    }

    {
        let dt = chrono::DateTime::convert_from(zdt.clone());
        benchmark(c, format!("{NAME}/oneshot/chrono"), |b| {
            b.iter(|| {
                buf.clear();
                bb(dt).format(bb(FMT)).write_to(&mut buf).unwrap();
                assert_eq!(buf, EXPECTED);
            })
        });
    }

    {
        let dt = chrono::DateTime::convert_from(zdt.clone());
        let items =
            chrono::format::strftime::StrftimeItems::new(FMT).parse().unwrap();
        benchmark(c, format!("{NAME}/prebuilt/chrono"), |b| {
            b.iter(|| {
                buf.clear();
                bb(dt)
                    .format_with_items(items.as_slice().iter())
                    .write_to(&mut buf)
                    .unwrap();
                assert_eq!(buf, EXPECTED);
            })
        });
    }

    {
        // `time` requires `std::io::Write`...
        let mut buf = Vec::with_capacity(1024);
        let odt = time::OffsetDateTime::convert_from(zdt.clone());
        benchmark(c, format!("{NAME}/prebuilt/time"), |b| {
            b.iter(|| {
                buf.clear();
                bb(odt).format_into(&mut buf, &TIME_FMT).unwrap();
                assert_eq!(buf, EXPECTED.as_bytes());
            })
        });
    }
}
