use std::hint::black_box as bb;

use criterion::Criterion;
use jiff::{civil, tz::TimeZone};

use crate::{benchmark, convert::ConvertFrom};

pub(super) fn define(c: &mut Criterion) {
    parse_civil_datetime(c);
    parse_friendly(c);
    parse_iso8601_duration(c);
    parse_rfc2822(c);
    parse_strptime(c);
}

/// Measures the time it takes to parse a civil datetime in ISO 8601 format.
fn parse_civil_datetime(c: &mut Criterion) {
    const NAME: &str = "parse/civil_datetime";
    const STRING: &str = "2024-06-30T09:46:00";
    const EXPECTED: civil::DateTime = civil::date(2024, 6, 30).at(9, 46, 0, 0);

    {
        let expected = EXPECTED;
        benchmark(c, format!("{NAME}/jiff"), |b| {
            b.iter(|| {
                let dt: civil::DateTime = bb(STRING).parse().unwrap();
                assert_eq!(dt, expected);
            })
        });
    }

    {
        let expected = chrono::NaiveDateTime::convert_from(EXPECTED);
        benchmark(c, format!("{NAME}/chrono"), |b| {
            b.iter(|| {
                let dt: chrono::NaiveDateTime = bb(STRING).parse().unwrap();
                assert_eq!(dt, expected);
            })
        });
    }

    {
        let expected = time::PrimitiveDateTime::convert_from(EXPECTED);
        benchmark(c, format!("{NAME}/time"), |b| {
            b.iter(|| {
                let dt = time::PrimitiveDateTime::parse(
                    bb(STRING),
                    &time::format_description::well_known::Iso8601::DEFAULT,
                )
                .unwrap();
                assert_eq!(dt, expected);
            })
        });
    }
}

/// Benchmarks parsing a "friendly" or "human" duration. We compare Jiff with
/// `humantime`.
fn parse_friendly(c: &mut Criterion) {
    use jiff::{SignedDuration, Span, ToSpan};
    use std::time::Duration;

    const NAME: &str = "parse/friendly";
    const TINY: &str = "2s";
    const SHORT: &str = "2h30m";
    const MEDIUM: &str = "2d5h30m";
    const LONG_JIFF: &str = "2y1mo15d5h59m1s";
    const LONG_HUMANTIME: &str = "2y1M15d5h59m1s";
    const LONGER: &str = "2 years 1 month 15 days 5 hours 59 minutes 1 second";
    const LONGEST: &str = "\
        2 years 1 month 15 days \
        5 hours 59 minutes 1 second \
        123 millis 456 usec 789 nanos\
    ";
    // The longest duration parsable by Jiff and humantime that doesn't involve
    // units whose duration can change. This lets us benchmark parsing into a
    // `SignedDuration`, which is more of an apples-to-apples comparison to
    // humantime.
    const LONGEST_TIME: &str = "\
        5 hours 59 minutes 1 second \
        123 millis 456 usec 789 nanos\
    ";

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
    for (kind, input, expected) in benches {
        benchmark(c, format!("{NAME}/{kind}/span/jiff"), |b| {
            b.iter(|| {
                let got: Span = input.parse().unwrap();
                assert_eq!(got.fieldwise(), expected.fieldwise());
            })
        });
    }

    let benches = [
        ("tiny", TINY, SignedDuration::new(2, 0)),
        ("short", SHORT, SignedDuration::new(2 * 60 * 60 + 30 * 60, 0)),
        (
            "longest-time",
            LONGEST_TIME,
            SignedDuration::new(5 * 3600 + 59 * 60 + 1, 123_456_789),
        ),
    ];
    for (kind, input, expected) in benches {
        benchmark(c, format!("{NAME}/{kind}/duration/jiff"), |b| {
            b.iter(|| {
                let got: SignedDuration = input.parse().unwrap();
                assert_eq!(got, expected);
            })
        });
    }

    let benches = [
        ("tiny", TINY, Duration::new(2, 0)),
        ("short", SHORT, Duration::new(2 * 60 * 60 + 30 * 60, 0)),
        (
            "medium",
            MEDIUM,
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
            LONGER,
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
            LONGEST,
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
            LONGEST_TIME,
            Duration::new(5 * 3600 + 59 * 60 + 1, 123_456_789),
        ),
    ];
    for (kind, input, expected) in benches {
        benchmark(c, format!("{NAME}/{kind}/duration/humantime"), |b| {
            b.iter(|| {
                let got = humantime::parse_duration(input).unwrap();
                assert_eq!(got, expected);
            })
        });
    }
}

/// Benchmarks parsing an ISO 8601 duration. I think Jiff is alone in being
/// able to parse ISO 8601 durations (among itself, chrono and time).
fn parse_iso8601_duration(c: &mut Criterion) {
    use jiff::{SignedDuration, Span, ToSpan};

    const NAME: &str = "parse/iso8601_duration";
    const TINY: &str = "PT2S";
    const SHORT: &str = "PT2H30M";
    const MEDIUM: &str = "P2DT5H30M";
    const LONG: &str = "P2Y1M15DT5H59M1S";
    const LONG_TIME: &str = "PT5H59M1.123456789S";

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
    for (kind, input, expected) in benches {
        benchmark(c, format!("{NAME}/{kind}/span/jiff"), |b| {
            b.iter(|| {
                let got: Span = input.parse().unwrap();
                assert_eq!(got.fieldwise(), expected.fieldwise());
            })
        });
    }

    let benches = [
        ("tiny", TINY, SignedDuration::new(2, 0)),
        ("short", SHORT, SignedDuration::new(2 * 60 * 60 + 30 * 60, 0)),
        (
            "long-time",
            LONG_TIME,
            SignedDuration::new(5 * 3600 + 59 * 60 + 1, 123_456_789),
        ),
    ];
    for (kind, input, expected) in benches {
        benchmark(c, format!("{NAME}/{kind}/duration/jiff"), |b| {
            b.iter(|| {
                let got: SignedDuration = input.parse().unwrap();
                assert_eq!(got, expected);
            })
        });
    }
}

/// Measures the time it takes to parse an RFC 2822 datetime as a timestamp.
fn parse_rfc2822(c: &mut Criterion) {
    const NAME: &str = "parse/rfc2822";
    const STRING: &str = "Sat, 13 Jul 2024 17:24:59 -0400";
    const EXPECTED: civil::DateTime =
        civil::date(2024, 7, 13).at(21, 24, 59, 0);
    let expected = EXPECTED.to_zoned(TimeZone::UTC).unwrap().timestamp();

    {
        benchmark(c, format!("{NAME}/jiff"), |b| {
            b.iter(|| {
                let ts = jiff::fmt::rfc2822::DateTimeParser::new()
                    .parse_timestamp(bb(STRING))
                    .unwrap();
                assert_eq!(ts, expected);
            })
        });
    }

    {
        let expected = chrono::DateTime::convert_from(expected);
        benchmark(c, format!("{NAME}/chrono"), |b| {
            b.iter(|| {
                let dt =
                    chrono::DateTime::parse_from_rfc2822(bb(STRING)).unwrap();
                assert_eq!(dt, expected);
            })
        });
    }

    {
        let expected = time::OffsetDateTime::convert_from(expected);
        benchmark(c, format!("{NAME}/time"), |b| {
            b.iter(|| {
                let odt = time::OffsetDateTime::parse(
                    bb(STRING),
                    &time::format_description::well_known::Rfc2822,
                )
                .unwrap();
                assert_eq!(odt, expected);
            })
        });
    }
}

/// Measures time it takes to parse via a `strptime` format
/// string into a timestamp.
fn parse_strptime(c: &mut Criterion) {
    const NAME: &str = "parse/strptime";
    const STRING: &str = "Mon Jul 15 04:24:59 PM -0400 2024";
    const EXPECTED: civil::DateTime =
        civil::date(2024, 7, 15).at(20, 24, 59, 0);
    const FMT: &str = "%a %b %e %I:%M:%S %p %z %Y";
    // `time` doesn't have strtime-like APIs, but does provide its own
    // custom formatting machinery. So we just use that since it's solving
    // roughly the same problem as strptime.
    const TIME_FMT: &[time::format_description::BorrowedFormatItem] = time::macros::format_description!(
        "[weekday repr:short case_sensitive:false] \
         [month repr:short case_sensitive:false] \
         [day] \
         [hour repr:12]:[minute]:[second] \
         [period] \
         [offset_hour sign:mandatory][offset_minute] \
         [year]"
    );
    let expected = EXPECTED.to_zoned(TimeZone::UTC).unwrap().timestamp();

    {
        benchmark(c, format!("{NAME}/oneshot/jiff"), |b| {
            b.iter(|| {
                let ts =
                    jiff::Timestamp::strptime(bb(FMT), bb(STRING)).unwrap();
                assert_eq!(ts, expected);
            })
        });
    }

    {
        let expected = chrono::DateTime::convert_from(expected);
        benchmark(c, format!("{NAME}/oneshot/chrono"), |b| {
            b.iter(|| {
                let dt = chrono::DateTime::parse_from_str(bb(STRING), bb(FMT))
                    .unwrap();
                assert_eq!(dt, expected);
            })
        });
    }

    {
        let expected = chrono::DateTime::convert_from(expected);
        let items =
            chrono::format::strftime::StrftimeItems::new(FMT).parse().unwrap();
        benchmark(c, format!("{NAME}/prebuilt/chrono"), |b| {
            b.iter(|| {
                let mut parsed = chrono::format::Parsed::new();
                chrono::format::parse(
                    &mut parsed,
                    bb(STRING),
                    items.as_slice().iter(),
                )
                .unwrap();
                let dt = parsed.to_datetime().unwrap();
                assert_eq!(dt, expected);
            })
        });
    }

    {
        let expected = time::OffsetDateTime::convert_from(expected);
        benchmark(c, format!("{NAME}/prebuilt/time"), |b| {
            b.iter(|| {
                let odt = time::OffsetDateTime::parse(bb(STRING), &TIME_FMT)
                    .unwrap();
                assert_eq!(odt, expected);
            })
        });
    }
}
