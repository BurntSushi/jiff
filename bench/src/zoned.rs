use std::hint::black_box as bb;

use criterion::Criterion;
use jiff::{
    civil,
    tz::{Offset, TimeZone},
    Timestamp, ToSpan,
};

use crate::{benchmark, convert::ConvertFrom};

pub(super) fn define(c: &mut Criterion) {
    add_calendar(c);
    default(c);
    fixed_offset_add_time(c);
    fixed_offset_to_civil_datetime(c);
    fixed_offset_to_timestamp(c);
}

/// Measures adding calendar units to a datetime in an IANA time zone.
///
/// Calendar-only additions can reuse the offset from civil datetime
/// resolution. Gap, fold and mixed calendar/time cases are also included.
///
/// Ref: https://github.com/BurntSushi/jiff/pull/666
fn add_calendar(c: &mut Criterion) {
    const NAME: &str = "zoned/add_calendar";

    let tz = TimeZone::get("America/New_York").unwrap();
    for (label, start, span, expected) in [
        (
            "day",
            civil::date(2024, 6, 30).at(9, 46, 0, 0),
            1.day(),
            civil::date(2024, 7, 1).at(9, 46, 0, 0),
        ),
        (
            "month",
            civil::date(2024, 1, 31).at(2, 30, 0, 0),
            1.month(),
            civil::date(2024, 2, 29).at(2, 30, 0, 0),
        ),
        (
            "dst",
            civil::date(2024, 3, 9).at(12, 0, 0, 0),
            1.day(),
            civil::date(2024, 3, 10).at(12, 0, 0, 0),
        ),
        (
            "gap",
            civil::date(2024, 3, 9).at(2, 30, 0, 0),
            1.day(),
            civil::date(2024, 3, 10).at(3, 30, 0, 0),
        ),
        (
            "fold",
            civil::date(2024, 11, 2).at(1, 30, 0, 0),
            1.day(),
            civil::date(2024, 11, 3).at(1, 30, 0, 0),
        ),
        (
            "mixed",
            civil::date(2024, 6, 30).at(9, 46, 0, 0),
            1.day().hours(1),
            civil::date(2024, 7, 1).at(10, 46, 0, 0),
        ),
    ] {
        let start = start.to_zoned(tz.clone()).unwrap();
        let expected = expected.to_zoned(tz.clone()).unwrap();
        benchmark(c, format!("{NAME}/{label}/jiff"), |b| {
            b.iter(|| {
                let end = bb(&start).checked_add(bb(span)).unwrap();
                assert_eq!(bb(end), expected);
            })
        });
    }
}

/// Measures the time that `Zoned::default()` takes.
///
/// This is a little weird in that it usually doesn't matter how fast this
/// runs. But default values are used often as throw-away values[1] and perf
/// can matter.
///
/// Previously, `Zoned::default()` went through `Zoned::new()`, which does
/// offset lookup and a translation to a civil datetime. This benchmarks tests
/// that we do something smarter: just fix everything to the expected values.
///
/// [1]: https://github.com/BurntSushi/jiff/pull/492#discussion_r2751601292
fn default(c: &mut Criterion) {
    const NAME: &str = "zoned/default";

    {
        benchmark(
            c,
            format!("{NAME}/jiff"),
            #[inline(never)]
            |b| {
                b.iter(|| {
                    for _ in 0..50 {
                        let got = bb(jiff::Zoned::default());
                        assert_eq!(got.timestamp().as_second(), bb(0));
                    }
                })
            },
        );
    }
}

/// Measures how long it takes to add 24 hours to a fixed offset datetime.
///
/// Note that we used a fixed offset as our time zone in order to accommodate
/// the lowest common denominator.
///
/// Jiff doesn't do as well here compared to Chrono because a `Zoned` in Jiff
/// is a much heavier weight type. e.g., It has more stuff in it (timestamp,
/// offset, civil datetime and time zone) and creating a new `Zoned` means
/// an `Arc::clone`. If one really just wants a fixed offset timestamp with
/// the best possible perf, then probably a `TimestampWithOffset { timestamp,
/// offset }` is the way to go.
fn fixed_offset_add_time(c: &mut Criterion) {
    const NAME: &str = "zoned/fixed_offset_add_time";
    const TZ: TimeZone = TimeZone::fixed(Offset::constant(-4));
    const START: Timestamp = Timestamp::constant(1719755160, 0);
    const EXPECTED: Timestamp =
        Timestamp::constant(1719755160 + (24 * 60 * 60), 0);

    let start = START.to_zoned(TZ.clone());
    let expected = EXPECTED.to_zoned(TZ.clone());

    {
        let span = 24.hours();
        benchmark(c, format!("{NAME}/span/jiff"), |b| {
            b.iter(|| {
                let end = bb(&start).checked_add(bb(span)).unwrap();
                assert_eq!(end, expected);
            })
        });

        let duration = jiff::SignedDuration::from_hours(24);
        benchmark(c, format!("{NAME}/duration/jiff"), |b| {
            b.iter(|| {
                let end = bb(&start).checked_add(bb(duration)).unwrap();
                assert_eq!(end, expected);
            })
        });
    }

    {
        let start = chrono::DateTime::convert_from(start.clone());
        let expected = chrono::DateTime::convert_from(expected.clone());
        let delta = chrono::TimeDelta::hours(24);
        benchmark(c, format!("{NAME}/duration/chrono"), |b| {
            b.iter(|| {
                let end = bb(start).checked_add_signed(bb(delta)).unwrap();
                assert_eq!(end, expected);
            })
        });
    }

    {
        let start = time::OffsetDateTime::convert_from(start.clone());
        let expected = time::OffsetDateTime::convert_from(expected.clone());
        let duration = time::Duration::hours(24);
        benchmark(c, format!("{NAME}/duration/time"), |b| {
            b.iter(|| {
                let end = bb(start).checked_add(bb(duration)).unwrap();
                assert_eq!(end, expected);
            })
        });
    }
}

/// This benchmarks the case where one already has a fixed offset datetime,
/// and measures how long it takes to get a civil datetime.
///
/// For Jiff, a fixed offset datetime is both a timestamp and a civil datetime,
/// so this operation is effectively free.
///
/// For Chrono, its zone aware datetime stores a civil datetime in UTC, so to
/// get the "local" civil time, some arithmetic on the UTC civil datetime needs
/// to be performed.
///
/// For `time`, its zone aware datetime stores a "local" civil datetime, so
/// this operation is effectively free.
///
/// 2025-01-05: `time` does quite a bit better than Jiff on this benchmark. It
/// looks like it's because `time`'s `PartialEq` impl for `PrimitiveDateTime`
/// is better optimized than Jiff's.
fn fixed_offset_to_civil_datetime(c: &mut Criterion) {
    const NAME: &str = "zoned/fixed_offset_to_civil_datetime";
    const TZ: TimeZone = TimeZone::fixed(Offset::constant(-4));
    const STAMP: Timestamp = Timestamp::constant(1719755160, 0);
    const EXPECTED: civil::DateTime = civil::date(2024, 6, 30).at(9, 46, 0, 0);

    let zdt = STAMP.to_zoned(TZ.clone());

    {
        benchmark(c, format!("{NAME}/jiff"), |b| {
            b.iter(|| {
                assert_eq!(bb(&zdt).datetime(), EXPECTED);
            })
        });
    }

    {
        let expected = chrono::NaiveDateTime::convert_from(EXPECTED);
        let zdt = chrono::DateTime::convert_from(zdt.clone());
        benchmark(c, format!("{NAME}/chrono"), |b| {
            b.iter(|| {
                assert_eq!(bb(zdt).naive_local(), expected);
            })
        });
    }

    {
        let expected = time::PrimitiveDateTime::convert_from(EXPECTED);
        let zdt = time::OffsetDateTime::convert_from(zdt.clone());
        benchmark(c, format!("{NAME}/time"), |b| {
            b.iter(|| {
                let dt = time::PrimitiveDateTime::new(
                    bb(zdt.date()),
                    bb(zdt.time()),
                );
                assert_eq!(dt, expected);
            })
        });
    }
}

/// This benchmarks the time it takes to get a timestamp from a library's
/// fixed offset datetime type.
///
/// Jiff uses a timestamp internally, so this is effectively free.
///
/// Chrono and `time` both use civil datetimes internally, so they must do a
/// conversion step.
fn fixed_offset_to_timestamp(c: &mut Criterion) {
    const NAME: &str = "zoned/fixed_offset_to_timestamp";
    const TZ: TimeZone = TimeZone::fixed(Offset::constant(-4));
    const STAMP: Timestamp = Timestamp::constant(1719755160, 0);

    let zdt = STAMP.to_zoned(TZ.clone());

    {
        benchmark(c, format!("{NAME}/jiff"), |b| {
            b.iter(|| {
                assert_eq!(bb(&zdt).timestamp(), STAMP);
            })
        });
    }

    {
        let zdt = chrono::DateTime::convert_from(zdt.clone());
        let stamp = STAMP.as_second();
        benchmark(c, format!("{NAME}/chrono"), |b| {
            b.iter(|| {
                assert_eq!(bb(zdt).timestamp(), stamp);
            })
        });
    }

    {
        let zdt = time::OffsetDateTime::convert_from(zdt.clone());
        let stamp = STAMP.as_second();
        benchmark(c, format!("{NAME}/time"), |b| {
            b.iter(|| {
                assert_eq!(bb(zdt).unix_timestamp(), stamp);
            })
        });
    }
}
