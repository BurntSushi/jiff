use std::hint::black_box as bb;

use criterion::Criterion;
use jiff::{
    civil,
    tz::{Offset, TimeZone},
    Timestamp, ToSpan,
};

use crate::{benchmark, convert::ConvertFrom};

pub(super) fn define(c: &mut Criterion) {
    fixed_offset_add_time(c);
    fixed_offset_to_civil_datetime(c);
    fixed_offset_to_timestamp(c);
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
    const OFFSET: Offset = Offset::constant(-4);
    const START: Timestamp = Timestamp::constant(1719755160, 0);
    const EXPECTED: Timestamp =
        Timestamp::constant(1719755160 + (24 * 60 * 60), 0);

    let tz = TimeZone::fixed(OFFSET);
    let start = START.to_zoned(tz.clone());
    let expected = EXPECTED.to_zoned(tz.clone());

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
fn fixed_offset_to_civil_datetime(c: &mut Criterion) {
    const NAME: &str = "zoned/fixed_offset_to_civil_datetime";
    const OFFSET: Offset = Offset::constant(-4);
    const STAMP: Timestamp = Timestamp::constant(1719755160, 0);
    const EXPECTED: civil::DateTime = civil::date(2024, 6, 30).at(9, 46, 0, 0);

    let tz = TimeZone::fixed(OFFSET);
    let zdt = STAMP.to_zoned(tz.clone());

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
    const OFFSET: Offset = Offset::constant(-4);
    const STAMP: Timestamp = Timestamp::constant(1719755160, 0);

    let tz = TimeZone::fixed(OFFSET);
    let zdt = STAMP.to_zoned(tz.clone());

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
