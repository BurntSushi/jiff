use std::hint::black_box as bb;

use criterion::Criterion;
use jiff::{
    civil,
    tz::{AmbiguousOffset, Offset, TimeZone, TimeZoneDatabase},
    Timestamp,
};

use crate::benchmark;

pub(super) fn define(c: &mut Criterion) {
    posix_datetime_to_offset(c);
    posix_timestamp_to_offset(c);
    tzif_bundled_datetime_to_offset(c);
    tzif_bundled_timestamp_to_offset(c);
    tzif_future_datetime_to_offset(c);
    tzif_future_timestamp_to_offset(c);
    tzif_historical_datetime_to_offset(c);
    tzif_historical_timestamp_to_offset(c);
}

/// Measures how long it takes to map a civil datetime to a possibly ambiguous
/// timestamp using a POSIX time zone.
fn posix_datetime_to_offset(c: &mut Criterion) {
    const NAME: &str = "tz/posix_datetime_to_offset";
    const DATETIME: civil::DateTime = civil::date(2024, 6, 30).at(9, 46, 0, 0);
    const TZ: &str = "EST5EDT,M3.2.0,M11.1.0";
    const EXPECTED_OFFSET: Offset = Offset::constant(-4);
    const EXPECTED: AmbiguousOffset =
        AmbiguousOffset::Unambiguous { offset: EXPECTED_OFFSET };

    let tz = TimeZone::posix(TZ).unwrap();
    {
        benchmark(c, format!("{NAME}/jiff"), |b| {
            b.iter(|| {
                let ambiguous = bb(&tz).to_ambiguous_timestamp(bb(DATETIME));
                assert_eq!(ambiguous.offset(), EXPECTED);
            })
        });
    }
}

/// Measures how long it takes to map a timestamp to an offset using a POSIX
/// time zone.
fn posix_timestamp_to_offset(c: &mut Criterion) {
    const NAME: &str = "tz/posix_timestamp_to_offset";
    const STAMP: Timestamp = Timestamp::constant(1719755160, 0);
    const TZ: &str = "EST5EDT,M3.2.0,M11.1.0";
    const EXPECTED: Offset = Offset::constant(-4);

    let tz = TimeZone::posix(TZ).unwrap();
    {
        benchmark(c, format!("{NAME}/jiff"), |b| {
            b.iter(|| {
                let offset = bb(&tz).to_offset(bb(STAMP));
                assert_eq!(offset, EXPECTED);
            })
        });
    }
}

/// Measures how long it takes to map a civil datetime to a possibly ambiguous
/// timestamp using a TZif time zone's current data from `jiff-tzdb`. That is,
/// we pick a time zone and a timestamp around the current time (2025-02-27).
///
/// This is relevant because the `jiff-tzdb` bundled data uses "slim" TZif
/// data, where transitions are only present for historical data. And anything
/// later (e.g., after 2007 in `America/New_York`) are handled by POSIX time
/// zones.
///
/// This is relevant for benchmarking because a binary search on explicit
/// transitions in TZif data tends to be faster than POSIX time zones. This
/// benchmark explicitly captures an optimization where Jiff effectively turns
/// "slim" TZif data into fat TZif data in memory.
fn tzif_bundled_datetime_to_offset(c: &mut Criterion) {
    const NAME: &str = "tz/tzif_bundled_datetime_to_offset";
    const DATETIME: civil::DateTime = civil::date(2024, 6, 30).at(9, 46, 0, 0);
    const TZ: &str = "America/New_York";
    const EXPECTED_OFFSET: Offset = Offset::constant(-4);
    const EXPECTED: AmbiguousOffset =
        AmbiguousOffset::Unambiguous { offset: EXPECTED_OFFSET };

    let db = TimeZoneDatabase::bundled();
    let tz = db.get(TZ).unwrap();
    {
        benchmark(c, format!("{NAME}/jiff"), |b| {
            b.iter(|| {
                let ambiguous = bb(&tz).to_ambiguous_timestamp(bb(DATETIME));
                assert_eq!(ambiguous.offset(), EXPECTED);
            })
        });
    }
}

/// Measures how long it takes to map a timestamp to an offset using a TZif
/// time zone's current data from `jiff-tzdb`. That is, we pick a time zone and
/// a timestamp around the current time (2025-02-27).
///
/// This is relevant because the `jiff-tzdb` bundled data uses "slim" TZif
/// data, where transitions are only present for historical data. And anything
/// later (e.g., after 2007 in `America/New_York`) are handled by POSIX time
/// zones.
///
/// This is relevant for benchmarking because a binary search on explicit
/// transitions in TZif data tends to be faster than POSIX time zones. This
/// benchmark explicitly captures an optimization where Jiff effectively turns
/// "slim" TZif data into fat TZif data in memory.
fn tzif_bundled_timestamp_to_offset(c: &mut Criterion) {
    const NAME: &str = "tz/tzif_bundled_timestamp_to_offset";
    const STAMP: Timestamp = Timestamp::constant(1719755160, 0);
    const TZ: &str = "America/New_York";
    const EXPECTED: Offset = Offset::constant(-4);

    let db = TimeZoneDatabase::bundled();
    let tz = db.get(TZ).unwrap();
    {
        benchmark(c, format!("{NAME}/jiff"), |b| {
            b.iter(|| {
                let offset = bb(&tz).to_offset(bb(STAMP));
                assert_eq!(offset, EXPECTED);
            })
        });
    }
}

/// Measures how long it takes to map a civil datetime to a possibly ambiguous
/// timestamp using a TZif time zone's *non-historical* data. That is, we pick
/// a time zone and a timestamp far enough in the future that it will have to
/// use the POSIX time zone. And we explicitly pick a date far enough in the
/// future that even our optimization to "fatten" up slim TZif data won't
/// reasonably apply.
fn tzif_future_datetime_to_offset(c: &mut Criterion) {
    const NAME: &str = "tz/tzif_future_datetime_to_offset";
    // America/New_York on my system only has transitions to 2037 (2025-02-27).
    const DATETIME: civil::DateTime = civil::date(2100, 7, 1).at(17, 0, 0, 0);
    const TZ: &str = "America/New_York";
    const EXPECTED_OFFSET: Offset = Offset::constant(-4);
    const EXPECTED: AmbiguousOffset =
        AmbiguousOffset::Unambiguous { offset: EXPECTED_OFFSET };

    let tz = TimeZone::get(TZ).unwrap();
    {
        benchmark(c, format!("{NAME}/jiff"), |b| {
            b.iter(|| {
                let ambiguous = bb(&tz).to_ambiguous_timestamp(bb(DATETIME));
                assert_eq!(ambiguous.offset(), EXPECTED);
            })
        });
    }
}

/// Measures how long it takes to map a timestamp to an offset using a TZif
/// time zone's *non-historical* data. That is, we pick a time zone and a
/// timestamp far enough in the future that it will have to use the POSIX time
/// zone. And we explicitly pick a date far enough in the future that even our
/// optimization to "fatten" up slim TZif data won't reasonably apply.
fn tzif_future_timestamp_to_offset(c: &mut Criterion) {
    const NAME: &str = "tz/tzif_future_timestamp_to_offset";
    const STAMP: Timestamp = Timestamp::constant(4118083200, 0);
    const TZ: &str = "America/New_York";
    const EXPECTED: Offset = Offset::constant(-4);

    let tz = TimeZone::get(TZ).unwrap();
    {
        benchmark(c, format!("{NAME}/jiff"), |b| {
            b.iter(|| {
                let offset = bb(&tz).to_offset(bb(STAMP));
                assert_eq!(offset, EXPECTED);
            })
        });
    }
}

/// Measures how long it takes to map a civil datetime to a possibly ambiguous
/// timestamp using a TZif time zone's *historical* data. That is, we pick a
/// time zone and a timestamp old enough that it won't hit the POSIX time zone
/// case.
fn tzif_historical_datetime_to_offset(c: &mut Criterion) {
    const NAME: &str = "tz/tzif_historical_datetime_to_offset";
    const DATETIME: civil::DateTime = civil::date(2000, 7, 1).at(17, 0, 0, 0);
    const TZ: &str = "America/New_York";
    const EXPECTED_OFFSET: Offset = Offset::constant(-4);
    const EXPECTED: AmbiguousOffset =
        AmbiguousOffset::Unambiguous { offset: EXPECTED_OFFSET };

    let tz = TimeZone::get(TZ).unwrap();
    {
        benchmark(c, format!("{NAME}/jiff"), |b| {
            b.iter(|| {
                let ambiguous = bb(&tz).to_ambiguous_timestamp(bb(DATETIME));
                assert_eq!(ambiguous.offset(), EXPECTED);
            })
        });
    }
}

/// Measures how long it takes to map a timestamp to an offset using a TZif
/// time zone's *historical* data. That is, we pick a time zone and a timestamp
/// old enough that it won't hit the POSIX time zone case.
fn tzif_historical_timestamp_to_offset(c: &mut Criterion) {
    const NAME: &str = "tz/tzif_historical_timestamp_to_offset";
    const STAMP: Timestamp = Timestamp::constant(962409600, 0);
    const TZ: &str = "America/New_York";
    const EXPECTED: Offset = Offset::constant(-4);

    let tz = TimeZone::get(TZ).unwrap();
    {
        benchmark(c, format!("{NAME}/jiff"), |b| {
            b.iter(|| {
                let offset = bb(&tz).to_offset(bb(STAMP));
                assert_eq!(offset, EXPECTED);
            })
        });
    }
}
