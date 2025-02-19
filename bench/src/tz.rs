use std::hint::black_box as bb;

use criterion::Criterion;
use jiff::{
    civil,
    tz::{Offset, TimeZone},
    Timestamp,
};

use crate::benchmark;

pub(super) fn define(c: &mut Criterion) {
    posix_to_offset(c);
    posix_to_timestamp(c);
}

/// Measures how long it takes to map a timestamp to an offset using a POSIX
/// time zone.
fn posix_to_offset(c: &mut Criterion) {
    const NAME: &str = "tz/posix_to_offset";
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
/// timestamp using a POSIX time zone.
fn posix_to_timestamp(c: &mut Criterion) {
    const NAME: &str = "tz/posix_to_timestamp";
    const DATETIME: civil::DateTime = civil::date(2024, 6, 30).at(9, 46, 0, 0);
    const TZ: &str = "EST5EDT,M3.2.0,M11.1.0";
    const EXPECTED: Timestamp = Timestamp::constant(1719755160, 0);

    let tz = TimeZone::posix(TZ).unwrap();
    {
        benchmark(c, format!("{NAME}/jiff"), |b| {
            b.iter(|| {
                let ambiguous = bb(&tz).to_ambiguous_timestamp(bb(DATETIME));
                let ts = ambiguous.unambiguous().unwrap();
                assert_eq!(ts, EXPECTED);
            })
        });
    }
}
