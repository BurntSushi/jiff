use std::hint::black_box as bb;

use criterion::Criterion;

use jiff::{civil, ToSpan};

use crate::{benchmark, convert::ConvertFrom};

pub(super) fn define(c: &mut Criterion) {
    add_days(c);
    add_years_months_days(c);
    to_timestamp_static(c);
    to_timestamp_tzdb_lookup(c);
}

/// Measures the time to add a number of days to a civil datetime.
fn add_days(c: &mut Criterion) {
    const NAME: &str = "civil_datetime/add_days";

    fn benchmark_with(
        c: &mut Criterion,
        label: &str,
        date: civil::Date,
        days: i32,
        expected: civil::Date,
    ) {
        let dt = date.at(17, 59, 30, 0);
        let expected = expected.at(17, 59, 30, 0);

        {
            let span = jiff::Span::new().days(days);
            benchmark(c, format!("{NAME}/{label}/span/jiff"), |b| {
                b.iter(|| {
                    let got = bb(dt) + bb(span);
                    assert_eq!(got, expected);
                })
            });
        }

        {
            let dur = jiff::SignedDuration::from_hours(24 * i64::from(days));
            benchmark(c, format!("{NAME}/{label}/duration/jiff"), |b| {
                b.iter(|| {
                    let got = bb(dt) + bb(dur);
                    assert_eq!(got, expected);
                })
            });
        }

        {
            let dt = chrono::NaiveDateTime::convert_from(dt);
            let expected = chrono::NaiveDateTime::convert_from(expected);
            let dur = chrono::TimeDelta::days(days.into());
            benchmark(c, format!("{NAME}/{label}/duration/chrono"), |b| {
                b.iter(|| {
                    let got = bb(dt) + bb(dur);
                    assert_eq!(got, expected);
                })
            });
        }

        {
            let dt = time::PrimitiveDateTime::convert_from(dt);
            let expected = time::PrimitiveDateTime::convert_from(expected);
            let dur = time::Duration::days(days.into());
            benchmark(c, format!("{NAME}/{label}/duration/time"), |b| {
                b.iter(|| {
                    let got = bb(dt) + bb(dur);
                    assert_eq!(got, expected);
                })
            });
        }
    }

    benchmark_with(
        c,
        "sameyear",
        civil::date(2023, 2, 12),
        270,
        civil::date(2023, 11, 9),
    );
    benchmark_with(
        c,
        "diffyear",
        civil::date(2023, 2, 12),
        1070,
        civil::date(2026, 1, 17),
    );
}

/// Measures the timing for adding a `Span` with years, months and days to
/// a `civil::DateTime`.
fn add_years_months_days(c: &mut Criterion) {
    const NAME: &str = "datetime/add_years_months_days";
    const EXPECTED: civil::DateTime =
        civil::date(2013, 4, 24).at(17, 29, 30, 0);

    let date = civil::date(2006, 8, 13).at(17, 29, 30, 0);
    let span = 6.years().months(8).days(11);
    benchmark(c, format!("{NAME}/jiff"), |b| {
        b.iter(|| {
            let got = bb(date) + bb(span);
            assert_eq!(got, EXPECTED);
        })
    });
}

/// Measures the time it takes to convert a civil datetime to a specific
/// instant, *not* including the time it takes to do a time zone lookup.
///
/// This is useful when you have a known time zone already and want to get
/// a specific instant for many distinct civil datetimes in that time zone.
fn to_timestamp_static(c: &mut Criterion) {
    const NAME: &str = "civil_datetime/to_datetime_static";
    const TZNAME: &str = "America/New_York";
    const STAMP: i64 = 1719755160;
    const DATETIME: civil::DateTime = civil::date(2024, 6, 30).at(9, 46, 0, 0);

    if let Ok(tz) = jiff::tz::TimeZone::get(TZNAME) {
        benchmark(c, format!("{NAME}/zoneinfo/jiff"), |b| {
            b.iter(|| {
                // The natural way to do this is `dt.to_zoned(..)`, but
                // Jiff doesn't actually require one to materialize a `Zoned`
                // to disambiguate a civil datetime.
                let ts = bb(&tz).to_timestamp(bb(DATETIME)).unwrap();
                assert_eq!(ts.as_second(), STAMP);
            })
        });
    }

    #[cfg(unix)]
    {
        if let Ok(tz) = tzfile::Tz::named(TZNAME) {
            let dt = chrono::NaiveDateTime::convert_from(DATETIME);
            benchmark(c, format!("{NAME}/zoneinfo/chrono"), |b| {
                use chrono::TimeZone;

                b.iter(|| {
                    let mapped = (&tz).from_local_datetime(bb(&dt));
                    let zdt = mapped.single().unwrap();
                    assert_eq!(zdt.timestamp(), STAMP);
                })
            });
        }
    }

    {
        let dt = chrono::NaiveDateTime::convert_from(DATETIME);
        benchmark(c, format!("{NAME}/bundled/chrono"), |b| {
            use chrono::TimeZone;
            use chrono_tz::America::New_York;

            b.iter(|| {
                let mapped = New_York.from_local_datetime(bb(&dt));
                let zdt = mapped.single().unwrap();
                assert_eq!(zdt.timestamp(), STAMP);
            })
        });
    }

    // The `time` crate doesn't support this.
}

/// This benchmarks the time it takes to convert a civil datetime to a specific
/// instant, *including* the time it takes to lookup a time zone in the system
/// zoneinfo database. (Lookups may be cached by the library, but that is part
/// of the benchmark model.)
///
/// This applies when, for example, parsing a large number of datetime strings
/// with a time zone in them, e.g., `2024-06-30T13:42-04[America/New_York]`.
/// Jiff is the only Rust library to support RFC 9557 time zone annotations, so
/// we don't measure the parsing here and instead just the TZ name lookup and
/// resolution to an instant.
fn to_timestamp_tzdb_lookup(c: &mut Criterion) {
    const NAME: &str = "civil_datetime/to_timestamp_tzdb_lookup";
    const TZNAME: &str = "America/New_York";
    const STAMP: i64 = 1719755160;
    const DATETIME: civil::DateTime = civil::date(2024, 6, 30).at(9, 46, 0, 0);

    {
        if jiff::tz::TimeZone::get(TZNAME).is_ok() {
            benchmark(c, format!("{NAME}/zoneinfo/jiff"), |b| {
                b.iter(|| {
                    let zdt = bb(DATETIME).in_tz(bb(TZNAME)).unwrap();
                    assert_eq!(zdt.timestamp().as_second(), STAMP)
                })
            });
        }
    }

    // `tzfile` exposes a Unix specific platform API.
    #[cfg(unix)]
    {
        if tzfile::Tz::named(TZNAME).is_ok() {
            let dt = chrono::NaiveDateTime::convert_from(DATETIME);
            benchmark(c, format!("{NAME}/zoneinfo/chrono"), |b| {
                use chrono::TimeZone;

                b.iter(|| {
                    let tz = tzfile::Tz::named(bb(TZNAME)).unwrap();
                    let mapped = (&tz).from_local_datetime(bb(&dt));
                    let zdt = mapped.single().unwrap();
                    assert_eq!(zdt.timestamp(), STAMP);
                })
            });
        }
    }

    {
        let dt = chrono::NaiveDateTime::convert_from(DATETIME);
        benchmark(c, format!("{NAME}/bundled/chrono"), |b| {
            use chrono::TimeZone;

            b.iter(|| {
                let tz: chrono_tz::Tz = "America/New_York".parse().unwrap();
                let mapped = tz.from_local_datetime(bb(&dt));
                let zdt = mapped.single().unwrap();
                assert_eq!(zdt.timestamp(), STAMP);
            })
        });
    }

    // The `time` crate doesn't support this.
}
