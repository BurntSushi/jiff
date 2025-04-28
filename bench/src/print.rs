use std::hint::black_box as bb;

use criterion::Criterion;
use jiff::civil;

use crate::{benchmark, convert::ConvertFrom};

pub(super) fn define(c: &mut Criterion) {
    print_civil_datetime(c);
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
