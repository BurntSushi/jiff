use std::hint::black_box as bb;

use criterion::Criterion;
use jiff::civil;

use crate::{benchmark, convert::ConvertFrom};

pub(super) fn define(c: &mut Criterion) {
    print_civil_datetime(c);
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
