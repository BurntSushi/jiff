use std::hint::black_box as bb;

use criterion::Criterion;

use jiff::{civil, ToSpan};

use crate::{benchmark, convert::ConvertFrom};

pub(super) fn define(c: &mut Criterion) {
    add_days(c);
    add_years_months_days(c);
    day_of_year_get(c);
    days_in_month(c);
    difference_days(c);
    tomorrow(c);
    yesterday(c);
}

/// Measures the time to add a number of days to a civil date.
fn add_days(c: &mut Criterion) {
    const NAME: &str = "date/add_days";

    fn benchmark_with(
        c: &mut Criterion,
        label: &str,
        date: civil::Date,
        days: i32,
        expected: civil::Date,
    ) {
        {
            let span = jiff::Span::new().days(days);
            benchmark(c, format!("{NAME}/{label}/span/jiff"), |b| {
                b.iter(|| {
                    let got = bb(date) + bb(span);
                    assert_eq!(got, expected);
                })
            });
        }

        {
            let dur = jiff::SignedDuration::from_hours(24 * i64::from(days));
            benchmark(c, format!("{NAME}/{label}/duration/jiff"), |b| {
                b.iter(|| {
                    let got = bb(date) + bb(dur);
                    assert_eq!(got, expected);
                })
            });
        }

        {
            let expected = chrono::NaiveDate::convert_from(expected);
            let date = chrono::NaiveDate::convert_from(date);
            let dur = chrono::TimeDelta::days(days.into());
            benchmark(c, format!("{NAME}/{label}/duration/chrono"), |b| {
                b.iter(|| {
                    let got = bb(date) + bb(dur);
                    assert_eq!(got, expected);
                })
            });
        }

        {
            let expected = time::Date::convert_from(expected);
            let date = time::Date::convert_from(date);
            let dur = time::Duration::days(days.into());
            benchmark(c, format!("{NAME}/{label}/duration/time"), |b| {
                b.iter(|| {
                    let got = bb(date) + bb(dur);
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
/// a `civil::Date`.
fn add_years_months_days(c: &mut Criterion) {
    const NAME: &str = "date/add_years_months_days";
    const START: civil::Date = civil::date(2006, 8, 13);
    const EXPECTED: civil::Date = civil::date(2013, 4, 24);

    {
        let span = 6.years().months(8).days(11);
        benchmark(c, format!("{NAME}/jiff"), |b| {
            b.iter(|| {
                let got = bb(START) + bb(span);
                assert_eq!(got, EXPECTED);
            })
        });
    }
}

/// Measures the timing for `civil::Date::day_of_year`.
fn day_of_year_get(c: &mut Criterion) {
    const NAME: &str = "date/day_of_year/get";

    let date = civil::date(2024, 6, 30);
    benchmark(c, format!("{NAME}/leap/jiff"), |b| {
        b.iter(|| {
            assert_eq!(bb(date).day_of_year(), 182);
        })
    });

    let date = civil::date(2023, 6, 30);
    benchmark(c, format!("{NAME}/noleap/jiff"), |b| {
        b.iter(|| {
            assert_eq!(bb(date).day_of_year(), 181);
        })
    });
}

/// Measures the timing for `civil::Date::day_of_year`.
fn days_in_month(c: &mut Criterion) {
    const NAME: &str = "date/days_in_month";

    let date = civil::date(2024, 6, 30);
    {
        benchmark(c, format!("{NAME}/leap/nofeb/jiff"), |b| {
            b.iter(|| {
                assert_eq!(bb(date).days_in_month(), 30);
            })
        });
    }
    {
        let date = time::Date::convert_from(date);
        benchmark(c, format!("{NAME}/leap/nofeb/time"), |b| {
            b.iter(|| {
                assert_eq!(bb(date).month().length(bb(date).year()), 30);
            })
        });
    }

    let date = civil::date(2024, 2, 15);
    {
        benchmark(c, format!("{NAME}/leap/feb/jiff"), |b| {
            b.iter(|| {
                assert_eq!(bb(date).days_in_month(), 29);
            })
        });
    }
    {
        let date = time::Date::convert_from(date);
        benchmark(c, format!("{NAME}/leap/feb/time"), |b| {
            b.iter(|| {
                assert_eq!(bb(date).month().length(bb(date).year()), 29);
            })
        });
    }

    let date = civil::date(2023, 6, 30);
    {
        benchmark(c, format!("{NAME}/noleap/nofeb/jiff"), |b| {
            b.iter(|| {
                assert_eq!(bb(date).days_in_month(), 30);
            })
        });
    }
    {
        let date = time::Date::convert_from(date);
        benchmark(c, format!("{NAME}/noleap/nofeb/time"), |b| {
            b.iter(|| {
                assert_eq!(bb(date).month().length(bb(date).year()), 30);
            })
        });
    }

    let date = civil::date(2023, 2, 15);
    {
        benchmark(c, format!("{NAME}/noleap/feb/jiff"), |b| {
            b.iter(|| {
                assert_eq!(bb(date).days_in_month(), 28);
            })
        });
    }
    {
        let date = time::Date::convert_from(date);
        benchmark(c, format!("{NAME}/noleap/feb/time"), |b| {
            b.iter(|| {
                assert_eq!(bb(date).month().length(bb(date).year()), 28);
            })
        });
    }
}

/// Measures how long it takes to compute the number of days between two civil
/// dates.
fn difference_days(c: &mut Criterion) {
    const NAME: &str = "date/difference_days";
    const DATE1: civil::Date = civil::date(1997, 1, 1);
    const DATE2: civil::Date = civil::date(2025, 2, 12);
    const EXPECTED: i32 = 10_269;

    {
        benchmark(c, format!("{NAME}/span/jiff"), |b| {
            b.iter(|| {
                let got = (bb(DATE2) - bb(DATE1)).get_days();
                assert_eq!(got, EXPECTED);
            })
        });
    }

    {
        let expected = i64::from(EXPECTED);
        benchmark(c, format!("{NAME}/duration/jiff"), |b| {
            b.iter(|| {
                let got = bb(DATE2).duration_since(bb(DATE1)).as_hours() / 24;
                assert_eq!(got, expected);
            })
        });
    }

    {
        let date1 = chrono::NaiveDate::convert_from(DATE1);
        let date2 = chrono::NaiveDate::convert_from(DATE2);
        let expected = i64::from(EXPECTED);
        benchmark(c, format!("{NAME}/duration/chrono"), |b| {
            b.iter(|| {
                let got = (bb(date2) - bb(date1)).num_days();
                assert_eq!(got, expected);
            })
        });
    }

    {
        let date1 = time::Date::convert_from(DATE1);
        let date2 = time::Date::convert_from(DATE2);
        let expected = i64::from(EXPECTED);
        benchmark(c, format!("{NAME}/duration/time"), |b| {
            b.iter(|| {
                let got = (bb(date2) - bb(date1)).whole_days();
                assert_eq!(got, expected);
            })
        });
    }
}

/// Measures the timing for finding the day after a date.
///
/// Jiff was initially quite slow here, but has mostly caught up. Measurements
/// still report it as 3-4x slower than `time` here, but profiling suggests
/// that a big chunk of time is being spent just in equality checks. I tried
/// futzing with this a bit (including trying to make `Date::eq` faster), but
/// didn't get far. If I remove the assertion entirely, than Jiff's
/// measurement gets a little less than twice as fast.
///
/// So perhaps this benchmark isn't great?
fn tomorrow(c: &mut Criterion) {
    const NAME: &str = "date/tomorrow";

    let date = civil::date(2024, 6, 15);
    let expected = civil::date(2024, 6, 16);
    {
        benchmark(c, format!("{NAME}/same-month/jiff"), |b| {
            b.iter(|| {
                assert_eq!(bb(date).tomorrow().unwrap(), expected);
            })
        });
    }
    {
        let date = chrono::NaiveDate::convert_from(date);
        let expected = chrono::NaiveDate::convert_from(expected);
        benchmark(c, format!("{NAME}/same-month/chrono"), |b| {
            b.iter(|| {
                assert_eq!(bb(date).succ_opt().unwrap(), expected);
            })
        });
    }
    {
        let date = time::Date::convert_from(date);
        let expected = time::Date::convert_from(expected);
        benchmark(c, format!("{NAME}/same-month/time"), |b| {
            b.iter(|| {
                assert_eq!(bb(date).next_day().unwrap(), expected);
            })
        });
    }

    let date = civil::date(2024, 6, 30);
    let expected = civil::date(2024, 7, 1);
    {
        benchmark(c, format!("{NAME}/diff-month/jiff"), |b| {
            b.iter(|| {
                assert_eq!(bb(date).tomorrow().unwrap(), expected);
            })
        });
    }
    {
        let date = chrono::NaiveDate::convert_from(date);
        let expected = chrono::NaiveDate::convert_from(expected);
        benchmark(c, format!("{NAME}/diff-month/chrono"), |b| {
            b.iter(|| {
                assert_eq!(bb(date).succ_opt().unwrap(), expected);
            })
        });
    }
    {
        let date = time::Date::convert_from(date);
        let expected = time::Date::convert_from(expected);
        benchmark(c, format!("{NAME}/diff-month/time"), |b| {
            b.iter(|| {
                assert_eq!(bb(date).next_day().unwrap(), expected);
            })
        });
    }

    let date = civil::date(2024, 12, 31);
    let expected = civil::date(2025, 1, 1);
    {
        benchmark(c, format!("{NAME}/diff-year/jiff"), |b| {
            b.iter(|| {
                assert_eq!(bb(date).tomorrow().unwrap(), expected);
            })
        });
    }
    {
        let date = chrono::NaiveDate::convert_from(date);
        let expected = chrono::NaiveDate::convert_from(expected);
        benchmark(c, format!("{NAME}/diff-year/chrono"), |b| {
            b.iter(|| {
                assert_eq!(bb(date).succ_opt().unwrap(), expected);
            })
        });
    }
    {
        let date = time::Date::convert_from(date);
        let expected = time::Date::convert_from(expected);
        benchmark(c, format!("{NAME}/diff-year/time"), |b| {
            b.iter(|| {
                assert_eq!(bb(date).next_day().unwrap(), expected);
            })
        });
    }
}

/// Measures the timing for finding the day before a date.
///
/// See comments above on `tomorrow` which are likely also relevant here.
fn yesterday(c: &mut Criterion) {
    const NAME: &str = "date/yesterday";

    let date = civil::date(2024, 6, 15);
    let expected = civil::date(2024, 6, 14);
    {
        benchmark(c, format!("{NAME}/same-month/jiff"), |b| {
            b.iter(|| {
                assert_eq!(bb(date).yesterday().unwrap(), expected);
            })
        });
    }
    {
        let date = chrono::NaiveDate::convert_from(date);
        let expected = chrono::NaiveDate::convert_from(expected);
        benchmark(c, format!("{NAME}/same-month/chrono"), |b| {
            b.iter(|| {
                assert_eq!(bb(date).pred_opt().unwrap(), expected);
            })
        });
    }
    {
        let date = time::Date::convert_from(date);
        let expected = time::Date::convert_from(expected);
        benchmark(c, format!("{NAME}/same-month/time"), |b| {
            b.iter(|| {
                assert_eq!(bb(date).previous_day().unwrap(), expected);
            })
        });
    }

    let date = civil::date(2024, 6, 1);
    let expected = civil::date(2024, 5, 31);
    {
        benchmark(c, format!("{NAME}/diff-month/jiff"), |b| {
            b.iter(|| {
                assert_eq!(bb(date).yesterday().unwrap(), expected);
            })
        });
    }
    {
        let date = chrono::NaiveDate::convert_from(date);
        let expected = chrono::NaiveDate::convert_from(expected);
        benchmark(c, format!("{NAME}/diff-month/chrono"), |b| {
            b.iter(|| {
                assert_eq!(bb(date).pred_opt().unwrap(), expected);
            })
        });
    }
    {
        let date = time::Date::convert_from(date);
        let expected = time::Date::convert_from(expected);
        benchmark(c, format!("{NAME}/diff-month/time"), |b| {
            b.iter(|| {
                assert_eq!(bb(date).previous_day().unwrap(), expected);
            })
        });
    }

    let date = civil::date(2024, 1, 1);
    let expected = civil::date(2023, 12, 31);
    {
        benchmark(c, format!("{NAME}/diff-year/jiff"), |b| {
            b.iter(|| {
                assert_eq!(bb(date).yesterday().unwrap(), expected);
            })
        });
    }
    {
        let date = chrono::NaiveDate::convert_from(date);
        let expected = chrono::NaiveDate::convert_from(expected);
        benchmark(c, format!("{NAME}/diff-year/chrono"), |b| {
            b.iter(|| {
                assert_eq!(bb(date).pred_opt().unwrap(), expected);
            })
        });
    }
    {
        let date = time::Date::convert_from(date);
        let expected = time::Date::convert_from(expected);
        benchmark(c, format!("{NAME}/diff-year/time"), |b| {
            b.iter(|| {
                assert_eq!(bb(date).previous_day().unwrap(), expected);
            })
        });
    }
}
