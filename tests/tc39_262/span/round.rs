use jiff::{
    civil::date, tz::TimeZone, RoundMode, Span, SpanRelativeTo, SpanRound,
    Timestamp, ToSpan, Unit, Zoned,
};

use crate::tc39_262::Result;

const MAX_SPAN_SECONDS: i64 = 631_107_417_600;

fn mk<const N: usize>(units: [i64; N]) -> Span {
    assert!(N <= 10);
    Span::new()
        .years(units.get(0).copied().unwrap_or(0))
        .months(units.get(1).copied().unwrap_or(0))
        .weeks(units.get(2).copied().unwrap_or(0))
        .days(units.get(3).copied().unwrap_or(0))
        .hours(units.get(4).copied().unwrap_or(0))
        .minutes(units.get(5).copied().unwrap_or(0))
        .seconds(units.get(6).copied().unwrap_or(0))
        .milliseconds(units.get(7).copied().unwrap_or(0))
        .microseconds(units.get(8).copied().unwrap_or(0))
        .nanoseconds(units.get(9).copied().unwrap_or(0))
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/balance-negative-result.js
#[test]
fn balance_negative_result() -> Result {
    let span1 = -60.hours();
    let span2 = span1.round(SpanRound::new().largest(Unit::Day))?;
    assert_eq!(span2, -2.days().hours(12));
    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/balance-subseconds.js
#[test]
fn balance_subseconds() -> Result {
    let span1 =
        999.milliseconds().microseconds(999_999).nanoseconds(999_999_999);
    let span2 = span1.round(SpanRound::new().largest(Unit::Second))?;
    assert_eq!(
        span2,
        2.seconds().milliseconds(998).microseconds(998).nanoseconds(999)
    );

    let span1 =
        -999.milliseconds().microseconds(999_999).nanoseconds(999_999_999);
    let span2 = span1.round(SpanRound::new().largest(Unit::Second))?;
    assert_eq!(
        span2,
        -2.seconds().milliseconds(998).microseconds(998).nanoseconds(999)
    );

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/calendar-possibly-required.js
#[test]
fn calendar_possibly_required() -> Result {
    let d = date(2021, 12, 15);
    let relative_years = SpanRound::new().largest(Unit::Year).relative(d);
    let relative_months = SpanRound::new().largest(Unit::Month).relative(d);
    let relative_weeks = SpanRound::new().largest(Unit::Week).relative(d);
    let relative_days = SpanRound::new().largest(Unit::Day).relative(d);

    let sp = 1.year();
    insta::assert_snapshot!(
        sp.round(Unit::Hour).unwrap_err(),
        @"using largest unit (which is 'year') in given span requires that a relative reference time be given, but none was provided",
    );
    assert_eq!(sp.round(relative_years)?, 1.year());
    assert_eq!(sp.round(relative_months)?, 12.months());
    assert_eq!(sp.round(relative_weeks)?, 52.weeks().days(1));
    assert_eq!(sp.round(relative_days)?, 365.days());

    let sp = 12.months();
    insta::assert_snapshot!(
        sp.round(Unit::Hour).unwrap_err(),
        @"using largest unit (which is 'month') in given span requires that a relative reference time be given, but none was provided",
    );
    assert_eq!(sp.round(relative_years)?, 1.year());
    assert_eq!(sp.round(relative_months)?, 12.months());
    assert_eq!(sp.round(relative_weeks)?, 52.weeks().days(1));
    assert_eq!(sp.round(relative_days)?, 365.days());

    let sp = 5.weeks();
    insta::assert_snapshot!(
        sp.round(Unit::Hour).unwrap_err(),
        @"using largest unit (which is 'week') in given span requires that a relative reference time be given, but none was provided",
    );
    assert_eq!(sp.round(relative_years)?, 1.month().days(4));
    assert_eq!(sp.round(relative_months)?, 1.month().days(4));
    assert_eq!(sp.round(relative_weeks)?, 5.weeks());
    assert_eq!(sp.round(relative_days)?, 35.days());

    let sp = 42.days();
    assert_eq!(sp.round(relative_years)?, 1.month().days(11));
    assert_eq!(sp.round(relative_months)?, 1.month().days(11));
    assert_eq!(sp.round(relative_weeks)?, 6.weeks());
    assert_eq!(sp.round(relative_days)?, 42.days());
    // We don't need a relative datetime for rounding days.
    // In this case, we assume civil day (always 24 hours).
    assert_eq!(sp.round(Unit::Hour)?, 42.days());

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/dst-balancing-result.js
#[test]
fn dst_balancing_result() -> Result {
    if jiff::tz::db().is_definitively_empty() {
        return Ok(());
    }

    let sp = 1.year().hours(24);
    let zdt = "1999-10-29T01-07[America/Los_Angeles]".parse::<Zoned>()?;
    let result =
        sp.round(SpanRound::new().largest(Unit::Year).relative(&zdt))?;
    assert_eq!(result, 1.year().hours(24));

    // Added my own test here using a shorter duration since we use an
    // actual time zone for testing, where as Temporal uses a "dummy" time
    // zone with only one forward and one backward transition in the year 2000.
    // But with real TZ data, a span of 1 year will pretty much always cover
    // a DST backward transition.
    let sp = 1.month().hours(24);
    let zdt = "2000-09-29T01-07[America/Los_Angeles]".parse::<Zoned>()?;
    let result =
        sp.round(SpanRound::new().largest(Unit::Year).relative(&zdt))?;
    assert_eq!(result, 1.month().hours(24));

    // Try one month earlier, and we balance up to 1 day.
    let sp = 1.month().hours(24);
    let zdt = "2000-08-29T01-07[America/Los_Angeles]".parse::<Zoned>()?;
    let result =
        sp.round(SpanRound::new().largest(Unit::Year).relative(&zdt))?;
    assert_eq!(result, 1.month().days(1));

    let sp = 24.hours().nanoseconds(5);
    let zdt = "2000-10-29T00-07[America/Los_Angeles]".parse::<Zoned>()?;
    let result = sp.round(
        SpanRound::new()
            .largest(Unit::Day)
            .smallest(Unit::Minute)
            .mode(RoundMode::Expand)
            .increment(30)
            .relative(&zdt),
    )?;
    assert_eq!(result, 24.hours().minutes(30));

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/dst-rounding-result.js
#[test]
fn dst_rounding_result() -> Result {
    if jiff::tz::db().is_definitively_empty() {
        return Ok(());
    }

    let sp = 1.month().days(15).hours(11).minutes(30);
    let zdt = "2000-02-18T02-08[America/Los_Angeles]".parse::<Zoned>()?;
    let result =
        sp.round(SpanRound::new().smallest(Unit::Month).relative(&zdt))?;
    assert_eq!(result, 2.months());

    let sp = 1.month().days(15).minutes(30);
    let zdt = "2000-03-02T02-08[America/Los_Angeles]".parse::<Zoned>()?;
    let result =
        sp.round(SpanRound::new().smallest(Unit::Month).relative(&zdt))?;
    assert_eq!(result, 2.months());
    let result = sp.round(
        SpanRound::new()
            .smallest(Unit::Month)
            .mode(RoundMode::HalfTrunc)
            .relative(&zdt),
    )?;
    assert_eq!(result, 1.month());

    let sp = 11.hours().minutes(30);
    let zdt = "2000-04-02T00:00:00[America/Los_Angeles]".parse::<Zoned>()?;
    let result =
        sp.round(SpanRound::new().smallest(Unit::Day).relative(&zdt))?;
    assert_eq!(result, 1.day());
    let result = sp.round(
        SpanRound::new()
            .smallest(Unit::Day)
            .mode(RoundMode::HalfTrunc)
            .relative(&zdt),
    )?;
    assert_eq!(result, 0.days());

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/duration-out-of-range-added-to-relativeto.js
#[test]
fn duration_out_of_range_added_to_relative() -> Result {
    let d = date(2000, 1, 1);

    let sp = 2_000_000.days().hours(170_000_000);
    let relative = SpanRound::new().relative(d);
    insta::assert_snapshot!(
        sp.round(relative.smallest(Unit::Year)).unwrap_err(),
        @"failed to add P2000000dT170000000h to 2000-01-01T00:00:00: failed to add overflowing span, P7083333d, from adding PT170000000h to 00:00:00, to 7475-10-25: parameter 'days' with value 7083333 is not in the required range of -4371587..=2932896",
    );

    let sp = -2_000_000.days().hours(170_000_000);
    let relative = SpanRound::new().relative(d);
    insta::assert_snapshot!(
        sp.round(relative.smallest(Unit::Year)).unwrap_err(),
        @"failed to add -P2000000dT170000000h to 2000-01-01T00:00:00: failed to add overflowing span, -P7083334d, from adding -PT170000000h to 00:00:00, to -003476-03-09: parameter 'days' with value -7083334 is not in the required range of -4371587..=2932896",
    );

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/february-leap-year.js
#[test]
fn february_leap_year() -> Result {
    let d = date(1972, 3, 1);
    let options = SpanRound::new().largest(Unit::Year).relative(d);

    let sp = 3.years().months(11).days(27);
    let result = sp.round(options)?;
    assert_eq!(result, 3.years().months(11).days(27));

    let sp = 3.years().months(11).days(28);
    let result = sp.round(options)?;
    assert_eq!(result, 3.years().months(11).days(28));

    let sp = 3.years().months(11).days(29);
    let result = sp.round(options)?;
    assert_eq!(result, 4.years());

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/largestunit-correct-rebalancing.js
#[test]
fn largestunit_correct_rebalancing() -> Result {
    let days: i64 = 100;
    let d = date(2023, 2, 21);
    let options = SpanRound::new().largest(Unit::Month).relative(d);

    let sp = Span::new().days(days);
    assert_eq!(sp.round(options)?, 3.months().days(11));

    let sp = Span::new().hours(days * 24);
    assert_eq!(sp.round(options)?, 3.months().days(11));

    let sp = Span::new().minutes(days * 24 * 60);
    assert_eq!(sp.round(options)?, 3.months().days(11));

    let sp = Span::new().seconds(days * 24 * 60 * 60);
    assert_eq!(sp.round(options)?, 3.months().days(11));

    let sp = Span::new().milliseconds(days * 24 * 60 * 60 * 1_000);
    assert_eq!(sp.round(options)?, 3.months().days(11));

    let sp = Span::new().microseconds(days * 24 * 60 * 60 * 1_000_000);
    assert_eq!(sp.round(options)?, 3.months().days(11));

    let sp = Span::new().nanoseconds(days * 24 * 60 * 60 * 1_000_000_000);
    assert_eq!(sp.round(options)?, 3.months().days(11));

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/largestunit-smallestunit-combinations-relativeto.js
#[test]
fn largestunit_smallestunit_combinations_relative() -> Result {
    let sp = mk([5, 5, 5, 5, 5, 5, 5, 5, 5, 5]);
    let d = date(2000, 1, 1);
    let zdt = date(1972, 1, 1).intz("UTC")?;
    let exact: &[(Unit, &[(Unit, Span)])] = &[
        (
            Unit::Year,
            &[
                (Unit::Year, mk([6])),
                (Unit::Month, mk([5, 6])),
                (Unit::Week, mk([5, 6, 1])),
                (Unit::Day, mk([5, 6, 0, 10])),
                (Unit::Hour, mk([5, 6, 0, 10, 5])),
                (Unit::Minute, mk([5, 6, 0, 10, 5, 5])),
                (Unit::Second, mk([5, 6, 0, 10, 5, 5, 5])),
                (Unit::Millisecond, mk([5, 6, 0, 10, 5, 5, 5, 5])),
                (Unit::Microsecond, mk([5, 6, 0, 10, 5, 5, 5, 5, 5])),
                (Unit::Nanosecond, mk([5, 6, 0, 10, 5, 5, 5, 5, 5, 5])),
            ],
        ),
        (
            Unit::Month,
            &[
                (Unit::Month, mk([0, 66])),
                (Unit::Week, mk([0, 66, 1])),
                (Unit::Day, mk([0, 66, 0, 10])),
                (Unit::Hour, mk([0, 66, 0, 10, 5])),
                (Unit::Minute, mk([0, 66, 0, 10, 5, 5])),
                (Unit::Second, mk([0, 66, 0, 10, 5, 5, 5])),
                (Unit::Millisecond, mk([0, 66, 0, 10, 5, 5, 5, 5])),
                (Unit::Microsecond, mk([0, 66, 0, 10, 5, 5, 5, 5, 5])),
                (Unit::Nanosecond, mk([0, 66, 0, 10, 5, 5, 5, 5, 5, 5])),
            ],
        ),
        (
            Unit::Week,
            &[
                (Unit::Week, mk([0, 0, 288])),
                (Unit::Day, mk([0, 0, 288, 2])),
                (Unit::Hour, mk([0, 0, 288, 2, 5])),
                (Unit::Minute, mk([0, 0, 288, 2, 5, 5])),
                (Unit::Second, mk([0, 0, 288, 2, 5, 5, 5])),
                (Unit::Millisecond, mk([0, 0, 288, 2, 5, 5, 5, 5])),
                (Unit::Microsecond, mk([0, 0, 288, 2, 5, 5, 5, 5, 5])),
                (Unit::Nanosecond, mk([0, 0, 288, 2, 5, 5, 5, 5, 5, 5])),
            ],
        ),
        (
            Unit::Day,
            &[
                (Unit::Day, mk([0, 0, 0, 2018])),
                (Unit::Hour, mk([0, 0, 0, 2018, 5])),
                (Unit::Minute, mk([0, 0, 0, 2018, 5, 5])),
                (Unit::Second, mk([0, 0, 0, 2018, 5, 5, 5])),
                (Unit::Millisecond, mk([0, 0, 0, 2018, 5, 5, 5, 5])),
                (Unit::Microsecond, mk([0, 0, 0, 2018, 5, 5, 5, 5, 5])),
                (Unit::Nanosecond, mk([0, 0, 0, 2018, 5, 5, 5, 5, 5, 5])),
            ],
        ),
        (
            Unit::Hour,
            &[
                (Unit::Hour, mk([0, 0, 0, 0, 48_437])),
                (Unit::Minute, mk([0, 0, 0, 0, 48_437, 5])),
                (Unit::Second, mk([0, 0, 0, 0, 48_437, 5, 5])),
                (Unit::Millisecond, mk([0, 0, 0, 0, 48_437, 5, 5, 5])),
                (Unit::Microsecond, mk([0, 0, 0, 0, 48_437, 5, 5, 5, 5])),
                (Unit::Nanosecond, mk([0, 0, 0, 0, 48_437, 5, 5, 5, 5, 5])),
            ],
        ),
        (
            Unit::Minute,
            &[
                (Unit::Minute, mk([0, 0, 0, 0, 0, 2_906_225])),
                (Unit::Second, mk([0, 0, 0, 0, 0, 2_906_225, 5])),
                (Unit::Millisecond, mk([0, 0, 0, 0, 0, 2_906_225, 5, 5])),
                (Unit::Microsecond, mk([0, 0, 0, 0, 0, 2_906_225, 5, 5, 5])),
                (Unit::Nanosecond, mk([0, 0, 0, 0, 0, 2_906_225, 5, 5, 5, 5])),
            ],
        ),
        (
            Unit::Second,
            &[
                (Unit::Second, mk([0, 0, 0, 0, 0, 0, 174_373_505])),
                (Unit::Millisecond, mk([0, 0, 0, 0, 0, 0, 174_373_505, 5])),
                (Unit::Microsecond, mk([0, 0, 0, 0, 0, 0, 174_373_505, 5, 5])),
                (
                    Unit::Nanosecond,
                    mk([0, 0, 0, 0, 0, 0, 174_373_505, 5, 5, 5]),
                ),
            ],
        ),
        (
            Unit::Millisecond,
            &[
                (Unit::Millisecond, mk([0, 0, 0, 0, 0, 0, 0, 174373505005])),
                (
                    Unit::Microsecond,
                    mk([0, 0, 0, 0, 0, 0, 0, 174373505005, 5]),
                ),
                (
                    Unit::Nanosecond,
                    mk([0, 0, 0, 0, 0, 0, 0, 174373505005, 5, 5]),
                ),
            ],
        ),
        (
            Unit::Microsecond,
            &[
                (
                    Unit::Microsecond,
                    mk([0, 0, 0, 0, 0, 0, 0, 0, 174373505005005]),
                ),
                (
                    Unit::Nanosecond,
                    mk([0, 0, 0, 0, 0, 0, 0, 0, 174373505005005, 5]),
                ),
            ],
        ),
        (
            Unit::Nanosecond,
            &[(
                Unit::Nanosecond,
                mk([0, 0, 0, 0, 0, 0, 0, 0, 0, 174373505005005005]),
            )],
        ),
    ];

    for &(largest, entry) in exact.iter() {
        for &(smallest, expected) in entry.iter() {
            let dates = [SpanRelativeTo::from(d), SpanRelativeTo::from(&zdt)];
            for relative in dates {
                let result = sp.round(
                    SpanRound::new()
                        .largest(largest)
                        .smallest(smallest)
                        .relative(relative),
                )?;
                assert_eq!(
                    result, expected,
                    "largest unit {largest:?}, \
                     smallest unit {smallest:?}, \
                     and relative to {relative:?}",
                );
            }
        }
    }

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/largestunit-smallestunit-combinations.js
#[test]
fn largestunit_smallestunit_combinations() -> Result {
    let sp = mk([0, 0, 0, 5, 5, 5, 5, 5, 5, 5]);
    let exact: &[(Unit, &[(Unit, Span)])] = &[
        (
            Unit::Day,
            &[
                (Unit::Day, mk([0, 0, 0, 5])),
                (Unit::Hour, mk([0, 0, 0, 5, 5])),
                (Unit::Minute, mk([0, 0, 0, 5, 5, 5])),
                (Unit::Second, mk([0, 0, 0, 5, 5, 5, 5])),
                (Unit::Millisecond, mk([0, 0, 0, 5, 5, 5, 5, 5])),
                (Unit::Microsecond, mk([0, 0, 0, 5, 5, 5, 5, 5, 5])),
                (Unit::Nanosecond, mk([0, 0, 0, 5, 5, 5, 5, 5, 5, 5])),
            ],
        ),
        (
            Unit::Hour,
            &[
                (Unit::Hour, mk([0, 0, 0, 0, 125])),
                (Unit::Minute, mk([0, 0, 0, 0, 125, 5])),
                (Unit::Second, mk([0, 0, 0, 0, 125, 5, 5])),
                (Unit::Millisecond, mk([0, 0, 0, 0, 125, 5, 5, 5])),
                (Unit::Microsecond, mk([0, 0, 0, 0, 125, 5, 5, 5, 5])),
                (Unit::Nanosecond, mk([0, 0, 0, 0, 125, 5, 5, 5, 5, 5])),
            ],
        ),
        (
            Unit::Minute,
            &[
                (Unit::Minute, mk([0, 0, 0, 0, 0, 7_505])),
                (Unit::Second, mk([0, 0, 0, 0, 0, 7_505, 5])),
                (Unit::Millisecond, mk([0, 0, 0, 0, 0, 7_505, 5, 5])),
                (Unit::Microsecond, mk([0, 0, 0, 0, 0, 7_505, 5, 5, 5])),
                (Unit::Nanosecond, mk([0, 0, 0, 0, 0, 7_505, 5, 5, 5, 5])),
            ],
        ),
        (
            Unit::Second,
            &[
                (Unit::Second, mk([0, 0, 0, 0, 0, 0, 450_305])),
                (Unit::Millisecond, mk([0, 0, 0, 0, 0, 0, 450_305, 5])),
                (Unit::Microsecond, mk([0, 0, 0, 0, 0, 0, 450_305, 5, 5])),
                (Unit::Nanosecond, mk([0, 0, 0, 0, 0, 0, 450_305, 5, 5, 5])),
            ],
        ),
        (
            Unit::Millisecond,
            &[
                (Unit::Millisecond, mk([0, 0, 0, 0, 0, 0, 0, 450305005])),
                (Unit::Microsecond, mk([0, 0, 0, 0, 0, 0, 0, 450305005, 5])),
                (Unit::Nanosecond, mk([0, 0, 0, 0, 0, 0, 0, 450305005, 5, 5])),
            ],
        ),
        (
            Unit::Microsecond,
            &[
                (
                    Unit::Microsecond,
                    mk([0, 0, 0, 0, 0, 0, 0, 0, 450305005005]),
                ),
                (
                    Unit::Nanosecond,
                    mk([0, 0, 0, 0, 0, 0, 0, 0, 450305005005, 5]),
                ),
            ],
        ),
        (
            Unit::Nanosecond,
            &[(
                Unit::Nanosecond,
                mk([0, 0, 0, 0, 0, 0, 0, 0, 0, 450305005005005]),
            )],
        ),
    ];

    for &(largest, entry) in exact.iter() {
        for &(smallest, expected) in entry.iter() {
            let result = sp
                .round(SpanRound::new().largest(largest).smallest(smallest))?;
            assert_eq!(
                result, expected,
                "largest unit {largest:?}, smallest unit {smallest:?}",
            );
        }
    }

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/largestunit-smallestunit-default.js
#[test]
fn largestunit_smallestunit_default() -> Result {
    let d = date(2020, 1, 1);

    let almost_year = 364.days();
    let options = SpanRound::new().smallest(Unit::Year).relative(d);
    assert_eq!(almost_year.round(options)?, 1.year());

    let almost_month = 27.days();
    let options = SpanRound::new().smallest(Unit::Month).relative(d);
    assert_eq!(almost_month.round(options)?, 1.month());

    let almost_week = 6.days();
    let options = SpanRound::new().smallest(Unit::Week).relative(d);
    assert_eq!(almost_week.round(options)?, 1.week());

    let almost_day = 86_399.seconds();
    assert_eq!(almost_day.round(Unit::Day)?, 1.day());

    let almost_hour = 3599.seconds();
    assert_eq!(almost_hour.round(Unit::Hour)?, 1.hour());

    let almost_minute = 59.seconds();
    assert_eq!(almost_minute.round(Unit::Minute)?, 1.minute());

    let almost_second = 999_999_999.nanoseconds();
    assert_eq!(almost_second.round(Unit::Second)?, 1.second());

    let almost_millisecond = 999_999.nanoseconds();
    assert_eq!(almost_millisecond.round(Unit::Millisecond)?, 1.millisecond());

    let almost_microsecond = 999.nanoseconds();
    assert_eq!(almost_microsecond.round(Unit::Microsecond)?, 1.microsecond());

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/largestunit-smallestunit-mismatch.js
#[test]
fn largestunit_smallestunit_mismatch() -> Result {
    let sp = mk([5, 5, 5, 5, 5, 5, 5, 5, 5, 5]);
    let options = SpanRound::new().relative(date(2020, 1, 1));
    let units = [
        Unit::Year,
        Unit::Month,
        Unit::Week,
        Unit::Day,
        Unit::Hour,
        Unit::Minute,
        Unit::Second,
        Unit::Millisecond,
        Unit::Microsecond,
        Unit::Nanosecond,
    ];
    for largest in 1..units.len() {
        for smallest in 0..largest {
            let (largest, smallest) = (units[largest], units[smallest]);
            let options = options.largest(largest).smallest(smallest);
            assert!(sp.round(options).is_err());
        }
    }

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/largestunit-undefined.js
#[test]
fn largestunit_undefined() -> Result {
    let sp = "PT1h120m1.123456789s".parse::<Span>()?;
    let result = sp.round(Unit::Nanosecond)?;
    assert_eq!(result, "PT3h1.123456789s".parse()?);

    let sp = "PT120m1.123456789s".parse::<Span>()?;
    let result = sp.round(Unit::Nanosecond)?;
    assert_eq!(result, "PT120m1.123456789s".parse()?);

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/out-of-range-when-adjusting-rounded-days.js
#[test]
fn out_of_range_when_adjusting_rounded_days() -> Result {
    let sp =
        1.days().seconds(MAX_SPAN_SECONDS - 86_400).nanoseconds(999_999_999);
    let zdt = Timestamp::UNIX_EPOCH.to_zoned(TimeZone::UTC);

    let options =
        SpanRound::new().largest(Unit::Nanosecond).increment(2).relative(&zdt);
    insta::assert_snapshot!(
        sp.round(options).unwrap_err(),
        // Kind of a brutal error message...
        @"failed to add P1dT631107331200.999999999s to 1970-01-01T00:00:00+00:00[UTC]: failed to add span PT631107331200.999999999s to timestamp 1970-01-02T00:00:00Z (which was created from 1970-01-02T00:00:00): adding PT631107331200.999999999s to 1970-01-02T00:00:00Z overflowed: parameter 'span' with value 631107331200999999999 is not in the required range of -377705023201000000000..=253402207200999999999",
    );

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/out-of-range-when-converting-from-normalized-duration.js
#[test]
fn out_of_range_when_converting_from_normalized_duration() -> Result {
    let sp = MAX_SPAN_SECONDS.seconds().nanoseconds(999_999_999);

    let options = SpanRound::new().largest(Unit::Nanosecond).increment(1);
    insta::assert_snapshot!(
        sp.round(options).unwrap_err(),
        // Kind of a brutal error message...
        @"failed to convert rounded nanoseconds 631107417600999999999 to span for largest unit as nanoseconds: parameter 'nanoseconds' with value 631107417600999999999 is not in the required range of -9223372036854775807..=9223372036854775807",
    );

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/precision-exact-in-round-duration.js
#[test]
fn precision_exact_in_round_duration() -> Result {
    let sp = 100_000.hours().nanoseconds(5);
    let result =
        sp.round(SpanRound::new().smallest(Unit::Hour).mode(RoundMode::Ceil))?;
    assert_eq!(result, 100_001.hours());

    let sp = 1_000.days().nanoseconds(5);
    let result =
        sp.round(SpanRound::new().smallest(Unit::Day).mode(RoundMode::Ceil))?;
    assert_eq!(result, 1001.days());

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/relativeto-undefined-throw-on-calendar-units.js
#[test]
fn relativeto_undefined_throw_on_calendar_units() -> Result {
    assert_eq!(1.day().round(SpanRound::new().largest(Unit::Day))?, 1.day());
    insta::assert_snapshot!(
        1.week().round(SpanRound::new().largest(Unit::Day)).unwrap_err(),
        @"using largest unit (which is 'week') in given span requires that a relative reference time be given, but none was provided",
    );
    insta::assert_snapshot!(
        1.month().round(SpanRound::new().largest(Unit::Day)).unwrap_err(),
        @"using largest unit (which is 'month') in given span requires that a relative reference time be given, but none was provided",
    );
    insta::assert_snapshot!(
        1.year().round(SpanRound::new().largest(Unit::Day)).unwrap_err(),
        @"using largest unit (which is 'year') in given span requires that a relative reference time be given, but none was provided",
    );

    insta::assert_snapshot!(
        1.day().round(SpanRound::new().largest(Unit::Week)).unwrap_err(),
        @"using unit 'week' in round option 'largest' requires that a relative reference time be given, but none was provided",
    );
    insta::assert_snapshot!(
        1.day().round(SpanRound::new().largest(Unit::Month)).unwrap_err(),
        @"using unit 'month' in round option 'largest' requires that a relative reference time be given, but none was provided",
    );
    insta::assert_snapshot!(
        1.day().round(SpanRound::new().largest(Unit::Year)).unwrap_err(),
        @"using unit 'year' in round option 'largest' requires that a relative reference time be given, but none was provided",
    );

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/relativeto-zoneddatetime-negative-epochnanoseconds.js
#[test]
fn relativeto_zoneddatetime_negative_epochnanoseconds() -> Result {
    let zdt = Timestamp::from_nanosecond(-13849764_999_999_999)?
        .to_zoned(TimeZone::UTC);
    let sp = 1.day();
    let result =
        sp.round(SpanRound::new().largest(Unit::Day).relative(&zdt))?;
    assert_eq!(result, 1.day());
    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/result-out-of-range.js
#[test]
fn result_out_of_range() -> Result {
    let sp = MAX_SPAN_SECONDS.seconds().nanoseconds(999_999_999);
    insta::assert_snapshot!(
        sp.round(Unit::Second).unwrap_err(),
        @"failed to convert rounded nanoseconds 631107417601000000000 to span for largest unit as seconds: parameter 'seconds' with value 631107417601 is not in the required range of -631107417600..=631107417600",
    );

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/round-cross-unit-boundary.js
#[test]
fn round_cross_unit_bondary() -> Result {
    let d = date(2022, 1, 1);
    let mode = RoundMode::Expand;

    let sp = 1.year().months(11).days(24);
    let result = sp.round(
        SpanRound::new().smallest(Unit::Month).mode(mode).relative(d),
    )?;
    assert_eq!(result, 2.years());

    let sp = -1.year().months(11).days(24);
    let result = sp.round(
        SpanRound::new().smallest(Unit::Month).mode(mode).relative(d),
    )?;
    assert_eq!(result, -2.years());

    let sp = 1.hour().minutes(59).seconds(59).milliseconds(900);
    let result = sp.round(
        SpanRound::new().smallest(Unit::Second).mode(mode).relative(d),
    )?;
    assert_eq!(result, 2.hours());

    let sp = -1.hour().minutes(59).seconds(59).milliseconds(900);
    let result = sp.round(
        SpanRound::new().smallest(Unit::Second).mode(mode).relative(d),
    )?;
    assert_eq!(result, -2.hours());

    let sp = 11.months().days(24);
    let result = sp.round(
        SpanRound::new().smallest(Unit::Month).mode(mode).relative(d),
    )?;
    assert_eq!(result, 12.months());

    let sp = -11.months().days(24);
    let result = sp.round(
        SpanRound::new().smallest(Unit::Month).mode(mode).relative(d),
    )?;
    assert_eq!(result, -12.months());

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/round-negative-result.js
#[test]
fn round_negative_result() -> Result {
    let sp = -60.hours();
    let result = sp.round(Unit::Day)?;
    assert_eq!(result, -3.days());

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/roundingincrement-non-integer.js
#[test]
fn roundingincrement_non_integer() -> Result {
    let sp = 1.day();
    let options = SpanRound::new()
        .smallest(Unit::Day)
        .mode(RoundMode::Expand)
        .relative(date(2000, 1, 1));

    let result = sp.round(options.increment(2))?;
    assert_eq!(result, 2.days());

    let result = sp.round(options.increment(1_000_000))?;
    assert_eq!(result, 1_000_000.days());

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/roundingmode-ceil.js
#[test]
fn roundingmode_ceil() -> Result {
    let options = SpanRound::new().mode(RoundMode::Ceil);
    let sp = mk([5, 6, 7, 8, 40, 30, 20, 123, 987, 500]);
    let fwd = date(2020, 4, 1);
    let bck = date(2020, 12, 1);
    let expected: &[(Unit, Span, Span)] = &[
        (Unit::Year, mk([6]), mk([-5])),
        (Unit::Month, mk([5, 8]), mk([-5, -7])),
        (Unit::Week, mk([5, 7, 4]), mk([-5, -7, -3])),
        (Unit::Hour, mk([5, 7, 0, 27, 17]), mk([-5, -7, 0, -27, -16])),
        (
            Unit::Minute,
            mk([5, 7, 0, 27, 16, 31]),
            mk([-5, -7, 0, -27, -16, -30]),
        ),
        (
            Unit::Second,
            mk([5, 7, 0, 27, 16, 30, 21]),
            mk([-5, -7, 0, -27, -16, -30, -20]),
        ),
        (
            Unit::Millisecond,
            mk([5, 7, 0, 27, 16, 30, 20, 124]),
            mk([-5, -7, 0, -27, -16, -30, -20, -123]),
        ),
        (
            Unit::Microsecond,
            mk([5, 7, 0, 27, 16, 30, 20, 123, 988]),
            mk([-5, -7, 0, -27, -16, -30, -20, -123, -987]),
        ),
        (
            Unit::Nanosecond,
            mk([5, 7, 0, 27, 16, 30, 20, 123, 987, 500]),
            mk([-5, -7, 0, -27, -16, -30, -20, -123, -987, -500]),
        ),
    ];
    for &(smallest, positive, negative) in expected {
        let options = options.smallest(smallest);
        assert_eq!(
            sp.round(options.relative(fwd))?,
            positive,
            "{sp} rounds to {positive} for smallest unit {smallest:?}",
        );
        assert_eq!(
            sp.negate().round(options.relative(bck))?,
            negative,
            "-{sp} rounds to {negative} for smallest unit {smallest:?}",
        );
    }
    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/roundingmode-expand.js
#[test]
fn roundingmode_expand() -> Result {
    let options = SpanRound::new().mode(RoundMode::Expand);
    let sp = mk([5, 6, 7, 8, 40, 30, 20, 123, 987, 500]);
    let fwd = date(2020, 4, 1);
    let bck = date(2020, 12, 1);
    let expected: &[(Unit, Span, Span)] = &[
        (Unit::Year, mk([6]), mk([-6])),
        (Unit::Month, mk([5, 8]), mk([-5, -8])),
        (Unit::Week, mk([5, 7, 4]), mk([-5, -7, -4])),
        (Unit::Day, mk([5, 7, 0, 28]), mk([-5, -7, 0, -28])),
        (Unit::Hour, mk([5, 7, 0, 27, 17]), mk([-5, -7, 0, -27, -17])),
        (
            Unit::Minute,
            mk([5, 7, 0, 27, 16, 31]),
            mk([-5, -7, 0, -27, -16, -31]),
        ),
        (
            Unit::Second,
            mk([5, 7, 0, 27, 16, 30, 21]),
            mk([-5, -7, 0, -27, -16, -30, -21]),
        ),
        (
            Unit::Millisecond,
            mk([5, 7, 0, 27, 16, 30, 20, 124]),
            mk([-5, -7, 0, -27, -16, -30, -20, -124]),
        ),
        (
            Unit::Microsecond,
            mk([5, 7, 0, 27, 16, 30, 20, 123, 988]),
            mk([-5, -7, 0, -27, -16, -30, -20, -123, -988]),
        ),
        (
            Unit::Nanosecond,
            mk([5, 7, 0, 27, 16, 30, 20, 123, 987, 500]),
            mk([-5, -7, 0, -27, -16, -30, -20, -123, -987, -500]),
        ),
    ];
    for &(smallest, positive, negative) in expected {
        let options = options.smallest(smallest);
        assert_eq!(
            sp.round(options.relative(fwd))?,
            positive,
            "{sp} rounds to {positive} for smallest unit {smallest:?}",
        );
        assert_eq!(
            sp.negate().round(options.relative(bck))?,
            negative,
            "-{sp} rounds to {negative} for smallest unit {smallest:?}",
        );
    }
    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/roundingmode-floor.js
#[test]
fn roundingmode_floor() -> Result {
    let options = SpanRound::new().mode(RoundMode::Floor);
    let sp = mk([5, 6, 7, 8, 40, 30, 20, 123, 987, 500]);
    let fwd = date(2020, 4, 1);
    let bck = date(2020, 12, 1);
    let expected: &[(Unit, Span, Span)] = &[
        (Unit::Year, mk([5]), mk([-6])),
        (Unit::Month, mk([5, 7]), mk([-5, -8])),
        (Unit::Week, mk([5, 7, 3]), mk([-5, -7, -4])),
        (Unit::Day, mk([5, 7, 0, 27]), mk([-5, -7, 0, -28])),
        (Unit::Hour, mk([5, 7, 0, 27, 16]), mk([-5, -7, 0, -27, -17])),
        (
            Unit::Minute,
            mk([5, 7, 0, 27, 16, 30]),
            mk([-5, -7, 0, -27, -16, -31]),
        ),
        (
            Unit::Second,
            mk([5, 7, 0, 27, 16, 30, 20]),
            mk([-5, -7, 0, -27, -16, -30, -21]),
        ),
        (
            Unit::Millisecond,
            mk([5, 7, 0, 27, 16, 30, 20, 123]),
            mk([-5, -7, 0, -27, -16, -30, -20, -124]),
        ),
        (
            Unit::Microsecond,
            mk([5, 7, 0, 27, 16, 30, 20, 123, 987]),
            mk([-5, -7, 0, -27, -16, -30, -20, -123, -988]),
        ),
        (
            Unit::Nanosecond,
            mk([5, 7, 0, 27, 16, 30, 20, 123, 987, 500]),
            mk([-5, -7, 0, -27, -16, -30, -20, -123, -987, -500]),
        ),
    ];
    for &(smallest, positive, negative) in expected {
        let options = options.smallest(smallest);
        assert_eq!(
            sp.round(options.relative(fwd))?,
            positive,
            "{sp} rounds to {positive} for smallest unit {smallest:?}",
        );
        assert_eq!(
            sp.negate().round(options.relative(bck))?,
            negative,
            "-{sp} rounds to {negative} for smallest unit {smallest:?}",
        );
    }
    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/roundingmode-halfCeil.js
#[test]
fn roundingmode_halfceil() -> Result {
    let options = SpanRound::new().mode(RoundMode::HalfCeil);
    let sp = mk([5, 6, 7, 8, 40, 30, 20, 123, 987, 500]);
    let fwd = date(2020, 4, 1);
    let bck = date(2020, 12, 1);
    let expected: &[(Unit, Span, Span)] = &[
        (Unit::Year, mk([6]), mk([-6])),
        (Unit::Month, mk([5, 8]), mk([-5, -8])),
        (Unit::Week, mk([5, 7, 4]), mk([-5, -7, -4])),
        (Unit::Day, mk([5, 7, 0, 28]), mk([-5, -7, 0, -28])),
        (Unit::Hour, mk([5, 7, 0, 27, 17]), mk([-5, -7, 0, -27, -17])),
        (
            Unit::Minute,
            mk([5, 7, 0, 27, 16, 30]),
            mk([-5, -7, 0, -27, -16, -30]),
        ),
        (
            Unit::Second,
            mk([5, 7, 0, 27, 16, 30, 20]),
            mk([-5, -7, 0, -27, -16, -30, -20]),
        ),
        (
            Unit::Millisecond,
            mk([5, 7, 0, 27, 16, 30, 20, 124]),
            mk([-5, -7, 0, -27, -16, -30, -20, -124]),
        ),
        (
            Unit::Microsecond,
            mk([5, 7, 0, 27, 16, 30, 20, 123, 988]),
            mk([-5, -7, 0, -27, -16, -30, -20, -123, -987]),
        ),
        (
            Unit::Nanosecond,
            mk([5, 7, 0, 27, 16, 30, 20, 123, 987, 500]),
            mk([-5, -7, 0, -27, -16, -30, -20, -123, -987, -500]),
        ),
    ];
    for &(smallest, positive, negative) in expected {
        let options = options.smallest(smallest);
        assert_eq!(
            sp.round(options.relative(fwd))?,
            positive,
            "{sp} rounds to {positive} for smallest unit {smallest:?}",
        );
        assert_eq!(
            sp.negate().round(options.relative(bck))?,
            negative,
            "-{sp} rounds to {negative} for smallest unit {smallest:?}",
        );
    }
    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/roundingmode-halfEven.js
#[test]
fn roundingmode_halfeven() -> Result {
    let options = SpanRound::new().mode(RoundMode::HalfEven);
    let sp = mk([5, 6, 7, 8, 40, 30, 20, 123, 987, 500]);
    let fwd = date(2020, 4, 1);
    let bck = date(2020, 12, 1);
    let expected: &[(Unit, Span, Span)] = &[
        (Unit::Year, mk([6]), mk([-6])),
        (Unit::Month, mk([5, 8]), mk([-5, -8])),
        (Unit::Week, mk([5, 7, 4]), mk([-5, -7, -4])),
        (Unit::Day, mk([5, 7, 0, 28]), mk([-5, -7, 0, -28])),
        (Unit::Hour, mk([5, 7, 0, 27, 17]), mk([-5, -7, 0, -27, -17])),
        (
            Unit::Minute,
            mk([5, 7, 0, 27, 16, 30]),
            mk([-5, -7, 0, -27, -16, -30]),
        ),
        (
            Unit::Second,
            mk([5, 7, 0, 27, 16, 30, 20]),
            mk([-5, -7, 0, -27, -16, -30, -20]),
        ),
        (
            Unit::Millisecond,
            mk([5, 7, 0, 27, 16, 30, 20, 124]),
            mk([-5, -7, 0, -27, -16, -30, -20, -124]),
        ),
        (
            Unit::Microsecond,
            mk([5, 7, 0, 27, 16, 30, 20, 123, 988]),
            mk([-5, -7, 0, -27, -16, -30, -20, -123, -988]),
        ),
        (
            Unit::Nanosecond,
            mk([5, 7, 0, 27, 16, 30, 20, 123, 987, 500]),
            mk([-5, -7, 0, -27, -16, -30, -20, -123, -987, -500]),
        ),
    ];
    for &(smallest, positive, negative) in expected {
        let options = options.smallest(smallest);
        assert_eq!(
            sp.round(options.relative(fwd))?,
            positive,
            "{sp} rounds to {positive} for smallest unit {smallest:?}",
        );
        assert_eq!(
            sp.negate().round(options.relative(bck))?,
            negative,
            "-{sp} rounds to {negative} for smallest unit {smallest:?}",
        );
    }
    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/roundingmode-halfExpand.js
#[test]
fn roundingmode_halfexpand() -> Result {
    let options = SpanRound::new().mode(RoundMode::HalfExpand);
    let sp = mk([5, 6, 7, 8, 40, 30, 20, 123, 987, 500]);
    let fwd = date(2020, 4, 1);
    let bck = date(2020, 12, 1);
    let expected: &[(Unit, Span, Span)] = &[
        (Unit::Year, mk([6]), mk([-6])),
        (Unit::Month, mk([5, 8]), mk([-5, -8])),
        (Unit::Week, mk([5, 7, 4]), mk([-5, -7, -4])),
        (Unit::Day, mk([5, 7, 0, 28]), mk([-5, -7, 0, -28])),
        (Unit::Hour, mk([5, 7, 0, 27, 17]), mk([-5, -7, 0, -27, -17])),
        (
            Unit::Minute,
            mk([5, 7, 0, 27, 16, 30]),
            mk([-5, -7, 0, -27, -16, -30]),
        ),
        (
            Unit::Second,
            mk([5, 7, 0, 27, 16, 30, 20]),
            mk([-5, -7, 0, -27, -16, -30, -20]),
        ),
        (
            Unit::Millisecond,
            mk([5, 7, 0, 27, 16, 30, 20, 124]),
            mk([-5, -7, 0, -27, -16, -30, -20, -124]),
        ),
        (
            Unit::Microsecond,
            mk([5, 7, 0, 27, 16, 30, 20, 123, 988]),
            mk([-5, -7, 0, -27, -16, -30, -20, -123, -988]),
        ),
        (
            Unit::Nanosecond,
            mk([5, 7, 0, 27, 16, 30, 20, 123, 987, 500]),
            mk([-5, -7, 0, -27, -16, -30, -20, -123, -987, -500]),
        ),
    ];
    for &(smallest, positive, negative) in expected {
        let options = options.smallest(smallest);
        assert_eq!(
            sp.round(options.relative(fwd))?,
            positive,
            "{sp} rounds to {positive} for smallest unit {smallest:?}",
        );
        assert_eq!(
            sp.negate().round(options.relative(bck))?,
            negative,
            "-{sp} rounds to {negative} for smallest unit {smallest:?}",
        );
    }
    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/roundingmode-halfFloor.js
#[test]
fn roundingmode_halffloor() -> Result {
    let options = SpanRound::new().mode(RoundMode::HalfFloor);
    let sp = mk([5, 6, 7, 8, 40, 30, 20, 123, 987, 500]);
    let fwd = date(2020, 4, 1);
    let bck = date(2020, 12, 1);
    let expected: &[(Unit, Span, Span)] = &[
        (Unit::Year, mk([6]), mk([-6])),
        (Unit::Month, mk([5, 8]), mk([-5, -8])),
        (Unit::Week, mk([5, 7, 4]), mk([-5, -7, -4])),
        (Unit::Day, mk([5, 7, 0, 28]), mk([-5, -7, 0, -28])),
        (Unit::Hour, mk([5, 7, 0, 27, 17]), mk([-5, -7, 0, -27, -17])),
        (
            Unit::Minute,
            mk([5, 7, 0, 27, 16, 30]),
            mk([-5, -7, 0, -27, -16, -30]),
        ),
        (
            Unit::Second,
            mk([5, 7, 0, 27, 16, 30, 20]),
            mk([-5, -7, 0, -27, -16, -30, -20]),
        ),
        (
            Unit::Millisecond,
            mk([5, 7, 0, 27, 16, 30, 20, 124]),
            mk([-5, -7, 0, -27, -16, -30, -20, -124]),
        ),
        (
            Unit::Microsecond,
            mk([5, 7, 0, 27, 16, 30, 20, 123, 987]),
            mk([-5, -7, 0, -27, -16, -30, -20, -123, -988]),
        ),
        (
            Unit::Nanosecond,
            mk([5, 7, 0, 27, 16, 30, 20, 123, 987, 500]),
            mk([-5, -7, 0, -27, -16, -30, -20, -123, -987, -500]),
        ),
    ];
    for &(smallest, positive, negative) in expected {
        let options = options.smallest(smallest);
        assert_eq!(
            sp.round(options.relative(fwd))?,
            positive,
            "{sp} rounds to {positive} for smallest unit {smallest:?}",
        );
        assert_eq!(
            sp.negate().round(options.relative(bck))?,
            negative,
            "-{sp} rounds to {negative} for smallest unit {smallest:?}",
        );
    }
    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/roundingmode-halfTrunc.js
#[test]
fn roundingmode_halftrunc() -> Result {
    let options = SpanRound::new().mode(RoundMode::HalfTrunc);
    let sp = mk([5, 6, 7, 8, 40, 30, 20, 123, 987, 500]);
    let fwd = date(2020, 4, 1);
    let bck = date(2020, 12, 1);
    let expected: &[(Unit, Span, Span)] = &[
        (Unit::Year, mk([6]), mk([-6])),
        (Unit::Month, mk([5, 8]), mk([-5, -8])),
        (Unit::Week, mk([5, 7, 4]), mk([-5, -7, -4])),
        (Unit::Day, mk([5, 7, 0, 28]), mk([-5, -7, 0, -28])),
        (Unit::Hour, mk([5, 7, 0, 27, 17]), mk([-5, -7, 0, -27, -17])),
        (
            Unit::Minute,
            mk([5, 7, 0, 27, 16, 30]),
            mk([-5, -7, 0, -27, -16, -30]),
        ),
        (
            Unit::Second,
            mk([5, 7, 0, 27, 16, 30, 20]),
            mk([-5, -7, 0, -27, -16, -30, -20]),
        ),
        (
            Unit::Millisecond,
            mk([5, 7, 0, 27, 16, 30, 20, 124]),
            mk([-5, -7, 0, -27, -16, -30, -20, -124]),
        ),
        (
            Unit::Microsecond,
            mk([5, 7, 0, 27, 16, 30, 20, 123, 987]),
            mk([-5, -7, 0, -27, -16, -30, -20, -123, -987]),
        ),
        (
            Unit::Nanosecond,
            mk([5, 7, 0, 27, 16, 30, 20, 123, 987, 500]),
            mk([-5, -7, 0, -27, -16, -30, -20, -123, -987, -500]),
        ),
    ];
    for &(smallest, positive, negative) in expected {
        let options = options.smallest(smallest);
        assert_eq!(
            sp.round(options.relative(fwd))?,
            positive,
            "{sp} rounds to {positive} for smallest unit {smallest:?}",
        );
        assert_eq!(
            sp.negate().round(options.relative(bck))?,
            negative,
            "-{sp} rounds to {negative} for smallest unit {smallest:?}",
        );
    }
    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/roundingmode-trunc.js
#[test]
fn roundingmode_trunc() -> Result {
    let options = SpanRound::new().mode(RoundMode::Trunc);
    let sp = mk([5, 6, 7, 8, 40, 30, 20, 123, 987, 500]);
    let fwd = date(2020, 4, 1);
    let bck = date(2020, 12, 1);
    let expected: &[(Unit, Span, Span)] = &[
        (Unit::Year, mk([5]), mk([-5])),
        (Unit::Month, mk([5, 7]), mk([-5, -7])),
        (Unit::Week, mk([5, 7, 3]), mk([-5, -7, -3])),
        (Unit::Day, mk([5, 7, 0, 27]), mk([-5, -7, 0, -27])),
        (Unit::Hour, mk([5, 7, 0, 27, 16]), mk([-5, -7, 0, -27, -16])),
        (
            Unit::Minute,
            mk([5, 7, 0, 27, 16, 30]),
            mk([-5, -7, 0, -27, -16, -30]),
        ),
        (
            Unit::Second,
            mk([5, 7, 0, 27, 16, 30, 20]),
            mk([-5, -7, 0, -27, -16, -30, -20]),
        ),
        (
            Unit::Millisecond,
            mk([5, 7, 0, 27, 16, 30, 20, 123]),
            mk([-5, -7, 0, -27, -16, -30, -20, -123]),
        ),
        (
            Unit::Microsecond,
            mk([5, 7, 0, 27, 16, 30, 20, 123, 987]),
            mk([-5, -7, 0, -27, -16, -30, -20, -123, -987]),
        ),
        (
            Unit::Nanosecond,
            mk([5, 7, 0, 27, 16, 30, 20, 123, 987, 500]),
            mk([-5, -7, 0, -27, -16, -30, -20, -123, -987, -500]),
        ),
    ];
    for &(smallest, positive, negative) in expected {
        let options = options.smallest(smallest);
        assert_eq!(
            sp.round(options.relative(fwd))?,
            positive,
            "{sp} rounds to {positive} for smallest unit {smallest:?}",
        );
        assert_eq!(
            sp.negate().round(options.relative(bck))?,
            negative,
            "-{sp} rounds to {negative} for smallest unit {smallest:?}",
        );
    }
    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/round/smallestunit.js
#[test]
fn smallestunit() -> Result {
    let sp = 1
        .day()
        .hours(2)
        .minutes(3)
        .seconds(4)
        .milliseconds(5)
        .microseconds(6)
        .nanoseconds(7);
    let tests: &[(Unit, Span)] = &[
        (Unit::Day, 1.day()),
        (Unit::Hour, 1.day().hours(2)),
        (Unit::Minute, 1.day().hours(2).minutes(3)),
        (Unit::Second, 1.day().hours(2).minutes(3).seconds(4)),
        (
            Unit::Millisecond,
            1.day().hours(2).minutes(3).seconds(4).milliseconds(5),
        ),
        (
            Unit::Microsecond,
            1.day()
                .hours(2)
                .minutes(3)
                .seconds(4)
                .milliseconds(5)
                .microseconds(6),
        ),
        (
            Unit::Nanosecond,
            1.day()
                .hours(2)
                .minutes(3)
                .seconds(4)
                .milliseconds(5)
                .microseconds(6)
                .nanoseconds(7),
        ),
    ];
    for &(smallest, expected) in tests {
        assert_eq!(
            sp.round(smallest)?,
            expected,
            "rounding {sp} to {smallest:?}"
        );
    }
    Ok(())
}
