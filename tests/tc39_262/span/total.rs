use jiff::{civil::date, tz, Timestamp, ToSpan, Unit, Zoned};

use crate::tc39_262::Result;

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/total/balance-negative-result.js
#[test]
fn balance_negative_result() -> Result {
    let sp = -60.hours();
    let result = sp.total(Unit::Day)?;
    assert_eq!(result, -2.5);

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/total/balance-subseconds.js
#[test]
fn balance_subseconds() -> Result {
    let sp = 999.milliseconds().microseconds(999_999).nanoseconds(999_999_999);
    let result = sp.total(Unit::Second)?;
    assert_eq!(result, 2.998998999);

    let sp =
        -999.milliseconds().microseconds(999_999).nanoseconds(999_999_999);
    let result = sp.total(Unit::Second)?;
    assert_eq!(result, -2.998998999);

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/total/calendar-possibly-required.js
#[test]
fn calendar_possibly_required() -> Result {
    let year = 1999.years();
    let month = 49.months();
    let week = 1.week();
    let day = 42.days();
    let d = date(2021, 12, 15);

    insta::assert_snapshot!(
        year.total(Unit::Day).unwrap_err(),
        @"using unit 'year' requires that a relative reference time be given, but none was provided",
    );
    let result = year.total((Unit::Day, d))?;
    assert_eq!(result, 730_120.0);

    insta::assert_snapshot!(
        month.total(Unit::Day).unwrap_err(),
        @"using unit 'month' requires that a relative reference time be given, but none was provided",
    );
    let result = month.total((Unit::Day, d))?;
    assert_eq!(result, 1_492.0);

    insta::assert_snapshot!(
        week.total(Unit::Day).unwrap_err(),
        @"using unit 'week' requires that a relative reference time be given, but none was provided",
    );
    let result = week.total((Unit::Day, d))?;
    assert_eq!(result, 7.0);

    let result = day.total(Unit::Day)?;
    assert_eq!(result, 42.0);
    let result = day.total((Unit::Day, d))?;
    assert_eq!(result, 42.0);

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/total/dst-balancing-result.js
#[test]
fn dst_balancing_result() -> Result {
    if jiff::tz::db().is_definitively_empty() {
        return Ok(());
    }

    let sp = 1.year().hours(24);
    let zdt = "1999-10-29T01-07[America/Los_Angeles]".parse::<Zoned>()?;
    let result = sp.total((Unit::Day, &zdt))?;
    assert_eq!(result, 366.96);

    // Added my own test here using a shorter duration since we use an
    // actual time zone for testing, where as Temporal uses a "dummy" time
    // zone with only one forward and one backward transition in the year 2000.
    // But with real TZ data, a span of 1 year will pretty much always cover
    // a DST backward transition.
    let sp = 1.month().hours(24);
    let zdt = "2000-09-29T01-07[America/Los_Angeles]".parse::<Zoned>()?;
    let result = sp.total((Unit::Day, &zdt))?;
    assert_eq!(result, 30.96);

    // Try one month earlier, and we balance up to 1 day.
    let sp = 1.month().hours(24);
    let zdt = "2000-08-29T01-07[America/Los_Angeles]".parse::<Zoned>()?;
    let result = sp.total((Unit::Day, &zdt))?;
    assert_eq!(result, 32.0);

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/total/dst-day-length.js
#[test]
fn dst_day_length() -> Result {
    if jiff::tz::db().is_definitively_empty() {
        return Ok(());
    }

    let skipped_hour_day = "2000-04-02T00-08[America/Los_Angeles]".parse()?;
    let repeated_hour_day = "2000-10-29T00-07[America/Los_Angeles]".parse()?;
    let in_repeated_hour = "2000-10-29T01-07[America/Los_Angeles]".parse()?;
    let one_day_after_repeated_hour =
        "2000-10-30T01-08[America/Los_Angeles]".parse()?;
    let before_skipped_hour =
        "2000-04-01T02:30-08[America/Los_Angeles]".parse()?;
    let day_after_skipped_hour =
        "2000-04-03T00-07[America/Los_Angeles]".parse()?;
    let after_skipped_hour =
        "2000-04-02T12-07[America/Los_Angeles]".parse()?;
    let after_repeated_hour =
        "2000-10-30T00-08[America/Los_Angeles]".parse()?;
    let after_repeated_hour_same_day =
        "2000-10-29T12-08[America/Los_Angeles]".parse()?;
    let before_repeated_hour =
        "2000-10-28T00-07[America/Los_Angeles]".parse()?;

    assert_eq!(25.hours().total((Unit::Day, &in_repeated_hour))?, 1.0);
    assert_eq!(1.day().total((Unit::Hour, &in_repeated_hour))?, 25.0);
    assert_eq!(
        (-25.hours()).total((Unit::Day, &one_day_after_repeated_hour))?,
        -1.0
    );
    assert_eq!(
        (-1.day()).total((Unit::Hour, &one_day_after_repeated_hour))?,
        -25.0
    );
    assert_eq!(
        25.hours().total((Unit::Day, &before_skipped_hour))?,
        24.0 / 23.0
    );
    assert_eq!(1.day().total((Unit::Hour, &before_skipped_hour))?, 24.0);
    assert_eq!(25.hours().total((Unit::Day, &skipped_hour_day))?, 13.0 / 12.0);
    assert_eq!(1.day().total((Unit::Hour, &skipped_hour_day))?, 23.0);
    assert_eq!(
        (-25.hours()).total((Unit::Day, &day_after_skipped_hour))?,
        -13.0 / 12.0
    );
    assert_eq!(
        (-1.day()).total((Unit::Hour, &day_after_skipped_hour))?,
        -23.0
    );
    assert_eq!(12.hours().total((Unit::Day, &skipped_hour_day))?, 12.0 / 23.0);
    assert_eq!(
        (-12.hours()).total((Unit::Day, &after_skipped_hour))?,
        -12.0 / 23.0
    );
    assert_eq!(25.hours().total((Unit::Day, &repeated_hour_day))?, 1.0);
    assert_eq!(1.day().total((Unit::Hour, &repeated_hour_day))?, 25.0);
    assert_eq!((-25.hours()).total((Unit::Day, &after_repeated_hour))?, -1.0);
    assert_eq!((-1.day()).total((Unit::Hour, &after_repeated_hour))?, -25.0);
    assert_eq!(
        12.hours().total((Unit::Day, &repeated_hour_day))?,
        12.0 / 25.0
    );
    assert_eq!(
        (-12.hours()).total((Unit::Day, &after_repeated_hour_same_day))?,
        -12.0 / 25.0
    );
    assert_eq!(
        48.hours().total((Unit::Day, &before_repeated_hour))?,
        49.0 / 25.0
    );

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/total/dst-rounding-result.js
#[test]
fn dst_rounding_result() -> Result {
    if jiff::tz::db().is_definitively_empty() {
        return Ok(());
    }

    let sp = 1.month().days(15).hours(11).minutes(30);
    let zdt = "2000-02-18T02-08[America/Los_Angeles]".parse()?;
    assert_eq!(sp.total((Unit::Month, &zdt))?, 1.5);

    let sp = 1.month().days(15).minutes(30);
    let zdt = "2000-03-02T02-08[America/Los_Angeles]".parse()?;
    assert_eq!(sp.total((Unit::Month, &zdt))?, 1.5);

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/total/no-dst-day-length.js
#[test]
fn no_dst_day_length() -> Result {
    assert_eq!(1.day().total(Unit::Hour)?, 24.0);
    assert_eq!(48.hours().total(Unit::Day)?, 2.0);

    let d = date(2017, 1, 1);
    assert_eq!(1.day().total((Unit::Hour, d))?, 24.0);
    assert_eq!(48.hours().total((Unit::Day, d))?, 2.0);

    let zdt = Timestamp::from_second(1_000_000_000)?
        .to_zoned(tz::offset(4).to_time_zone());
    assert_eq!(1.day().total((Unit::Hour, &zdt))?, 24.0);
    assert_eq!(48.hours().total((Unit::Day, &zdt))?, 2.0);

    Ok(())
}
