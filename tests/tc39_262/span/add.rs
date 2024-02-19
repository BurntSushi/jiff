use jiff::{Span, ToSpan};

use crate::tc39_262::Result;

const MAX_SPAN_SECONDS: i64 = 631_107_417_600;
const MAX_SPAN_NANOSECONDS: i64 = 9_223_372_036_854_775_807;

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/add/balance-negative-result.js
#[test]
fn balance_negative_result() -> Result {
    let sp1 = -60.hours();
    let sp2 = -1.day();
    let result = sp1.checked_add(sp2)?;
    assert_eq!(result, -3.days().hours(12));

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/add/balance-negative-time-units.js
#[test]
fn balance_negative_time_units() -> Result {
    let sp = 1
        .hour()
        .minutes(1)
        .seconds(1)
        .milliseconds(1)
        .microseconds(1)
        .nanoseconds(1);

    let result = sp.checked_add(-2.nanoseconds())?;
    assert_eq!(
        result,
        1.hour()
            .minutes(1)
            .seconds(1)
            .milliseconds(1)
            .microseconds(0)
            .nanoseconds(999),
    );

    let result = sp.checked_add(-2.microseconds())?;
    assert_eq!(
        result,
        1.hour()
            .minutes(1)
            .seconds(1)
            .milliseconds(0)
            .microseconds(999)
            .nanoseconds(1),
    );

    let result = sp.checked_add(-2.milliseconds())?;
    assert_eq!(
        result,
        1.hour()
            .minutes(1)
            .seconds(0)
            .milliseconds(999)
            .microseconds(1)
            .nanoseconds(1),
    );

    let result = sp.checked_add(-2.seconds())?;
    assert_eq!(
        result,
        1.hour()
            .minutes(0)
            .seconds(59)
            .milliseconds(1)
            .microseconds(1)
            .nanoseconds(1),
    );

    let result = sp.checked_add(-2.minutes())?;
    assert_eq!(
        result,
        0.hours()
            .minutes(59)
            .seconds(1)
            .milliseconds(1)
            .microseconds(1)
            .nanoseconds(1),
    );

    let result = sp.checked_add(-2.hours())?;
    assert_eq!(
        result,
        -58.minutes()
            .seconds(58)
            .milliseconds(998)
            .microseconds(998)
            .nanoseconds(999),
    );

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/add/basic.js
#[test]
fn basic() -> Result {
    let sp = 1.day().minutes(5);
    let result = sp.checked_add(2.days().minutes(5))?;
    assert_eq!(result, 3.days().minutes(10));
    let result = sp.checked_add(12.hours().seconds(30))?;
    assert_eq!(result, 1.day().hours(12).minutes(5).seconds(30));

    let sp = 3.days().minutes(10);
    let result = sp.checked_add(-2.days().minutes(5))?;
    assert_eq!(result, 1.day().minutes(5));

    let sp = 1.day().hours(12).minutes(5).seconds(30);
    let result = sp.checked_add(-12.hours().seconds(30))?;
    assert_eq!(result, 1.day().minutes(5));

    let sp = "P50DT50H50M50.500500500S".parse::<Span>()?;
    let result = sp.checked_add(sp)?;
    assert_eq!(
        result,
        104.days()
            .hours(5)
            .minutes(41)
            .seconds(41)
            .milliseconds(1)
            .microseconds(1)
    );

    let sp = -1.hour().seconds(60);
    let result = sp.checked_add(122.minutes())?;
    assert_eq!(result, 1.hour().minutes(1));

    let sp = -1.hour().seconds(3_721);
    let result = sp.checked_add(61.minutes().nanoseconds(3722000000001i64))?;
    assert_eq!(result, 1.minute().seconds(1).nanoseconds(1));

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/add/nanoseconds-is-number-max-safe-integer.js
#[test]
fn nanoseconds_is_number_max_safe_integer() -> Result {
    let sp1 = MAX_SPAN_NANOSECONDS.nanoseconds();
    let sp2 = 1.day().nanoseconds(2);
    let result = sp1.checked_add(sp2)?;

    let nanos = i128::from(MAX_SPAN_NANOSECONDS) + 2;
    let expected = Span::new()
        .days(1 + (nanos / (24 * 60 * 60 * 1_000_000_000)) as i64)
        .hours(((nanos / (60 * 60 * 1_000_000_000)) % 24) as i64)
        .minutes(((nanos / (60 * 1_000_000_000)) % 60) as i64)
        .seconds(((nanos / 1_000_000_000) % 60) as i64)
        .milliseconds(((nanos / 1_000_000) % 1_000) as i64)
        .microseconds(((nanos / 1_000) % 1_000) as i64)
        .nanoseconds((nanos % 1_000) as i64);
    assert_eq!(result, expected);

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/add/no-calendar-units.js
#[test]
fn no_calendar_units() -> Result {
    let blank = Span::new();
    insta::assert_snapshot!(
        1.year().checked_add(blank).unwrap_err(),
        @"using largest unit (which is 'year') in given span requires that a relative reference time be given, but none was provided",
    );
    insta::assert_snapshot!(
        1.month().checked_add(blank).unwrap_err(),
        @"using largest unit (which is 'month') in given span requires that a relative reference time be given, but none was provided",
    );
    insta::assert_snapshot!(
        1.week().checked_add(blank).unwrap_err(),
        @"using largest unit (which is 'week') in given span requires that a relative reference time be given, but none was provided",
    );

    let ok = 1.day();
    insta::assert_snapshot!(
        ok.checked_add(1.year()).unwrap_err(),
        @"using largest unit (which is 'year') in given span requires that a relative reference time be given, but none was provided",
    );
    insta::assert_snapshot!(
        ok.checked_add(1.month()).unwrap_err(),
        @"using largest unit (which is 'month') in given span requires that a relative reference time be given, but none was provided",
    );
    insta::assert_snapshot!(
        ok.checked_add(1.month()).unwrap_err(),
        @"using largest unit (which is 'month') in given span requires that a relative reference time be given, but none was provided",
    );

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/Duration/prototype/add/result-out-of-range-1.js
#[test]
fn result_out_of_range() -> Result {
    let sp = MAX_SPAN_SECONDS.seconds();
    insta::assert_snapshot!(
        sp.checked_add(sp).unwrap_err(),
        @"parameter 'seconds' with value 1262214835200 is not in the required range of -631107417600..=631107417600",
    );

    Ok(())
}
