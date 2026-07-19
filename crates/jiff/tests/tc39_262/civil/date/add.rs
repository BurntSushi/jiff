use jiff::{
    civil::{date, Date},
    Span, ToSpan,
};

use crate::tc39_262::Result;

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDate/prototype/add/balance-smaller-units-basic.js
#[test]
fn balance_smaller_units_basic() -> Result {
    let d1 = date(1976, 11, 18);

    assert_eq!(d1.checked_add(1.hour())?, d1);
    assert_eq!(d1.checked_add(1.minute())?, d1);
    assert_eq!(d1.checked_add(1.second())?, d1);
    assert_eq!(d1.checked_add(1.millisecond())?, d1);
    assert_eq!(d1.checked_add(1.microsecond())?, d1);
    assert_eq!(d1.checked_add(1.nanosecond())?, d1);

    let d2 = date(1976, 11, 19);
    assert_eq!(d1.checked_add(24.hours())?, d2);
    assert_eq!(d1.checked_add(36.hours())?, d2);
    assert_eq!(d1.checked_add(48.hours())?, date(1976, 11, 20));
    assert_eq!(d1.checked_add(1440.minutes())?, d2);
    assert_eq!(d1.checked_add(86400.seconds())?, d2);
    assert_eq!(d1.checked_add(86400_000.milliseconds())?, d2);
    assert_eq!(d1.checked_add(86400_000_000i64.microseconds())?, d2);
    assert_eq!(d1.checked_add(86400_000_000_000i64.nanoseconds())?, d2);

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDate/prototype/add/balance-smaller-units.js
#[test]
fn balance_smaller_units() -> Result {
    let d = date(2000, 5, 2);

    let span: Span = "P1dT24h1440m86400s".parse()?;
    assert_eq!(d + span, date(2000, 5, 6));

    let span = 1
        .day()
        .hours(24)
        .minutes(1440)
        .seconds(86400)
        .milliseconds(86400_000)
        .microseconds(86400_000_000i64)
        .nanoseconds(86400_000_000_000i64);
    assert_eq!(d + span, date(2000, 5, 9));
    assert_eq!(d + -span, date(2000, 4, 25));
    assert_eq!(d - span, date(2000, 4, 25));

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDate/prototype/add/basic.js
#[test]
fn basic() -> Result {
    let d: Date = "1976-11-18".parse()?;

    assert_eq!(d + 43.years(), date(2019, 11, 18));
    assert_eq!(d + 3.months(), date(1977, 2, 18));
    assert_eq!(d + 20.days(), date(1976, 12, 8));

    let d: Date = "2019-01-31".parse()?;
    assert_eq!(d + 1.month(), date(2019, 2, 28));

    let d: Date = "2019-11-18".parse()?;
    assert_eq!(d + -43.years(), date(1976, 11, 18));
    assert_eq!(d - 43.years(), date(1976, 11, 18));

    let d: Date = "1977-02-18".parse()?;
    assert_eq!(d + -3.months(), date(1976, 11, 18));
    assert_eq!(d - 3.months(), date(1976, 11, 18));

    let d: Date = "1976-12-08".parse()?;
    assert_eq!(d + -20.days(), date(1976, 11, 18));
    assert_eq!(d - 20.days(), date(1976, 11, 18));

    let d: Date = "2019-02-28".parse()?;
    assert_eq!(d + -1.month(), date(2019, 1, 28));
    assert_eq!(d - 1.month(), date(2019, 1, 28));

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDate/prototype/add/overflow-constrain.js
#[test]
fn overflow_constrain() {
    let d = date(2020, 1, 31);
    assert_eq!(d + 1.month(), date(2020, 2, 29));
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDate/prototype/add/overflow-reject.js
#[test]
fn overflow_reject() {
    // DIFFERENCE: We don't support 'reject' semantics.
    let d = date(2020, 1, 31);
    assert_eq!(d + 1.month(), date(2020, 2, 29));
}
