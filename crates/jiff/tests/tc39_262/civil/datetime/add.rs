use jiff::{civil::date, ToSpan};

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/add/ambiguous-date.js
///
/// DIFFERENCE: Jiff doesn't currently support `overflow: reject` semantics.
#[test]
fn ambiguous_date() {
    let dt1 = date(2020, 1, 31).at(15, 0, 0, 0);
    assert_eq!(dt1 + 1.month(), date(2020, 2, 29).at(15, 0, 0, 0));
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/add/balance-negative-time-units.js
#[test]
fn balance_negative_time_units() {
    let dt = date(1996, 5, 2).at(1, 1, 1, 001_001_001);

    assert_eq!(
        dt + -2.nanoseconds(),
        date(1996, 5, 2).at(1, 1, 1, 001_000_999)
    );
    assert_eq!(
        dt - 2.nanoseconds(),
        date(1996, 5, 2).at(1, 1, 1, 001_000_999)
    );

    assert_eq!(
        dt + -2.microseconds(),
        date(1996, 5, 2).at(1, 1, 1, 000_999_001)
    );
    assert_eq!(
        dt - 2.microseconds(),
        date(1996, 5, 2).at(1, 1, 1, 000_999_001)
    );

    assert_eq!(
        dt + -2.milliseconds(),
        date(1996, 5, 2).at(1, 1, 0, 999_001_001)
    );
    assert_eq!(
        dt - 2.milliseconds(),
        date(1996, 5, 2).at(1, 1, 0, 999_001_001)
    );

    assert_eq!(dt + -2.seconds(), date(1996, 5, 2).at(1, 0, 59, 001_001_001));
    assert_eq!(dt - 2.seconds(), date(1996, 5, 2).at(1, 0, 59, 001_001_001));

    assert_eq!(dt + -2.minutes(), date(1996, 5, 2).at(0, 59, 1, 001_001_001));
    assert_eq!(dt - 2.minutes(), date(1996, 5, 2).at(0, 59, 1, 001_001_001));

    assert_eq!(dt + -2.hours(), date(1996, 5, 1).at(23, 1, 1, 001_001_001));
    assert_eq!(dt - 2.hours(), date(1996, 5, 1).at(23, 1, 1, 001_001_001));
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/add/hour-overflow.js
#[test]
fn hour_overflow() {
    let dt = date(2020, 5, 31).at(23, 12, 38, 271_986_102);
    assert_eq!(dt + 2.hours(), date(2020, 6, 1).at(1, 12, 38, 271_986_102));

    let dt = date(2019, 10, 29).at(10, 46, 38, 271_986_102);
    assert_eq!(
        dt - 12.hours(),
        date(2019, 10, 28).at(22, 46, 38, 271_986_102)
    );
}
