use jiff::{
    civil::DateTime,
    round::{RoundMode, Unit},
};

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainDateTime/prototype/round/balance.js
#[test]
fn balance() {
    let dt = DateTime::constant(1976, 11, 18, 23, 59, 59, 999_999_999);
    let expected = DateTime::constant(1976, 11, 19, 0, 0, 0, 0);

    assert_eq!(dt.round(Unit::Day), expected);
    assert_eq!(dt.round(Unit::Hour), expected);
    assert_eq!(dt.round(Unit::Minute), expected);
    assert_eq!(dt.round(Unit::Second), expected);
    assert_eq!(dt.round(Unit::Millisecond), expected);
    assert_eq!(dt.round(Unit::Microsecond), expected);
    assert_eq!(dt.round(Unit::Nanosecond), dt);
}

/// DIFFERENCE: Temporal and Jiff have different maximums, so we use our own
/// values here.
///
/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainDateTime/prototype/round/limits.js
#[test]
fn limits() {
    let dt = DateTime::constant(9999, 12, 31, 23, 59, 59, 999_999_999);
    assert!(dt.try_round(Unit::Day).is_err());
    assert!(dt.try_round(Unit::Microsecond).is_err());

    let dt = DateTime::constant(9999, 12, 31, 23, 59, 59, 999_999_499);
    assert!(dt.try_round(Unit::Day).is_err());
    assert_eq!(
        dt.round(Unit::Microsecond),
        DateTime::constant(9999, 12, 31, 23, 59, 59, 999_999_000)
    );

    let dt = DateTime::constant(-9999, 1, 1, 0, 0, 0, 000_000_001);
    assert_eq!(
        dt.round(Unit::Microsecond.mode(RoundMode::Floor)),
        DateTime::constant(-9999, 1, 1, 0, 0, 0, 0)
    );
}
