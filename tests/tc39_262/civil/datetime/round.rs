use jiff::{
    civil::{date, DateTimeRound},
    RoundMode, Unit,
};

use crate::tc39_262::Result;

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainDateTime/prototype/round/balance.js
#[test]
fn balance() -> Result {
    let dt = date(1976, 11, 18).at(23, 59, 59, 999_999_999);
    let expected = date(1976, 11, 19).at(0, 0, 0, 0);

    assert_eq!(dt.round(Unit::Day)?, expected);
    assert_eq!(dt.round(Unit::Hour)?, expected);
    assert_eq!(dt.round(Unit::Minute)?, expected);
    assert_eq!(dt.round(Unit::Second)?, expected);
    assert_eq!(dt.round(Unit::Millisecond)?, expected);
    assert_eq!(dt.round(Unit::Microsecond)?, expected);
    assert_eq!(dt.round(Unit::Nanosecond)?, dt);

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainDateTime/prototype/round/limits.js
///
/// DIFFERENCE: Temporal and Jiff have different maximums, so we use our own
/// values here.
#[test]
fn limits() -> Result {
    let dt = date(9999, 12, 31).at(23, 59, 59, 999_999_999);
    assert!(dt.round(Unit::Day).is_err());
    assert!(dt.round(Unit::Microsecond).is_err());

    let dt = date(9999, 12, 31).at(23, 59, 59, 999_999_499);
    assert!(dt.round(Unit::Day).is_err());
    assert_eq!(
        dt.round(Unit::Microsecond)?,
        date(9999, 12, 31).at(23, 59, 59, 999_999_000),
    );

    let dt = date(-9999, 1, 1).at(0, 0, 0, 000_000_001);
    assert_eq!(
        dt.round(
            DateTimeRound::new()
                .smallest(Unit::Microsecond)
                .mode(RoundMode::Floor)
        )?,
        date(-9999, 1, 1).at(0, 0, 0, 0),
    );

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/round/rounding-direction.js
#[test]
fn rounding_direction() -> Result {
    let dt = date(-99, 12, 15).at(12, 0, 0, 500_000_000);

    let args =
        DateTimeRound::new().smallest(Unit::Second).mode(RoundMode::Floor);
    assert_eq!(dt.round(args)?, date(-99, 12, 15).at(12, 0, 0, 0));

    let args =
        DateTimeRound::new().smallest(Unit::Second).mode(RoundMode::Trunc);
    assert_eq!(dt.round(args)?, date(-99, 12, 15).at(12, 0, 0, 0));

    let args =
        DateTimeRound::new().smallest(Unit::Second).mode(RoundMode::Ceil);
    assert_eq!(dt.round(args)?, date(-99, 12, 15).at(12, 0, 1, 0));

    let args = DateTimeRound::new()
        .smallest(Unit::Second)
        .mode(RoundMode::HalfExpand);
    assert_eq!(dt.round(args)?, date(-99, 12, 15).at(12, 0, 1, 0));

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/round/roundingincrement-divides.js
#[test]
fn roundingincrement_divides() {
    let dt = date(1976, 11, 18).at(14, 23, 30, 123_456_789);

    for increment in [1, 2, 3, 4, 6, 8, 12] {
        assert!(dt.round((Unit::Hour, increment)).is_ok());
    }
    for unit in [Unit::Minute, Unit::Second] {
        for increment in [1, 2, 3, 4, 5, 6, 10, 12, 15, 20, 30] {
            assert!(dt.round((unit, increment)).is_ok());
        }
    }
    for unit in [Unit::Millisecond, Unit::Microsecond, Unit::Nanosecond] {
        let increments =
            [1, 2, 4, 5, 8, 10, 20, 25, 40, 50, 100, 125, 200, 250, 500];
        for increment in increments {
            assert!(dt.round((unit, increment)).is_ok());
        }
    }

    let next_increments = [
        (Unit::Hour, 23),
        (Unit::Minute, 60),
        (Unit::Second, 60),
        (Unit::Millisecond, 1000),
        (Unit::Microsecond, 1000),
        (Unit::Nanosecond, 1000),
    ];
    for (unit, increment) in next_increments {
        assert!(dt.round((unit, increment)).is_err());
    }
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/round/roundingincrement-does-not-divide.js
#[test]
fn roundingincrement_does_not_divide() {
    let dt = date(1976, 11, 18).at(14, 23, 30, 123_456_789);
    let units = [
        Unit::Day,
        Unit::Hour,
        Unit::Minute,
        Unit::Second,
        Unit::Millisecond,
        Unit::Microsecond,
        Unit::Nanosecond,
    ];
    for unit in units {
        assert!(dt.round((unit, 29)).is_err());
    }
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/round/roundingincrement-one-day.js
#[test]
fn roundingincrement_one_day() -> Result {
    let dt = date(1976, 11, 18).at(14, 23, 30, 123_456_789);
    assert_eq!(dt.round((Unit::Day, 1))?, date(1976, 11, 19).at(0, 0, 0, 0));
    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/round/roundingmode-basic.js
#[test]
fn roundingmode_basic() -> Result {
    let dt = date(1976, 11, 18).at(14, 23, 30, 123_456_789);

    assert_eq!(dt.round((Unit::Hour, 4))?, date(1976, 11, 18).at(16, 0, 0, 0));
    assert_eq!(
        dt.round((Unit::Minute, 15))?,
        date(1976, 11, 18).at(14, 30, 0, 0)
    );
    assert_eq!(
        dt.round((Unit::Second, 30))?,
        date(1976, 11, 18).at(14, 23, 30, 0)
    );
    assert_eq!(
        dt.round((Unit::Millisecond, 10))?,
        date(1976, 11, 18).at(14, 23, 30, 120_000_000)
    );
    assert_eq!(
        dt.round((Unit::Microsecond, 10))?,
        date(1976, 11, 18).at(14, 23, 30, 123_460_000)
    );
    assert_eq!(
        dt.round((Unit::Nanosecond, 10))?,
        date(1976, 11, 18).at(14, 23, 30, 123_456_790)
    );

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/round/roundingmode-ceil.js
#[test]
fn roundingmode_ceil() -> Result {
    let dt = date(1976, 11, 18).at(14, 23, 30, 123_987_500);

    let mode = RoundMode::Ceil;
    let expected = [
        (Unit::Day, date(1976, 11, 19).at(0, 0, 0, 0)),
        (Unit::Hour, date(1976, 11, 18).at(15, 0, 0, 0)),
        (Unit::Minute, date(1976, 11, 18).at(14, 24, 0, 0)),
        (Unit::Second, date(1976, 11, 18).at(14, 23, 31, 0)),
        (Unit::Millisecond, date(1976, 11, 18).at(14, 23, 30, 124_000_000)),
        (Unit::Microsecond, date(1976, 11, 18).at(14, 23, 30, 123_988_000)),
        (Unit::Nanosecond, date(1976, 11, 18).at(14, 23, 30, 123_987_500)),
    ];
    for (unit, expected) in expected {
        let args = DateTimeRound::new().smallest(unit).mode(mode);
        assert_eq!(dt.round(args)?, expected);
    }

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/round/roundingmode-expand.js
#[test]
fn roundingmode_expand() -> Result {
    let dt = date(1976, 11, 18).at(14, 23, 30, 123_987_500);

    let mode = RoundMode::Expand;
    let expected = [
        (Unit::Day, date(1976, 11, 19).at(0, 0, 0, 0)),
        (Unit::Hour, date(1976, 11, 18).at(15, 0, 0, 0)),
        (Unit::Minute, date(1976, 11, 18).at(14, 24, 0, 0)),
        (Unit::Second, date(1976, 11, 18).at(14, 23, 31, 0)),
        (Unit::Millisecond, date(1976, 11, 18).at(14, 23, 30, 124_000_000)),
        (Unit::Microsecond, date(1976, 11, 18).at(14, 23, 30, 123_988_000)),
        (Unit::Nanosecond, date(1976, 11, 18).at(14, 23, 30, 123_987_500)),
    ];
    for (unit, expected) in expected {
        let args = DateTimeRound::new().smallest(unit).mode(mode);
        assert_eq!(dt.round(args)?, expected);
    }

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/round/roundingmode-floor.js
#[test]
fn roundingmode_floor() -> Result {
    let dt = date(1976, 11, 18).at(14, 23, 30, 123_987_500);

    let mode = RoundMode::Floor;
    let expected = [
        (Unit::Day, date(1976, 11, 18).at(0, 0, 0, 0)),
        (Unit::Hour, date(1976, 11, 18).at(14, 0, 0, 0)),
        (Unit::Minute, date(1976, 11, 18).at(14, 23, 0, 0)),
        (Unit::Second, date(1976, 11, 18).at(14, 23, 30, 0)),
        (Unit::Millisecond, date(1976, 11, 18).at(14, 23, 30, 123_000_000)),
        (Unit::Microsecond, date(1976, 11, 18).at(14, 23, 30, 123_987_000)),
        (Unit::Nanosecond, date(1976, 11, 18).at(14, 23, 30, 123_987_500)),
    ];
    for (unit, expected) in expected {
        let args = DateTimeRound::new().smallest(unit).mode(mode);
        assert_eq!(dt.round(args)?, expected);
    }

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/round/roundingmode-halfCeil.js
#[test]
fn roundingmode_halfceil() -> Result {
    let dt = date(1976, 11, 18).at(14, 23, 30, 123_987_500);

    let mode = RoundMode::HalfCeil;
    let expected = [
        (Unit::Day, date(1976, 11, 19).at(0, 0, 0, 0)),
        (Unit::Hour, date(1976, 11, 18).at(14, 0, 0, 0)),
        (Unit::Minute, date(1976, 11, 18).at(14, 24, 0, 0)),
        (Unit::Second, date(1976, 11, 18).at(14, 23, 30, 0)),
        (Unit::Millisecond, date(1976, 11, 18).at(14, 23, 30, 124_000_000)),
        (Unit::Microsecond, date(1976, 11, 18).at(14, 23, 30, 123_988_000)),
        (Unit::Nanosecond, date(1976, 11, 18).at(14, 23, 30, 123_987_500)),
    ];
    for (unit, expected) in expected {
        let args = DateTimeRound::new().smallest(unit).mode(mode);
        assert_eq!(dt.round(args)?, expected);
    }

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/round/roundingmode-halfEven.js
#[test]
fn roundingmode_halfeven() -> Result {
    let dt = date(1976, 11, 18).at(14, 23, 30, 123_987_500);

    let mode = RoundMode::HalfEven;
    let expected = [
        (Unit::Day, date(1976, 11, 19).at(0, 0, 0, 0)),
        (Unit::Hour, date(1976, 11, 18).at(14, 0, 0, 0)),
        (Unit::Minute, date(1976, 11, 18).at(14, 24, 0, 0)),
        (Unit::Second, date(1976, 11, 18).at(14, 23, 30, 0)),
        (Unit::Millisecond, date(1976, 11, 18).at(14, 23, 30, 124_000_000)),
        (Unit::Microsecond, date(1976, 11, 18).at(14, 23, 30, 123_988_000)),
        (Unit::Nanosecond, date(1976, 11, 18).at(14, 23, 30, 123_987_500)),
    ];
    for (unit, expected) in expected {
        let args = DateTimeRound::new().smallest(unit).mode(mode);
        assert_eq!(dt.round(args)?, expected);
    }

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/round/roundingmode-halfExpand.js
#[test]
fn roundingmode_halfexpand() -> Result {
    let dt = date(1976, 11, 18).at(14, 23, 30, 123_987_500);

    let mode = RoundMode::HalfExpand;
    let expected = [
        (Unit::Day, date(1976, 11, 19).at(0, 0, 0, 0)),
        (Unit::Hour, date(1976, 11, 18).at(14, 0, 0, 0)),
        (Unit::Minute, date(1976, 11, 18).at(14, 24, 0, 0)),
        (Unit::Second, date(1976, 11, 18).at(14, 23, 30, 0)),
        (Unit::Millisecond, date(1976, 11, 18).at(14, 23, 30, 124_000_000)),
        (Unit::Microsecond, date(1976, 11, 18).at(14, 23, 30, 123_988_000)),
        (Unit::Nanosecond, date(1976, 11, 18).at(14, 23, 30, 123_987_500)),
    ];
    for (unit, expected) in expected {
        let args = DateTimeRound::new().smallest(unit).mode(mode);
        assert_eq!(dt.round(args)?, expected);
    }

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/round/roundingmode-halfFloor.js
#[test]
fn roundingmode_halffloor() -> Result {
    let dt = date(1976, 11, 18).at(14, 23, 30, 123_987_500);

    let mode = RoundMode::HalfFloor;
    let expected = [
        (Unit::Day, date(1976, 11, 19).at(0, 0, 0, 0)),
        (Unit::Hour, date(1976, 11, 18).at(14, 0, 0, 0)),
        (Unit::Minute, date(1976, 11, 18).at(14, 24, 0, 0)),
        (Unit::Second, date(1976, 11, 18).at(14, 23, 30, 0)),
        (Unit::Millisecond, date(1976, 11, 18).at(14, 23, 30, 124_000_000)),
        (Unit::Microsecond, date(1976, 11, 18).at(14, 23, 30, 123_987_000)),
        (Unit::Nanosecond, date(1976, 11, 18).at(14, 23, 30, 123_987_500)),
    ];
    for (unit, expected) in expected {
        let args = DateTimeRound::new().smallest(unit).mode(mode);
        assert_eq!(dt.round(args)?, expected);
    }

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/round/roundingmode-halfTrunc.js
#[test]
fn roundingmode_halftrunc() -> Result {
    let dt = date(1976, 11, 18).at(14, 23, 30, 123_987_500);

    let mode = RoundMode::HalfTrunc;
    let expected = [
        (Unit::Day, date(1976, 11, 19).at(0, 0, 0, 0)),
        (Unit::Hour, date(1976, 11, 18).at(14, 0, 0, 0)),
        (Unit::Minute, date(1976, 11, 18).at(14, 24, 0, 0)),
        (Unit::Second, date(1976, 11, 18).at(14, 23, 30, 0)),
        (Unit::Millisecond, date(1976, 11, 18).at(14, 23, 30, 124_000_000)),
        (Unit::Microsecond, date(1976, 11, 18).at(14, 23, 30, 123_987_000)),
        (Unit::Nanosecond, date(1976, 11, 18).at(14, 23, 30, 123_987_500)),
    ];
    for (unit, expected) in expected {
        let args = DateTimeRound::new().smallest(unit).mode(mode);
        assert_eq!(dt.round(args)?, expected);
    }

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/round/roundingmode-halfexpand-is-default.js
#[test]
fn roundingmode_halfexpand_is_default() -> Result {
    let dt = date(1976, 11, 18).at(14, 23, 30, 123_456_789);

    let expected = [
        (Unit::Day, date(1976, 11, 19).at(0, 0, 0, 0)),
        (Unit::Hour, date(1976, 11, 18).at(14, 0, 0, 0)),
        (Unit::Minute, date(1976, 11, 18).at(14, 24, 0, 0)),
        (Unit::Second, date(1976, 11, 18).at(14, 23, 30, 0)),
        (Unit::Millisecond, date(1976, 11, 18).at(14, 23, 30, 123_000_000)),
        (Unit::Microsecond, date(1976, 11, 18).at(14, 23, 30, 123_457_000)),
        (Unit::Nanosecond, date(1976, 11, 18).at(14, 23, 30, 123_456_789)),
    ];
    for (unit, expected) in expected {
        assert_eq!(dt.round(unit)?, expected);
    }

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/round/roundingmode-trunc.js
#[test]
fn roundingmode_trunc() -> Result {
    let dt = date(1976, 11, 18).at(14, 23, 30, 123_987_500);

    let mode = RoundMode::Trunc;
    let expected = [
        (Unit::Day, date(1976, 11, 18).at(0, 0, 0, 0)),
        (Unit::Hour, date(1976, 11, 18).at(14, 0, 0, 0)),
        (Unit::Minute, date(1976, 11, 18).at(14, 23, 0, 0)),
        (Unit::Second, date(1976, 11, 18).at(14, 23, 30, 0)),
        (Unit::Millisecond, date(1976, 11, 18).at(14, 23, 30, 123_000_000)),
        (Unit::Microsecond, date(1976, 11, 18).at(14, 23, 30, 123_987_000)),
        (Unit::Nanosecond, date(1976, 11, 18).at(14, 23, 30, 123_987_500)),
    ];
    for (unit, expected) in expected {
        let args = DateTimeRound::new().smallest(unit).mode(mode);
        assert_eq!(dt.round(args)?, expected);
    }

    Ok(())
}
