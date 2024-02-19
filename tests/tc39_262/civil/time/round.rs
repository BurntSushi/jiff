use jiff::{
    civil::Time,
    round::{Round, RoundMode, Unit},
};

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/rounding-cross-midnight.js
#[test]
fn rounding_cross_midnight() {
    let t1 = Time::constant(23, 59, 59, 999_999_999);

    let t2 = t1.round(Unit::Nanosecond);
    assert_eq!(t2, t1);

    let t2 = t1.round(Unit::Millisecond);
    assert_eq!(t2, Time::constant(0, 0, 0, 0));

    let t2 = t1.round(Unit::Microsecond);
    assert_eq!(t2, Time::constant(0, 0, 0, 0));

    let t2 = t1.round(Unit::Millisecond);
    assert_eq!(t2, Time::constant(0, 0, 0, 0));

    let t2 = t1.round(Unit::Second);
    assert_eq!(t2, Time::constant(0, 0, 0, 0));

    let t2 = t1.round(Unit::Minute);
    assert_eq!(t2, Time::constant(0, 0, 0, 0));

    let t2 = t1.round(Unit::Hour);
    assert_eq!(t2, Time::constant(0, 0, 0, 0));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingincrement-hours.js
#[test]
fn rounding_increment_hours() {
    let t1 = Time::constant(3, 34, 56, 987_654_321);

    let t2 = t1.round(Unit::Hour.increment(1));
    assert_eq!(t2, Time::constant(4, 0, 0, 0));

    let t2 = t1.round(Unit::Hour.increment(2));
    assert_eq!(t2, Time::constant(4, 0, 0, 0));

    let t2 = t1.round(Unit::Hour.increment(3));
    assert_eq!(t2, Time::constant(3, 0, 0, 0));

    let t2 = t1.round(Unit::Hour.increment(4));
    assert_eq!(t2, Time::constant(4, 0, 0, 0));

    let t2 = t1.round(Unit::Hour.increment(6));
    assert_eq!(t2, Time::constant(6, 0, 0, 0));

    let t2 = t1.round(Unit::Hour.increment(8));
    assert_eq!(t2, Time::constant(0, 0, 0, 0));

    let t2 = t1.round(Unit::Hour.increment(12));
    assert_eq!(t2, Time::constant(0, 0, 0, 0));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingincrement-minutes.js
#[test]
fn rounding_increment_minutes() {
    let t1 = Time::constant(3, 34, 56, 987_654_321);

    let t2 = t1.round(Unit::Minute.increment(1));
    assert_eq!(t2, Time::constant(3, 35, 0, 0));

    let t2 = t1.round(Unit::Minute.increment(2));
    assert_eq!(t2, Time::constant(3, 34, 0, 0));

    let t2 = t1.round(Unit::Minute.increment(3));
    assert_eq!(t2, Time::constant(3, 36, 0, 0));

    let t2 = t1.round(Unit::Minute.increment(4));
    assert_eq!(t2, Time::constant(3, 36, 0, 0));

    let t2 = t1.round(Unit::Minute.increment(5));
    assert_eq!(t2, Time::constant(3, 35, 0, 0));

    let t2 = t1.round(Unit::Minute.increment(6));
    assert_eq!(t2, Time::constant(3, 36, 0, 0));

    let t2 = t1.round(Unit::Minute.increment(10));
    assert_eq!(t2, Time::constant(3, 30, 0, 0));

    let t2 = t1.round(Unit::Minute.increment(12));
    assert_eq!(t2, Time::constant(3, 36, 0, 0));

    let t2 = t1.round(Unit::Minute.increment(15));
    assert_eq!(t2, Time::constant(3, 30, 0, 0));

    let t2 = t1.round(Unit::Minute.increment(20));
    assert_eq!(t2, Time::constant(3, 40, 0, 0));

    let t2 = t1.round(Unit::Minute.increment(30));
    assert_eq!(t2, Time::constant(3, 30, 0, 0));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingincrement-seconds.js
#[test]
fn rounding_increment_seconds() {
    let t1 = Time::constant(3, 34, 56, 987_654_321);

    let t2 = t1.round(Unit::Second.increment(1));
    assert_eq!(t2, Time::constant(3, 34, 57, 0));

    let t2 = t1.round(Unit::Second.increment(2));
    assert_eq!(t2, Time::constant(3, 34, 56, 0));

    let t2 = t1.round(Unit::Second.increment(3));
    assert_eq!(t2, Time::constant(3, 34, 57, 0));

    let t2 = t1.round(Unit::Second.increment(4));
    assert_eq!(t2, Time::constant(3, 34, 56, 0));

    let t2 = t1.round(Unit::Second.increment(5));
    assert_eq!(t2, Time::constant(3, 34, 55, 0));

    let t2 = t1.round(Unit::Second.increment(6));
    assert_eq!(t2, Time::constant(3, 34, 54, 0));

    let t2 = t1.round(Unit::Second.increment(10));
    assert_eq!(t2, Time::constant(3, 35, 0, 0));

    let t2 = t1.round(Unit::Second.increment(12));
    assert_eq!(t2, Time::constant(3, 35, 0, 0));

    let t2 = t1.round(Unit::Second.increment(15));
    assert_eq!(t2, Time::constant(3, 35, 0, 0));

    let t2 = t1.round(Unit::Second.increment(20));
    assert_eq!(t2, Time::constant(3, 35, 0, 0));

    let t2 = t1.round(Unit::Second.increment(30));
    assert_eq!(t2, Time::constant(3, 35, 0, 0));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingincrement-milliseconds.js
#[test]
fn rounding_increment_milliseconds() {
    let t1 = Time::constant(3, 34, 56, 987_654_321);

    let t2 = t1.round(Unit::Millisecond.increment(1));
    assert_eq!(t2, Time::constant(3, 34, 56, 988_000_000));

    let t2 = t1.round(Unit::Millisecond.increment(2));
    assert_eq!(t2, Time::constant(3, 34, 56, 988_000_000));

    let t2 = t1.round(Unit::Millisecond.increment(4));
    assert_eq!(t2, Time::constant(3, 34, 56, 988_000_000));

    let t2 = t1.round(Unit::Millisecond.increment(5));
    assert_eq!(t2, Time::constant(3, 34, 56, 990_000_000));

    let t2 = t1.round(Unit::Millisecond.increment(8));
    assert_eq!(t2, Time::constant(3, 34, 56, 984_000_000));

    let t2 = t1.round(Unit::Millisecond.increment(10));
    assert_eq!(t2, Time::constant(3, 34, 56, 990_000_000));

    let t2 = t1.round(Unit::Millisecond.increment(20));
    assert_eq!(t2, Time::constant(3, 34, 56, 980_000_000));

    let t2 = t1.round(Unit::Millisecond.increment(25));
    assert_eq!(t2, Time::constant(3, 34, 57, 0));

    let t2 = t1.round(Unit::Millisecond.increment(40));
    assert_eq!(t2, Time::constant(3, 34, 57, 0));

    let t2 = t1.round(Unit::Millisecond.increment(50));
    assert_eq!(t2, Time::constant(3, 34, 57, 0));

    let t2 = t1.round(Unit::Millisecond.increment(100));
    assert_eq!(t2, Time::constant(3, 34, 57, 0));

    let t2 = t1.round(Unit::Millisecond.increment(125));
    assert_eq!(t2, Time::constant(3, 34, 57, 0));

    let t2 = t1.round(Unit::Millisecond.increment(200));
    assert_eq!(t2, Time::constant(3, 34, 57, 0));

    let t2 = t1.round(Unit::Millisecond.increment(250));
    assert_eq!(t2, Time::constant(3, 34, 57, 0));

    let t2 = t1.round(Unit::Millisecond.increment(500));
    assert_eq!(t2, Time::constant(3, 34, 57, 0));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingincrement-microseconds.js
#[test]
fn rounding_increment_microseconds() {
    let t1 = Time::constant(3, 34, 56, 987_654_321);

    let t2 = t1.round(Unit::Microsecond.increment(1));
    assert_eq!(t2, Time::constant(3, 34, 56, 987_654_000));

    let t2 = t1.round(Unit::Microsecond.increment(2));
    assert_eq!(t2, Time::constant(3, 34, 56, 987_654_000));

    let t2 = t1.round(Unit::Microsecond.increment(4));
    assert_eq!(t2, Time::constant(3, 34, 56, 987_656_000));

    let t2 = t1.round(Unit::Microsecond.increment(5));
    assert_eq!(t2, Time::constant(3, 34, 56, 987_655_000));

    let t2 = t1.round(Unit::Microsecond.increment(8));
    assert_eq!(t2, Time::constant(3, 34, 56, 987_656_000));

    let t2 = t1.round(Unit::Microsecond.increment(10));
    assert_eq!(t2, Time::constant(3, 34, 56, 987_650_000));

    let t2 = t1.round(Unit::Microsecond.increment(20));
    assert_eq!(t2, Time::constant(3, 34, 56, 987_660_000));

    let t2 = t1.round(Unit::Microsecond.increment(25));
    assert_eq!(t2, Time::constant(3, 34, 56, 987_650_000));

    let t2 = t1.round(Unit::Microsecond.increment(40));
    assert_eq!(t2, Time::constant(3, 34, 56, 987_640_000));

    let t2 = t1.round(Unit::Microsecond.increment(50));
    assert_eq!(t2, Time::constant(3, 34, 56, 987_650_000));

    let t2 = t1.round(Unit::Microsecond.increment(100));
    assert_eq!(t2, Time::constant(3, 34, 56, 987_700_000));

    let t2 = t1.round(Unit::Microsecond.increment(125));
    assert_eq!(t2, Time::constant(3, 34, 56, 987_625_000));

    let t2 = t1.round(Unit::Microsecond.increment(200));
    assert_eq!(t2, Time::constant(3, 34, 56, 987_600_000));

    let t2 = t1.round(Unit::Microsecond.increment(250));
    assert_eq!(t2, Time::constant(3, 34, 56, 987_750_000));

    let t2 = t1.round(Unit::Microsecond.increment(500));
    assert_eq!(t2, Time::constant(3, 34, 56, 987_500_000));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingincrement-nanoseconds.js
#[test]
fn rounding_increment_nanoseconds() {
    let t1 = Time::constant(3, 34, 56, 987_654_321);

    let t2 = t1.round(Unit::Nanosecond.increment(1));
    assert_eq!(t2, Time::constant(3, 34, 56, 987_654_321));

    let t2 = t1.round(Unit::Nanosecond.increment(2));
    assert_eq!(t2, Time::constant(3, 34, 56, 987_654_322));

    let t2 = t1.round(Unit::Nanosecond.increment(4));
    assert_eq!(t2, Time::constant(3, 34, 56, 987_654_320));

    let t2 = t1.round(Unit::Nanosecond.increment(5));
    assert_eq!(t2, Time::constant(3, 34, 56, 987_654_320));

    let t2 = t1.round(Unit::Nanosecond.increment(8));
    assert_eq!(t2, Time::constant(3, 34, 56, 987_654_320));

    let t2 = t1.round(Unit::Nanosecond.increment(10));
    assert_eq!(t2, Time::constant(3, 34, 56, 987_654_320));

    let t2 = t1.round(Unit::Nanosecond.increment(20));
    assert_eq!(t2, Time::constant(3, 34, 56, 987_654_320));

    let t2 = t1.round(Unit::Nanosecond.increment(25));
    assert_eq!(t2, Time::constant(3, 34, 56, 987_654_325));

    let t2 = t1.round(Unit::Nanosecond.increment(40));
    assert_eq!(t2, Time::constant(3, 34, 56, 987_654_320));

    let t2 = t1.round(Unit::Nanosecond.increment(50));
    assert_eq!(t2, Time::constant(3, 34, 56, 987_654_300));

    let t2 = t1.round(Unit::Nanosecond.increment(100));
    assert_eq!(t2, Time::constant(3, 34, 56, 987_654_300));

    let t2 = t1.round(Unit::Nanosecond.increment(125));
    assert_eq!(t2, Time::constant(3, 34, 56, 987_654_375));

    let t2 = t1.round(Unit::Nanosecond.increment(200));
    assert_eq!(t2, Time::constant(3, 34, 56, 987_654_400));

    let t2 = t1.round(Unit::Nanosecond.increment(250));
    assert_eq!(t2, Time::constant(3, 34, 56, 987_654_250));

    let t2 = t1.round(Unit::Nanosecond.increment(500));
    assert_eq!(t2, Time::constant(3, 34, 56, 987_654_500));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingincrement-invalid.js
#[test]
fn rounding_increment_invalid() {
    let t1 = Time::constant(8, 22, 36, 123456789);

    assert!(t1.try_round(Unit::Hour.increment(11)).is_err());
    assert!(t1.try_round(Unit::Minute.increment(29)).is_err());
    assert!(t1.try_round(Unit::Second.increment(29)).is_err());
    assert!(t1.try_round(Unit::Millisecond.increment(29)).is_err());
    assert!(t1.try_round(Unit::Microsecond.increment(29)).is_err());
    assert!(t1.try_round(Unit::Nanosecond.increment(29)).is_err());

    assert!(t1.try_round(Unit::Hour.increment(24)).is_err());
    assert!(t1.try_round(Unit::Minute.increment(60)).is_err());
    assert!(t1.try_round(Unit::Second.increment(60)).is_err());
    assert!(t1.try_round(Unit::Millisecond.increment(1_000)).is_err());
    assert!(t1.try_round(Unit::Microsecond.increment(1_000)).is_err());
    assert!(t1.try_round(Unit::Nanosecond.increment(1_000)).is_err());
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingincrement-out-of-range.js
#[test]
fn rounding_increment_out_of_range() {
    let t1 = Time::constant(12, 34, 56, 000_000_005);

    assert!(t1.try_round(Unit::Nanosecond.increment(-1)).is_err());
    assert!(t1.try_round(Unit::Nanosecond.increment(0)).is_err());
    assert!(t1.try_round(Unit::Nanosecond.increment(1_000)).is_err());
    assert!(t1.try_round(Unit::Nanosecond.increment(1_000_000_001)).is_err());
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingmode-ceil.js
#[test]
fn rounding_mode_ceil() {
    let t1 = Time::constant(13, 46, 23, 123_987_500);

    let t2 = t1.round(Unit::Hour.mode(RoundMode::Ceil));
    assert_eq!(t2, Time::constant(14, 0, 0, 0));

    let t2 = t1.round(Unit::Minute.mode(RoundMode::Ceil));
    assert_eq!(t2, Time::constant(13, 47, 0, 0));

    let t2 = t1.round(Unit::Second.mode(RoundMode::Ceil));
    assert_eq!(t2, Time::constant(13, 46, 24, 0));

    let t2 = t1.round(Unit::Millisecond.mode(RoundMode::Ceil));
    assert_eq!(t2, Time::constant(13, 46, 23, 124_000_000));

    let t2 = t1.round(Unit::Microsecond.mode(RoundMode::Ceil));
    assert_eq!(t2, Time::constant(13, 46, 23, 123_988_000));

    let t2 = t1.round(Unit::Nanosecond.mode(RoundMode::Ceil));
    assert_eq!(t2, Time::constant(13, 46, 23, 123_987_500));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingmode-expand.js
#[test]
fn rounding_mode_expand() {
    let t1 = Time::constant(13, 46, 23, 123_987_500);

    let t2 = t1.round(Unit::Hour.mode(RoundMode::Expand));
    assert_eq!(t2, Time::constant(14, 0, 0, 0));

    let t2 = t1.round(Unit::Minute.mode(RoundMode::Expand));
    assert_eq!(t2, Time::constant(13, 47, 0, 0));

    let t2 = t1.round(Unit::Second.mode(RoundMode::Expand));
    assert_eq!(t2, Time::constant(13, 46, 24, 0));

    let t2 = t1.round(Unit::Millisecond.mode(RoundMode::Expand));
    assert_eq!(t2, Time::constant(13, 46, 23, 124_000_000));

    let t2 = t1.round(Unit::Microsecond.mode(RoundMode::Expand));
    assert_eq!(t2, Time::constant(13, 46, 23, 123_988_000));

    let t2 = t1.round(Unit::Nanosecond.mode(RoundMode::Expand));
    assert_eq!(t2, Time::constant(13, 46, 23, 123_987_500));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingmode-floor.js
#[test]
fn rounding_mode_floor() {
    let t1 = Time::constant(13, 46, 23, 123_987_500);

    let t2 = t1.round(Unit::Hour.mode(RoundMode::Floor));
    assert_eq!(t2, Time::constant(13, 0, 0, 0));

    let t2 = t1.round(Unit::Minute.mode(RoundMode::Floor));
    assert_eq!(t2, Time::constant(13, 46, 0, 0));

    let t2 = t1.round(Unit::Second.mode(RoundMode::Floor));
    assert_eq!(t2, Time::constant(13, 46, 23, 0));

    let t2 = t1.round(Unit::Millisecond.mode(RoundMode::Floor));
    assert_eq!(t2, Time::constant(13, 46, 23, 123_000_000));

    let t2 = t1.round(Unit::Microsecond.mode(RoundMode::Floor));
    assert_eq!(t2, Time::constant(13, 46, 23, 123_987_000));

    let t2 = t1.round(Unit::Nanosecond.mode(RoundMode::Floor));
    assert_eq!(t2, Time::constant(13, 46, 23, 123_987_500));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingmode-halfCeil.js
#[test]
fn rounding_mode_half_ceil() {
    let t1 = Time::constant(13, 46, 23, 123_987_500);

    let t2 = t1.round(Unit::Hour.mode(RoundMode::HalfCeil));
    assert_eq!(t2, Time::constant(14, 0, 0, 0));

    let t2 = t1.round(Unit::Minute.mode(RoundMode::HalfCeil));
    assert_eq!(t2, Time::constant(13, 46, 0, 0));

    let t2 = t1.round(Unit::Second.mode(RoundMode::HalfCeil));
    assert_eq!(t2, Time::constant(13, 46, 23, 0));

    let t2 = t1.round(Unit::Millisecond.mode(RoundMode::HalfCeil));
    assert_eq!(t2, Time::constant(13, 46, 23, 124_000_000));

    let t2 = t1.round(Unit::Microsecond.mode(RoundMode::HalfCeil));
    assert_eq!(t2, Time::constant(13, 46, 23, 123_988_000));

    let t2 = t1.round(Unit::Nanosecond.mode(RoundMode::HalfCeil));
    assert_eq!(t2, Time::constant(13, 46, 23, 123_987_500));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingmode-halfEven.js
#[test]
fn rounding_mode_half_even() {
    let t1 = Time::constant(13, 46, 23, 123_987_500);

    let t2 = t1.round(Unit::Hour.mode(RoundMode::HalfEven));
    assert_eq!(t2, Time::constant(14, 0, 0, 0));

    let t2 = t1.round(Unit::Minute.mode(RoundMode::HalfEven));
    assert_eq!(t2, Time::constant(13, 46, 0, 0));

    let t2 = t1.round(Unit::Second.mode(RoundMode::HalfEven));
    assert_eq!(t2, Time::constant(13, 46, 23, 0));

    let t2 = t1.round(Unit::Millisecond.mode(RoundMode::HalfEven));
    assert_eq!(t2, Time::constant(13, 46, 23, 124_000_000));

    let t2 = t1.round(Unit::Microsecond.mode(RoundMode::HalfEven));
    assert_eq!(t2, Time::constant(13, 46, 23, 123_988_000));

    let t2 = t1.round(Unit::Nanosecond.mode(RoundMode::HalfEven));
    assert_eq!(t2, Time::constant(13, 46, 23, 123_987_500));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingmode-halfExpand.js
#[test]
fn rounding_mode_half_expand() {
    let t1 = Time::constant(13, 46, 23, 123_987_500);

    let t2 = t1.round(Unit::Hour.mode(RoundMode::HalfExpand));
    assert_eq!(t2, Time::constant(14, 0, 0, 0));

    let t2 = t1.round(Unit::Minute.mode(RoundMode::HalfExpand));
    assert_eq!(t2, Time::constant(13, 46, 0, 0));

    let t2 = t1.round(Unit::Second.mode(RoundMode::HalfExpand));
    assert_eq!(t2, Time::constant(13, 46, 23, 0));

    let t2 = t1.round(Unit::Millisecond.mode(RoundMode::HalfExpand));
    assert_eq!(t2, Time::constant(13, 46, 23, 124_000_000));

    let t2 = t1.round(Unit::Microsecond.mode(RoundMode::HalfExpand));
    assert_eq!(t2, Time::constant(13, 46, 23, 123_988_000));

    let t2 = t1.round(Unit::Nanosecond.mode(RoundMode::HalfExpand));
    assert_eq!(t2, Time::constant(13, 46, 23, 123_987_500));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingmode-halfFloor.js
#[test]
fn rounding_mode_half_floor() {
    let t1 = Time::constant(13, 46, 23, 123_987_500);

    let t2 = t1.round(Unit::Hour.mode(RoundMode::HalfFloor));
    assert_eq!(t2, Time::constant(14, 0, 0, 0));

    let t2 = t1.round(Unit::Minute.mode(RoundMode::HalfFloor));
    assert_eq!(t2, Time::constant(13, 46, 0, 0));

    let t2 = t1.round(Unit::Second.mode(RoundMode::HalfFloor));
    assert_eq!(t2, Time::constant(13, 46, 23, 0));

    let t2 = t1.round(Unit::Millisecond.mode(RoundMode::HalfFloor));
    assert_eq!(t2, Time::constant(13, 46, 23, 124_000_000));

    let t2 = t1.round(Unit::Microsecond.mode(RoundMode::HalfFloor));
    assert_eq!(t2, Time::constant(13, 46, 23, 123_987_000));

    let t2 = t1.round(Unit::Nanosecond.mode(RoundMode::HalfFloor));
    assert_eq!(t2, Time::constant(13, 46, 23, 123_987_500));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingmode-halfTrunc.js
#[test]
fn rounding_mode_half_trunc() {
    let t1 = Time::constant(13, 46, 23, 123_987_500);

    let t2 = t1.round(Unit::Hour.mode(RoundMode::HalfTrunc));
    assert_eq!(t2, Time::constant(14, 0, 0, 0));

    let t2 = t1.round(Unit::Minute.mode(RoundMode::HalfTrunc));
    assert_eq!(t2, Time::constant(13, 46, 0, 0));

    let t2 = t1.round(Unit::Second.mode(RoundMode::HalfTrunc));
    assert_eq!(t2, Time::constant(13, 46, 23, 0));

    let t2 = t1.round(Unit::Millisecond.mode(RoundMode::HalfTrunc));
    assert_eq!(t2, Time::constant(13, 46, 23, 124_000_000));

    let t2 = t1.round(Unit::Microsecond.mode(RoundMode::HalfTrunc));
    assert_eq!(t2, Time::constant(13, 46, 23, 123_987_000));

    let t2 = t1.round(Unit::Nanosecond.mode(RoundMode::HalfTrunc));
    assert_eq!(t2, Time::constant(13, 46, 23, 123_987_500));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingmode-trunc.js
#[test]
fn rounding_mode_trunc() {
    let t1 = Time::constant(13, 46, 23, 123_987_500);

    let t2 = t1.round(Unit::Hour.mode(RoundMode::Trunc));
    assert_eq!(t2, Time::constant(13, 0, 0, 0));

    let t2 = t1.round(Unit::Minute.mode(RoundMode::Trunc));
    assert_eq!(t2, Time::constant(13, 46, 0, 0));

    let t2 = t1.round(Unit::Second.mode(RoundMode::Trunc));
    assert_eq!(t2, Time::constant(13, 46, 23, 0));

    let t2 = t1.round(Unit::Millisecond.mode(RoundMode::Trunc));
    assert_eq!(t2, Time::constant(13, 46, 23, 123_000_000));

    let t2 = t1.round(Unit::Microsecond.mode(RoundMode::Trunc));
    assert_eq!(t2, Time::constant(13, 46, 23, 123_987_000));

    let t2 = t1.round(Unit::Nanosecond.mode(RoundMode::Trunc));
    assert_eq!(t2, Time::constant(13, 46, 23, 123_987_500));
}

/// DIFFERENCE: Unlike Temporal, we permit the smallest unit to be missing. It
/// defaults to `Nanosecond`.
///
/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/smallestunit-missing.js
#[test]
fn smallest_unit_missing() {
    let t1 = Time::constant(13, 46, 23, 123_987_499);

    let t2 = t1.round(Round::new());
    assert_eq!(t2, t1);

    let t2 = t1.round(Round::new().increment(500));
    assert_eq!(t2, Time::constant(13, 46, 23, 123_987_500));
}
