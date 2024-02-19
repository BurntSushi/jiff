use jiff::{
    civil::{time, TimeRound},
    RoundMode, Unit,
};

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/rounding-cross-midnight.js
#[test]
fn rounding_cross_midnight() {
    let t1 = time(23, 59, 59, 999_999_999);

    let t2 = t1.round(Unit::Nanosecond).unwrap();
    assert_eq!(t2, t1);

    let t2 = t1.round(Unit::Millisecond).unwrap();
    assert_eq!(t2, time(0, 0, 0, 0));

    let t2 = t1.round(Unit::Microsecond).unwrap();
    assert_eq!(t2, time(0, 0, 0, 0));

    let t2 = t1.round(Unit::Millisecond).unwrap();
    assert_eq!(t2, time(0, 0, 0, 0));

    let t2 = t1.round(Unit::Second).unwrap();
    assert_eq!(t2, time(0, 0, 0, 0));

    let t2 = t1.round(Unit::Minute).unwrap();
    assert_eq!(t2, time(0, 0, 0, 0));

    let t2 = t1.round(Unit::Hour).unwrap();
    assert_eq!(t2, time(0, 0, 0, 0));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingincrement-hours.js
#[test]
fn rounding_increment_hours() {
    let t1 = time(3, 34, 56, 987_654_321);

    let t2 = t1.round((Unit::Hour, 1)).unwrap();
    assert_eq!(t2, time(4, 0, 0, 0));

    let t2 = t1.round((Unit::Hour, 2)).unwrap();
    assert_eq!(t2, time(4, 0, 0, 0));

    let t2 = t1.round((Unit::Hour, 3)).unwrap();
    assert_eq!(t2, time(3, 0, 0, 0));

    let t2 = t1.round((Unit::Hour, 4)).unwrap();
    assert_eq!(t2, time(4, 0, 0, 0));

    let t2 = t1.round((Unit::Hour, 6)).unwrap();
    assert_eq!(t2, time(6, 0, 0, 0));

    let t2 = t1.round((Unit::Hour, 8)).unwrap();
    assert_eq!(t2, time(0, 0, 0, 0));

    let t2 = t1.round((Unit::Hour, 12)).unwrap();
    assert_eq!(t2, time(0, 0, 0, 0));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingincrement-minutes.js
#[test]
fn rounding_increment_minutes() {
    let t1 = time(3, 34, 56, 987_654_321);

    let t2 = t1.round((Unit::Minute, 1)).unwrap();
    assert_eq!(t2, time(3, 35, 0, 0));

    let t2 = t1.round((Unit::Minute, 2)).unwrap();
    assert_eq!(t2, time(3, 34, 0, 0));

    let t2 = t1.round((Unit::Minute, 3)).unwrap();
    assert_eq!(t2, time(3, 36, 0, 0));

    let t2 = t1.round((Unit::Minute, 4)).unwrap();
    assert_eq!(t2, time(3, 36, 0, 0));

    let t2 = t1.round((Unit::Minute, 5)).unwrap();
    assert_eq!(t2, time(3, 35, 0, 0));

    let t2 = t1.round((Unit::Minute, 6)).unwrap();
    assert_eq!(t2, time(3, 36, 0, 0));

    let t2 = t1.round((Unit::Minute, 10)).unwrap();
    assert_eq!(t2, time(3, 30, 0, 0));

    let t2 = t1.round((Unit::Minute, 12)).unwrap();
    assert_eq!(t2, time(3, 36, 0, 0));

    let t2 = t1.round((Unit::Minute, 15)).unwrap();
    assert_eq!(t2, time(3, 30, 0, 0));

    let t2 = t1.round((Unit::Minute, 20)).unwrap();
    assert_eq!(t2, time(3, 40, 0, 0));

    let t2 = t1.round((Unit::Minute, 30)).unwrap();
    assert_eq!(t2, time(3, 30, 0, 0));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingincrement-seconds.js
#[test]
fn rounding_increment_seconds() {
    let t1 = time(3, 34, 56, 987_654_321);

    let t2 = t1.round((Unit::Second, 1)).unwrap();
    assert_eq!(t2, time(3, 34, 57, 0));

    let t2 = t1.round((Unit::Second, 2)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 0));

    let t2 = t1.round((Unit::Second, 3)).unwrap();
    assert_eq!(t2, time(3, 34, 57, 0));

    let t2 = t1.round((Unit::Second, 4)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 0));

    let t2 = t1.round((Unit::Second, 5)).unwrap();
    assert_eq!(t2, time(3, 34, 55, 0));

    let t2 = t1.round((Unit::Second, 6)).unwrap();
    assert_eq!(t2, time(3, 34, 54, 0));

    let t2 = t1.round((Unit::Second, 10)).unwrap();
    assert_eq!(t2, time(3, 35, 0, 0));

    let t2 = t1.round((Unit::Second, 12)).unwrap();
    assert_eq!(t2, time(3, 35, 0, 0));

    let t2 = t1.round((Unit::Second, 15)).unwrap();
    assert_eq!(t2, time(3, 35, 0, 0));

    let t2 = t1.round((Unit::Second, 20)).unwrap();
    assert_eq!(t2, time(3, 35, 0, 0));

    let t2 = t1.round((Unit::Second, 30)).unwrap();
    assert_eq!(t2, time(3, 35, 0, 0));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingincrement-milliseconds.js
#[test]
fn rounding_increment_milliseconds() {
    let t1 = time(3, 34, 56, 987_654_321);

    let t2 = t1.round((Unit::Millisecond, 1)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 988_000_000));

    let t2 = t1.round((Unit::Millisecond, 2)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 988_000_000));

    let t2 = t1.round((Unit::Millisecond, 4)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 988_000_000));

    let t2 = t1.round((Unit::Millisecond, 5)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 990_000_000));

    let t2 = t1.round((Unit::Millisecond, 8)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 984_000_000));

    let t2 = t1.round((Unit::Millisecond, 10)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 990_000_000));

    let t2 = t1.round((Unit::Millisecond, 20)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 980_000_000));

    let t2 = t1.round((Unit::Millisecond, 25)).unwrap();
    assert_eq!(t2, time(3, 34, 57, 0));

    let t2 = t1.round((Unit::Millisecond, 40)).unwrap();
    assert_eq!(t2, time(3, 34, 57, 0));

    let t2 = t1.round((Unit::Millisecond, 50)).unwrap();
    assert_eq!(t2, time(3, 34, 57, 0));

    let t2 = t1.round((Unit::Millisecond, 100)).unwrap();
    assert_eq!(t2, time(3, 34, 57, 0));

    let t2 = t1.round((Unit::Millisecond, 125)).unwrap();
    assert_eq!(t2, time(3, 34, 57, 0));

    let t2 = t1.round((Unit::Millisecond, 200)).unwrap();
    assert_eq!(t2, time(3, 34, 57, 0));

    let t2 = t1.round((Unit::Millisecond, 250)).unwrap();
    assert_eq!(t2, time(3, 34, 57, 0));

    let t2 = t1.round((Unit::Millisecond, 500)).unwrap();
    assert_eq!(t2, time(3, 34, 57, 0));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingincrement-microseconds.js
#[test]
fn rounding_increment_microseconds() {
    let t1 = time(3, 34, 56, 987_654_321);

    let t2 = t1.round((Unit::Microsecond, 1)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 987_654_000));

    let t2 = t1.round((Unit::Microsecond, 2)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 987_654_000));

    let t2 = t1.round((Unit::Microsecond, 4)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 987_656_000));

    let t2 = t1.round((Unit::Microsecond, 5)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 987_655_000));

    let t2 = t1.round((Unit::Microsecond, 8)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 987_656_000));

    let t2 = t1.round((Unit::Microsecond, 10)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 987_650_000));

    let t2 = t1.round((Unit::Microsecond, 20)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 987_660_000));

    let t2 = t1.round((Unit::Microsecond, 25)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 987_650_000));

    let t2 = t1.round((Unit::Microsecond, 40)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 987_640_000));

    let t2 = t1.round((Unit::Microsecond, 50)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 987_650_000));

    let t2 = t1.round((Unit::Microsecond, 100)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 987_700_000));

    let t2 = t1.round((Unit::Microsecond, 125)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 987_625_000));

    let t2 = t1.round((Unit::Microsecond, 200)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 987_600_000));

    let t2 = t1.round((Unit::Microsecond, 250)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 987_750_000));

    let t2 = t1.round((Unit::Microsecond, 500)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 987_500_000));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingincrement-nanoseconds.js
#[test]
fn rounding_increment_nanoseconds() {
    let t1 = time(3, 34, 56, 987_654_321);

    let t2 = t1.round((Unit::Nanosecond, 1)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 987_654_321));

    let t2 = t1.round((Unit::Nanosecond, 2)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 987_654_322));

    let t2 = t1.round((Unit::Nanosecond, 4)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 987_654_320));

    let t2 = t1.round((Unit::Nanosecond, 5)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 987_654_320));

    let t2 = t1.round((Unit::Nanosecond, 8)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 987_654_320));

    let t2 = t1.round((Unit::Nanosecond, 10)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 987_654_320));

    let t2 = t1.round((Unit::Nanosecond, 20)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 987_654_320));

    let t2 = t1.round((Unit::Nanosecond, 25)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 987_654_325));

    let t2 = t1.round((Unit::Nanosecond, 40)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 987_654_320));

    let t2 = t1.round((Unit::Nanosecond, 50)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 987_654_300));

    let t2 = t1.round((Unit::Nanosecond, 100)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 987_654_300));

    let t2 = t1.round((Unit::Nanosecond, 125)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 987_654_375));

    let t2 = t1.round((Unit::Nanosecond, 200)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 987_654_400));

    let t2 = t1.round((Unit::Nanosecond, 250)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 987_654_250));

    let t2 = t1.round((Unit::Nanosecond, 500)).unwrap();
    assert_eq!(t2, time(3, 34, 56, 987_654_500));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingincrement-invalid.js
#[test]
fn rounding_increment_invalid() {
    let t1 = time(8, 22, 36, 123456789);

    assert!(t1.round((Unit::Hour, 11)).is_err());
    assert!(t1.round((Unit::Minute, 29)).is_err());
    assert!(t1.round((Unit::Second, 29)).is_err());
    assert!(t1.round((Unit::Millisecond, 29)).is_err());
    assert!(t1.round((Unit::Microsecond, 29)).is_err());
    assert!(t1.round((Unit::Nanosecond, 29)).is_err());

    assert!(t1.round((Unit::Hour, 24)).is_err());
    assert!(t1.round((Unit::Minute, 60)).is_err());
    assert!(t1.round((Unit::Second, 60)).is_err());
    assert!(t1.round((Unit::Millisecond, 1_000)).is_err());
    assert!(t1.round((Unit::Microsecond, 1_000)).is_err());
    assert!(t1.round((Unit::Nanosecond, 1_000)).is_err());
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingincrement-out-of-range.js
#[test]
fn rounding_increment_out_of_range() {
    let t1 = time(12, 34, 56, 000_000_005);

    assert!(t1.round((Unit::Nanosecond, -1)).is_err());
    assert!(t1.round((Unit::Nanosecond, 0)).is_err());
    assert!(t1.round((Unit::Nanosecond, 1_000)).is_err());
    assert!(t1.round((Unit::Nanosecond, 1_000_000_001)).is_err());
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingmode-ceil.js
#[test]
fn rounding_mode_ceil() {
    let t1 = time(13, 46, 23, 123_987_500);

    let round = TimeRound::new().smallest(Unit::Hour).mode(RoundMode::Ceil);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(14, 0, 0, 0));

    let round = TimeRound::new().smallest(Unit::Minute).mode(RoundMode::Ceil);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 47, 0, 0));

    let round = TimeRound::new().smallest(Unit::Second).mode(RoundMode::Ceil);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 24, 0));

    let round =
        TimeRound::new().smallest(Unit::Millisecond).mode(RoundMode::Ceil);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 124_000_000));

    let round =
        TimeRound::new().smallest(Unit::Microsecond).mode(RoundMode::Ceil);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 123_988_000));

    let round =
        TimeRound::new().smallest(Unit::Nanosecond).mode(RoundMode::Ceil);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 123_987_500));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingmode-expand.js
#[test]
fn rounding_mode_expand() {
    let t1 = time(13, 46, 23, 123_987_500);

    let round = TimeRound::new().smallest(Unit::Hour).mode(RoundMode::Expand);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(14, 0, 0, 0));

    let round =
        TimeRound::new().smallest(Unit::Minute).mode(RoundMode::Expand);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 47, 0, 0));

    let round =
        TimeRound::new().smallest(Unit::Second).mode(RoundMode::Expand);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 24, 0));

    let round =
        TimeRound::new().smallest(Unit::Millisecond).mode(RoundMode::Expand);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 124_000_000));

    let round =
        TimeRound::new().smallest(Unit::Microsecond).mode(RoundMode::Expand);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 123_988_000));

    let round =
        TimeRound::new().smallest(Unit::Nanosecond).mode(RoundMode::Expand);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 123_987_500));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingmode-floor.js
#[test]
fn rounding_mode_floor() {
    let t1 = time(13, 46, 23, 123_987_500);

    let round = TimeRound::new().smallest(Unit::Hour).mode(RoundMode::Floor);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 0, 0, 0));

    let round = TimeRound::new().smallest(Unit::Minute).mode(RoundMode::Floor);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 0, 0));

    let round = TimeRound::new().smallest(Unit::Second).mode(RoundMode::Floor);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 0));

    let round =
        TimeRound::new().smallest(Unit::Millisecond).mode(RoundMode::Floor);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 123_000_000));

    let round =
        TimeRound::new().smallest(Unit::Microsecond).mode(RoundMode::Floor);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 123_987_000));

    let round =
        TimeRound::new().smallest(Unit::Nanosecond).mode(RoundMode::Floor);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 123_987_500));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingmode-halfCeil.js
#[test]
fn rounding_mode_half_ceil() {
    let t1 = time(13, 46, 23, 123_987_500);

    let round =
        TimeRound::new().smallest(Unit::Hour).mode(RoundMode::HalfCeil);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(14, 0, 0, 0));

    let round =
        TimeRound::new().smallest(Unit::Minute).mode(RoundMode::HalfCeil);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 0, 0));

    let round =
        TimeRound::new().smallest(Unit::Second).mode(RoundMode::HalfCeil);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 0));

    let round =
        TimeRound::new().smallest(Unit::Millisecond).mode(RoundMode::HalfCeil);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 124_000_000));

    let round =
        TimeRound::new().smallest(Unit::Microsecond).mode(RoundMode::HalfCeil);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 123_988_000));

    let round =
        TimeRound::new().smallest(Unit::Nanosecond).mode(RoundMode::HalfCeil);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 123_987_500));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingmode-halfEven.js
#[test]
fn rounding_mode_half_even() {
    let t1 = time(13, 46, 23, 123_987_500);

    let round =
        TimeRound::new().smallest(Unit::Hour).mode(RoundMode::HalfEven);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(14, 0, 0, 0));

    let round =
        TimeRound::new().smallest(Unit::Minute).mode(RoundMode::HalfEven);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 0, 0));

    let round =
        TimeRound::new().smallest(Unit::Second).mode(RoundMode::HalfEven);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 0));

    let round =
        TimeRound::new().smallest(Unit::Millisecond).mode(RoundMode::HalfEven);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 124_000_000));

    let round =
        TimeRound::new().smallest(Unit::Microsecond).mode(RoundMode::HalfEven);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 123_988_000));

    let round =
        TimeRound::new().smallest(Unit::Nanosecond).mode(RoundMode::HalfEven);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 123_987_500));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingmode-halfExpand.js
#[test]
fn rounding_mode_half_expand() {
    let t1 = time(13, 46, 23, 123_987_500);

    let round =
        TimeRound::new().smallest(Unit::Hour).mode(RoundMode::HalfExpand);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(14, 0, 0, 0));

    let round =
        TimeRound::new().smallest(Unit::Minute).mode(RoundMode::HalfExpand);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 0, 0));

    let round =
        TimeRound::new().smallest(Unit::Second).mode(RoundMode::HalfExpand);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 0));

    let round = TimeRound::new()
        .smallest(Unit::Millisecond)
        .mode(RoundMode::HalfExpand);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 124_000_000));

    let round = TimeRound::new()
        .smallest(Unit::Microsecond)
        .mode(RoundMode::HalfExpand);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 123_988_000));

    let round = TimeRound::new()
        .smallest(Unit::Nanosecond)
        .mode(RoundMode::HalfExpand);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 123_987_500));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingmode-halfFloor.js
#[test]
fn rounding_mode_half_floor() {
    let t1 = time(13, 46, 23, 123_987_500);

    let round =
        TimeRound::new().smallest(Unit::Hour).mode(RoundMode::HalfFloor);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(14, 0, 0, 0));

    let round =
        TimeRound::new().smallest(Unit::Minute).mode(RoundMode::HalfFloor);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 0, 0));

    let round =
        TimeRound::new().smallest(Unit::Second).mode(RoundMode::HalfFloor);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 0));

    let round = TimeRound::new()
        .smallest(Unit::Millisecond)
        .mode(RoundMode::HalfFloor);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 124_000_000));

    let round = TimeRound::new()
        .smallest(Unit::Microsecond)
        .mode(RoundMode::HalfFloor);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 123_987_000));

    let round =
        TimeRound::new().smallest(Unit::Nanosecond).mode(RoundMode::HalfFloor);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 123_987_500));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingmode-halfTrunc.js
#[test]
fn rounding_mode_half_trunc() {
    let t1 = time(13, 46, 23, 123_987_500);

    let round =
        TimeRound::new().smallest(Unit::Hour).mode(RoundMode::HalfTrunc);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(14, 0, 0, 0));

    let round =
        TimeRound::new().smallest(Unit::Minute).mode(RoundMode::HalfTrunc);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 0, 0));

    let round =
        TimeRound::new().smallest(Unit::Second).mode(RoundMode::HalfTrunc);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 0));

    let round = TimeRound::new()
        .smallest(Unit::Millisecond)
        .mode(RoundMode::HalfTrunc);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 124_000_000));

    let round = TimeRound::new()
        .smallest(Unit::Microsecond)
        .mode(RoundMode::HalfTrunc);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 123_987_000));

    let round =
        TimeRound::new().smallest(Unit::Nanosecond).mode(RoundMode::HalfTrunc);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 123_987_500));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/roundingmode-trunc.js
#[test]
fn rounding_mode_trunc() {
    let t1 = time(13, 46, 23, 123_987_500);

    let round = TimeRound::new().smallest(Unit::Hour).mode(RoundMode::Trunc);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 0, 0, 0));

    let round = TimeRound::new().smallest(Unit::Minute).mode(RoundMode::Trunc);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 0, 0));

    let round = TimeRound::new().smallest(Unit::Second).mode(RoundMode::Trunc);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 0));

    let round =
        TimeRound::new().smallest(Unit::Millisecond).mode(RoundMode::Trunc);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 123_000_000));

    let round =
        TimeRound::new().smallest(Unit::Microsecond).mode(RoundMode::Trunc);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 123_987_000));

    let round =
        TimeRound::new().smallest(Unit::Nanosecond).mode(RoundMode::Trunc);
    let t2 = t1.round(round).unwrap();
    assert_eq!(t2, time(13, 46, 23, 123_987_500));
}

/// DIFFERENCE: Unlike Temporal, we permit the smallest unit to be missing. It
/// defaults to `Nanosecond`.
///
/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/round/smallestunit-missing.js
#[test]
fn smallest_unit_missing() {
    let t1 = time(13, 46, 23, 123_987_499);

    let t2 = t1.round(TimeRound::new()).unwrap();
    assert_eq!(t2, t1);

    let t2 = t1.round(TimeRound::new().increment(500)).unwrap();
    assert_eq!(t2, time(13, 46, 23, 123_987_500));
}
