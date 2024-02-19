use jiff::{civil::Time, Instant};

/// TODO: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/equals
///
/// Most tests seem to require parsing. Some also deal with timezones. Many
/// are irrelevant because of types.

/// TODO: Switch to a zoned time, or at least add it.
///
/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/equals/argument-zoneddatetime-negative-epochnanoseconds.js
#[test]
fn argument_zoneddatetime_negative_epochnanoseconds() {
    let instant = Instant::from_unix(-13849764, -999_999_999).unwrap();
    let time = instant.to_datetime().time();
    assert_eq!(time, Time::constant(16, 50, 35, 000_000_001));
}
