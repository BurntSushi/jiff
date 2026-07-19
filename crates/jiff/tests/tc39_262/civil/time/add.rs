use jiff::{
    civil::{time, Time},
    Span,
};

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainTime/prototype/add/argument-string-fractional-units-rounding-mode.js
#[test]
fn argument_string_fractional_units_rounding_mode() {
    let span: Span = "PT1.03125H".parse().unwrap();
    assert_eq!(Time::midnight() + span, time(1, 1, 52, 500_000_000));

    let span: Span = "-PT1.03125H".parse().unwrap();
    assert_eq!(Time::midnight() + span, time(22, 58, 7, 500_000_000));
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainTime/prototype/add/argument-string-negative-fractional-units.js
#[test]
fn argument_string_negative_fractional_units() {
    let span: Span = "-PT24.567890123H".parse().unwrap();
    assert_eq!(Time::midnight() + span, time(23, 25, 55, 595_557_200));

    let span: Span = "-PT1440.567890123M".parse().unwrap();
    assert_eq!(Time::midnight() + span, time(23, 59, 25, 926_592_620));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/add/argument-duration.js
#[test]
fn argument_duration() {
    let t1 = time(15, 23, 30, 123_456_789);
    let span = Span::new().hours(16);
    let t2 = t1.wrapping_add(span);
    assert_eq!(t2, time(7, 23, 30, 123_456_789));
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/add/argument-duration-max.js
#[test]
fn argument_duration_max() {
    let t1 = time(0, 0, 0, 0);
    let expected = time(7, 36, 31, 999_999_999);

    let span = Span::new()
        .years(19_998)
        .days(7_304_482)
        .nanoseconds(27391999999999i64);
    let t2 = t1.wrapping_add(span);
    assert_eq!(t2, expected);

    let span = Span::new()
        .months(239_976)
        .days(7_304_482)
        .nanoseconds(27391999999999i64);
    let t2 = t1.wrapping_add(span);
    assert_eq!(t2, expected);

    let span = Span::new()
        .weeks(1_043_497)
        .days(7_304_482)
        .nanoseconds(27391999999999i64);
    let t2 = t1.wrapping_add(span);
    assert_eq!(t2, expected);

    let span = Span::new().days(7_304_482).nanoseconds(27391999999999i64);
    let t2 = t1.wrapping_add(span);
    assert_eq!(t2, expected);

    let span = Span::new().hours(175_307_591).nanoseconds(65498124754943i64);
    let t2 = t1.wrapping_add(span);
    assert_eq!(t2, expected);

    let span =
        Span::new().minutes(10_518_455_460i64).nanoseconds(65498124754943i64);
    let t2 = t1.wrapping_add(span);
    assert_eq!(t2, expected);

    let span =
        Span::new().seconds(631_107_327_600i64).nanoseconds(65498124754943i64);
    let t2 = t1.wrapping_add(span);
    assert_eq!(t2, expected);
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/add/argument-duration-max.js
#[test]
fn argument_duration_min() {
    let t1 = time(0, 0, 0, 0);
    let expected = time(16, 23, 28, 000_000_001);

    let span = Span::new()
        .years(-19_998)
        .days(-7_304_482)
        .nanoseconds(-27391999999999i64);
    let t2 = t1.wrapping_add(span);
    assert_eq!(t2, expected);

    let span = Span::new()
        .months(-239_976)
        .days(-7_304_482)
        .nanoseconds(-27391999999999i64);
    let t2 = t1.wrapping_add(span);
    assert_eq!(t2, expected);

    let span = Span::new()
        .weeks(-1_043_497)
        .days(-7_304_482)
        .nanoseconds(-27391999999999i64);
    let t2 = t1.wrapping_add(span);
    assert_eq!(t2, expected);

    let span = Span::new().days(-7_304_482).nanoseconds(-27391999999999i64);
    let t2 = t1.wrapping_add(span);
    assert_eq!(t2, expected);

    let span = Span::new().hours(-175_307_591).nanoseconds(-65498124754943i64);
    let t2 = t1.wrapping_add(span);
    assert_eq!(t2, expected);

    let span = Span::new()
        .minutes(-10_518_455_460i64)
        .nanoseconds(-65498124754943i64);
    let t2 = t1.wrapping_add(span);
    assert_eq!(t2, expected);

    let span = Span::new()
        .seconds(-631_107_327_600i64)
        .nanoseconds(-65498124754943i64);
    let t2 = t1.wrapping_add(span);
    assert_eq!(t2, expected);
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/add/argument-higher-units.js
#[test]
fn argument_higher_units() {
    let t1 = time(15, 23, 30, 123_456_789);

    let span = Span::new().days(1);
    assert_eq!(t1, t1.wrapping_add(span));

    let span = Span::new().weeks(1);
    assert_eq!(t1, t1.wrapping_add(span));

    let span = Span::new().months(1);
    assert_eq!(t1, t1.wrapping_add(span));

    let span = Span::new().years(1);
    assert_eq!(t1, t1.wrapping_add(span));
}

/// DIFFERENCE: We "allow" mixed signs in spans, but they normalize. That is,
/// if *any* component of a span is negative, then the whole span is negative.
///
/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/add/argument-mixed-sign.js
#[test]
fn argument_mixed_sign() {
    let t1 = time(15, 30, 45, 987_654_321);
    let span = Span::new().hours(1).minutes(-30);
    let t2 = t1.wrapping_add(span);
    assert_eq!(t2, time(14, 0, 45, 987_654_321));
}

/// In Test262, this is seemingly just testing that "plain" objects can
/// be passed to the `PlainTime.add` API, as opposed to proper `Duration`
/// objects. That doesn't really apply to jiff, because Rust, but we still
/// capture the tests here.
///
/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/add/argument-object.js
#[test]
fn argument_object() {
    let t1 = time(15, 23, 30, 123_456_789);

    let span = Span::new().hours(16);
    assert_eq!(t1.wrapping_add(span), time(7, 23, 30, 123_456_789));

    let span = Span::new().minutes(45);
    assert_eq!(t1.wrapping_add(span), time(16, 8, 30, 123_456_789));

    let span = Span::new().seconds(800);
    assert_eq!(t1.wrapping_add(span), time(15, 36, 50, 123_456_789));

    let span = Span::new().milliseconds(800);
    assert_eq!(t1.wrapping_add(span), time(15, 23, 30, 923_456_789));

    let span = Span::new().microseconds(800);
    assert_eq!(t1.wrapping_add(span), time(15, 23, 30, 124_256_789));

    let span = Span::new().nanoseconds(300);
    assert_eq!(t1.wrapping_add(span), time(15, 23, 30, 123_457_089));

    let t1 = time(7, 23, 30, 123_456_789);
    let span = Span::new().hours(-16);
    assert_eq!(t1.wrapping_add(span), time(15, 23, 30, 123_456_789));

    let t1 = time(16, 8, 30, 123_456_789);
    let span = Span::new().minutes(-45);
    assert_eq!(t1.wrapping_add(span), time(15, 23, 30, 123_456_789));

    let t1 = time(15, 36, 50, 123_456_789);
    let span = Span::new().seconds(-800);
    assert_eq!(t1.wrapping_add(span), time(15, 23, 30, 123_456_789));

    let t1 = time(15, 23, 30, 923_456_789);
    let span = Span::new().milliseconds(-800);
    assert_eq!(t1.wrapping_add(span), time(15, 23, 30, 123_456_789));

    let t1 = time(15, 23, 30, 124_256_789);
    let span = Span::new().microseconds(-800);
    assert_eq!(t1.wrapping_add(span), time(15, 23, 30, 123_456_789));

    let t1 = time(15, 23, 30, 123_457_089);
    let span = Span::new().nanoseconds(-300);
    assert_eq!(t1.wrapping_add(span), time(15, 23, 30, 123_456_789));
}

/// Temporal doesn't have checked arithmetic, so this test just copied
/// `argument_object`, but with checked arithmetic.
///
/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/add/argument-object.js
#[test]
fn argument_object_checked() {
    let t1 = time(15, 23, 30, 123_456_789);

    let span = Span::new().hours(16);
    assert_eq!(t1.checked_add(span).ok(), None);

    // Added our own test to avoid wrapping.
    let span = Span::new().hours(2);
    assert_eq!(t1.checked_add(span).unwrap(), time(17, 23, 30, 123_456_789));

    let span = Span::new().minutes(45);
    assert_eq!(t1.checked_add(span).unwrap(), time(16, 8, 30, 123_456_789));

    let span = Span::new().seconds(800);
    assert_eq!(t1.checked_add(span).unwrap(), time(15, 36, 50, 123_456_789));

    let span = Span::new().milliseconds(800);
    assert_eq!(t1.checked_add(span).unwrap(), time(15, 23, 30, 923_456_789));

    let span = Span::new().microseconds(800);
    assert_eq!(t1.checked_add(span).unwrap(), time(15, 23, 30, 124_256_789));

    let span = Span::new().nanoseconds(300);
    assert_eq!(t1.checked_add(span).unwrap(), time(15, 23, 30, 123_457_089));

    let t1 = time(7, 23, 30, 123_456_789);
    let span = Span::new().hours(-16);
    assert_eq!(t1.checked_add(span).ok(), None);

    // Added our own test to avoid wrapping.
    let t1 = time(7, 23, 30, 123_456_789);
    let span = Span::new().hours(-2);
    assert_eq!(t1.checked_add(span).unwrap(), time(5, 23, 30, 123_456_789));

    let t1 = time(16, 8, 30, 123_456_789);
    let span = Span::new().minutes(-45);
    assert_eq!(t1.checked_add(span).unwrap(), time(15, 23, 30, 123_456_789));

    let t1 = time(15, 36, 50, 123_456_789);
    let span = Span::new().seconds(-800);
    assert_eq!(t1.checked_add(span).unwrap(), time(15, 23, 30, 123_456_789));

    let t1 = time(15, 23, 30, 923_456_789);
    let span = Span::new().milliseconds(-800);
    assert_eq!(t1.checked_add(span).unwrap(), time(15, 23, 30, 123_456_789));

    let t1 = time(15, 23, 30, 124_256_789);
    let span = Span::new().microseconds(-800);
    assert_eq!(t1.checked_add(span).unwrap(), time(15, 23, 30, 123_456_789));

    let t1 = time(15, 23, 30, 123_457_089);
    let span = Span::new().nanoseconds(-300);
    assert_eq!(t1.checked_add(span).unwrap(), time(15, 23, 30, 123_456_789));
}

/// DIFFERENCE: Wrapping arithmetic on `Time` always wraps, even when the span
/// represents an interval of time bigger than what is supported.
///
/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/add/argument-string-duration-too-large.js
#[test]
fn argument_string_duration_too_large() {
    let t1 = time(0, 0, 0, 0);
    let span = Span::new().years(19_998).months(239_976);
    assert_eq!(t1.wrapping_add(span), t1);
    assert_eq!(t1.checked_add(span).ok(), None);
}

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/add/balance-negative-time-units.js
#[test]
fn balance_negative_time_units() {
    let t1 = time(1, 1, 1, 001_001_001);

    let span = Span::new().nanoseconds(-2);
    assert_eq!(t1.wrapping_add(span), time(1, 1, 1, 001_000_999));

    let span = Span::new().microseconds(-2);
    assert_eq!(t1.wrapping_add(span), time(1, 1, 1, 000_999_001));

    let span = Span::new().milliseconds(-2);
    assert_eq!(t1.wrapping_add(span), time(1, 1, 0, 999_001_001));

    let span = Span::new().seconds(-2);
    assert_eq!(t1.wrapping_add(span), time(1, 0, 59, 001_001_001));

    let span = Span::new().minutes(-2);
    assert_eq!(t1.wrapping_add(span), time(0, 59, 1, 001_001_001));

    let span = Span::new().hours(-2);
    assert_eq!(t1.wrapping_add(span), time(23, 1, 1, 001_001_001));
}
