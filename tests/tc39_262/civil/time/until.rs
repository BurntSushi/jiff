use jiff::{civil::Time, ToSpan};

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/until/argument-cast.js
#[test]
fn argument_cast() {
    let t1 = Time::constant(15, 23, 30, 123_456_789);
    let t2 = Time::constant(16, 34, 0, 0);
    let span = 1
        .hours()
        .minutes(10)
        .seconds(29)
        .milliseconds(876)
        .microseconds(543)
        .nanoseconds(211);
    assert_eq!(t1.until(t2), span);
}
