use jiff::{
    civil::{time, Time, TimeDifference},
    RoundMode, ToSpan, Unit,
};

use crate::tc39_262::Result;

/// Source: https://github.com/tc39/test262/blob/62626e083bd506124aac6c799464d76c2c42851b/test/built-ins/Temporal/PlainTime/prototype/until/argument-cast.js
#[test]
fn argument_cast() -> Result {
    let t1 = time(15, 23, 30, 123_456_789);
    let t2 = time(16, 34, 0, 0);
    let span = 1
        .hours()
        .minutes(10)
        .seconds(29)
        .milliseconds(876)
        .microseconds(543)
        .nanoseconds(211);
    assert_eq!(t1.until(t2)?, span);
    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainTime/prototype/until/balance-negative-time-units.js
#[test]
fn balance_negative_time_units() -> Result {
    let t2 = time(1, 1, 1, 001_001_001);

    let t1 = time(0, 0, 0, 000_000_002);
    assert_eq!(t1.until(t2)?.to_string(), "PT1h1m1.001000999s");

    let t1 = time(0, 0, 0, 000_002_000);
    assert_eq!(t1.until(t2)?.to_string(), "PT1h1m1.000999001s");

    let t1 = time(0, 0, 0, 002_000_000);
    assert_eq!(t1.until(t2)?.to_string(), "PT1h1m0.999001001s");

    let t1 = time(0, 0, 2, 0);
    assert_eq!(t1.until(t2)?.to_string(), "PT1h59.001001001s");

    let t1 = time(0, 2, 0, 0);
    assert_eq!(t1.until(t2)?.to_string(), "PT59m1.001001001s");

    let t1 = time(2, 0, 0, 0);
    assert_eq!(t1.until(t2)?.to_string(), "-PT58m58.998998999s");

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainTime/prototype/until/basic.js
#[test]
fn basic() -> Result {
    let one = time(15, 23, 30, 123_456_789);
    let two = time(16, 23, 30, 123_456_789);
    let three = time(17, 0, 30, 123_456_789);

    assert_eq!(one.until(two)?.to_string(), "PT1h");
    assert_eq!(two.until(one)?.to_string(), "-PT1h");
    assert_eq!(one.until(three)?.to_string(), "PT1h37m");
    assert_eq!(three.until(one)?.to_string(), "-PT1h37m");

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainTime/prototype/until/largestunit-invalid-string.js
#[test]
fn largestunit_invalid_string() {
    let earlier = time(12, 34, 56, 0);
    let later = time(13, 35, 57, 987_654_321);
    let bad_values = [Unit::Year, Unit::Month, Unit::Week, Unit::Day];
    for unit in bad_values {
        assert!(
            earlier.until((unit, later)).is_err(),
            "calling Time::until with largest unit {unit:?} should fail"
        );
    }
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainTime/prototype/until/largestunit-smallestunit-mismatch.js
#[test]
fn largestunit_smallestunit_mismatch() {
    let earlier = time(12, 34, 56, 0);
    let later = time(13, 35, 57, 987_654_321);
    let units = [
        Unit::Hour,
        Unit::Minute,
        Unit::Second,
        Unit::Millisecond,
        Unit::Microsecond,
        Unit::Nanosecond,
    ];
    for largest in 1..units.len() {
        for smallest in 0..largest {
            let (largest, smallest) = (units[largest], units[smallest]);
            let args =
                TimeDifference::new(later).largest(largest).smallest(smallest);
            assert!(
                earlier.until(args).is_err(),
                "Time::until with smallest unit {smallest:?} \
                 and largest unit {largest:?} should fail"
            );
        }
    }
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainTime/prototype/until/largestunit.js
#[test]
fn largestunit() -> Result {
    let t1 = time(4, 48, 55, 0);
    let t2 = time(11, 59, 58, 0);

    assert_eq!(t1.until(t2)?.to_string(), "PT7h11m3s");
    assert_eq!(t1.until((Unit::Hour, t2))?.to_string(), "PT7h11m3s");
    assert_eq!(t1.until((Unit::Minute, t2))?.to_string(), "PT431m3s");
    assert_eq!(t1.until((Unit::Second, t2))?.to_string(), "PT25863s");

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainTime/prototype/until/result-sub-second.js
#[test]
fn result_sub_second() -> Result {
    let t1 = time(10, 23, 15, 0);
    let t2 = time(17, 15, 57, 250_250_250);

    assert_eq!(
        t1.until((Unit::Millisecond, t2))?,
        24762250.milliseconds().microseconds(250).nanoseconds(250),
    );
    // Same as above, but tests that a span converted to a string is done
    // correctly. (Since ISO 8601 durations only support units below seconds
    // via fractional seconds.)
    assert_eq!(
        t1.until((Unit::Millisecond, t2))?.to_string(),
        "PT24762.25025025s",
    );

    assert_eq!(
        t1.until((Unit::Microsecond, t2))?,
        2_4762_250_250i64.microseconds().nanoseconds(250)
    );
    assert_eq!(
        t1.until((Unit::Microsecond, t2))?.to_string(),
        "PT24762.25025025s",
    );

    assert_eq!(
        t1.until((Unit::Nanosecond, t2))?,
        2_4762_250_250_250i64.nanoseconds(),
    );
    assert_eq!(
        t1.until((Unit::Nanosecond, t2))?.to_string(),
        "PT24762.25025025s",
    );

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainTime/prototype/until/round-cross-unit-boundary.js
#[test]
fn round_cross_unit_boundary() -> Result {
    let t1 = time(0, 0, 0, 0);
    let t2 = time(1, 59, 59, 0);
    let span = t1.until(
        TimeDifference::new(t2)
            .smallest(Unit::Minute)
            .largest(Unit::Hour)
            .mode(RoundMode::Expand),
    )?;
    assert_eq!(span, 2.hours());
    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainTime/prototype/until/roundingincrement-hours.js
#[test]
fn roundingincrement_hours() -> Result {
    let t1 = time(3, 12, 34, 123_456_789);
    let t2 = time(13, 47, 57, 988_655_322);
    let args = TimeDifference::new(t2).smallest(Unit::Hour);

    assert_eq!(t1.until(args.increment(1))?, 10.hours());
    assert_eq!(t1.until(args.increment(2))?, 10.hours());
    assert_eq!(t1.until(args.increment(3))?, 9.hours());
    assert_eq!(t1.until(args.increment(4))?, 8.hours());
    assert_eq!(t1.until(args.increment(6))?, 6.hours());
    assert_eq!(t1.until(args.increment(8))?, 8.hours());
    assert_eq!(t1.until(args.increment(12))?, 0.hours());

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainTime/prototype/until/roundingincrement-invalid.js
#[test]
fn roundingincrement_invalid() -> Result {
    let t1: Time = "08:22:36.123456789".parse()?;
    let t2: Time = "12:39:40.987654321".parse()?;
    let args = TimeDifference::new(t2);

    assert!(t1.until(args.smallest(Unit::Hour).increment(11)).is_err());
    assert!(t1.until(args.smallest(Unit::Minute).increment(29)).is_err());
    assert!(t1.until(args.smallest(Unit::Second).increment(29)).is_err());
    assert!(t1.until(args.smallest(Unit::Millisecond).increment(29)).is_err());
    assert!(t1.until(args.smallest(Unit::Microsecond).increment(29)).is_err());
    assert!(t1.until(args.smallest(Unit::Nanosecond).increment(29)).is_err());

    assert!(t1.until(args.smallest(Unit::Hour).increment(24)).is_err());
    assert!(t1.until(args.smallest(Unit::Minute).increment(60)).is_err());
    assert!(t1.until(args.smallest(Unit::Second).increment(60)).is_err());
    assert!(t1
        .until(args.smallest(Unit::Millisecond).increment(1000))
        .is_err());
    assert!(t1
        .until(args.smallest(Unit::Microsecond).increment(1000))
        .is_err());
    assert!(t1
        .until(args.smallest(Unit::Nanosecond).increment(1000))
        .is_err());

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainTime/prototype/until/roundingincrement-microseconds.js
#[test]
fn roundingincrement_microseconds() -> Result {
    let t1 = time(3, 12, 34, 123_456_789);
    let t2 = time(13, 47, 57, 988_655_322);
    let args = TimeDifference::new(t2).smallest(Unit::Microsecond);

    let span = 10.hours().minutes(35).seconds(23).milliseconds(865);
    assert_eq!(t1.until(args.increment(1))?, span.microseconds(198));
    assert_eq!(t1.until(args.increment(2))?, span.microseconds(198));
    assert_eq!(t1.until(args.increment(4))?, span.microseconds(196));
    assert_eq!(t1.until(args.increment(5))?, span.microseconds(195));
    assert_eq!(t1.until(args.increment(8))?, span.microseconds(192));
    assert_eq!(t1.until(args.increment(10))?, span.microseconds(190));
    assert_eq!(t1.until(args.increment(20))?, span.microseconds(180));
    assert_eq!(t1.until(args.increment(25))?, span.microseconds(175));
    assert_eq!(t1.until(args.increment(40))?, span.microseconds(160));
    assert_eq!(t1.until(args.increment(50))?, span.microseconds(150));
    assert_eq!(t1.until(args.increment(100))?, span.microseconds(100));
    assert_eq!(t1.until(args.increment(125))?, span.microseconds(125));
    assert_eq!(t1.until(args.increment(200))?, span.microseconds(0));
    assert_eq!(t1.until(args.increment(250))?, span.microseconds(0));
    assert_eq!(t1.until(args.increment(500))?, span.microseconds(0));

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainTime/prototype/until/roundingincrement-milliseconds.js
#[test]
fn roundingincrement_milliseconds() -> Result {
    let t1 = time(3, 12, 34, 123_456_789);
    let t2 = time(13, 47, 57, 988_655_322);
    let args = TimeDifference::new(t2).smallest(Unit::Millisecond);

    let span = 10.hours().minutes(35).seconds(23);
    assert_eq!(t1.until(args.increment(1))?, span.milliseconds(865));
    assert_eq!(t1.until(args.increment(2))?, span.milliseconds(864));
    assert_eq!(t1.until(args.increment(4))?, span.milliseconds(864));
    assert_eq!(t1.until(args.increment(5))?, span.milliseconds(865));
    assert_eq!(t1.until(args.increment(8))?, span.milliseconds(864));
    assert_eq!(t1.until(args.increment(10))?, span.milliseconds(860));
    assert_eq!(t1.until(args.increment(20))?, span.milliseconds(860));
    assert_eq!(t1.until(args.increment(25))?, span.milliseconds(850));
    assert_eq!(t1.until(args.increment(40))?, span.milliseconds(840));
    assert_eq!(t1.until(args.increment(50))?, span.milliseconds(850));
    assert_eq!(t1.until(args.increment(100))?, span.milliseconds(800));
    assert_eq!(t1.until(args.increment(125))?, span.milliseconds(750));
    assert_eq!(t1.until(args.increment(200))?, span.milliseconds(800));
    assert_eq!(t1.until(args.increment(250))?, span.milliseconds(750));
    assert_eq!(t1.until(args.increment(500))?, span.milliseconds(500));

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainTime/prototype/until/roundingincrement-minutes.js
#[test]
fn roundingincrement_minutes() -> Result {
    let t1 = time(3, 12, 34, 123_456_789);
    let t2 = time(13, 47, 57, 988_655_322);
    let args = TimeDifference::new(t2).smallest(Unit::Minute);

    let span = 10.hours();
    assert_eq!(t1.until(args.increment(1))?, span.minutes(35));
    assert_eq!(t1.until(args.increment(2))?, span.minutes(34));
    assert_eq!(t1.until(args.increment(3))?, span.minutes(33));
    assert_eq!(t1.until(args.increment(4))?, span.minutes(32));
    assert_eq!(t1.until(args.increment(5))?, span.minutes(35));
    assert_eq!(t1.until(args.increment(6))?, span.minutes(30));
    assert_eq!(t1.until(args.increment(10))?, span.minutes(30));
    assert_eq!(t1.until(args.increment(12))?, span.minutes(24));
    assert_eq!(t1.until(args.increment(15))?, span.minutes(30));
    assert_eq!(t1.until(args.increment(20))?, span.minutes(20));
    assert_eq!(t1.until(args.increment(30))?, span.minutes(30));

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainTime/prototype/until/roundingincrement-nanoseconds.js
#[test]
fn roundingincrement_nanoseconds() -> Result {
    let t1 = time(3, 12, 34, 123_456_789);
    let t2 = time(13, 47, 57, 988_655_322);
    let args = TimeDifference::new(t2).smallest(Unit::Nanosecond);

    let span =
        10.hours().minutes(35).seconds(23).milliseconds(865).microseconds(198);
    assert_eq!(t1.until(args.increment(1))?, span.nanoseconds(533));
    assert_eq!(t1.until(args.increment(2))?, span.nanoseconds(532));
    assert_eq!(t1.until(args.increment(4))?, span.nanoseconds(532));
    assert_eq!(t1.until(args.increment(5))?, span.nanoseconds(530));
    assert_eq!(t1.until(args.increment(8))?, span.nanoseconds(528));
    assert_eq!(t1.until(args.increment(10))?, span.nanoseconds(530));
    assert_eq!(t1.until(args.increment(20))?, span.nanoseconds(520));
    assert_eq!(t1.until(args.increment(25))?, span.nanoseconds(525));
    assert_eq!(t1.until(args.increment(40))?, span.nanoseconds(520));
    assert_eq!(t1.until(args.increment(50))?, span.nanoseconds(500));
    assert_eq!(t1.until(args.increment(100))?, span.nanoseconds(500));
    assert_eq!(t1.until(args.increment(125))?, span.nanoseconds(500));
    assert_eq!(t1.until(args.increment(200))?, span.nanoseconds(400));
    assert_eq!(t1.until(args.increment(250))?, span.nanoseconds(500));
    assert_eq!(t1.until(args.increment(500))?, span.nanoseconds(500));

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainTime/prototype/until/roundingincrement-seconds.js
#[test]
fn roundingincrement_seconds() -> Result {
    let t1 = time(3, 12, 34, 123_456_789);
    let t2 = time(13, 47, 57, 988_655_322);
    let args = TimeDifference::new(t2).smallest(Unit::Second);

    let span = 10.hours().minutes(35);
    assert_eq!(t1.until(args.increment(1))?, span.seconds(23));
    assert_eq!(t1.until(args.increment(2))?, span.seconds(22));
    assert_eq!(t1.until(args.increment(3))?, span.seconds(21));
    assert_eq!(t1.until(args.increment(4))?, span.seconds(20));
    assert_eq!(t1.until(args.increment(5))?, span.seconds(20));
    assert_eq!(t1.until(args.increment(6))?, span.seconds(18));
    assert_eq!(t1.until(args.increment(10))?, span.seconds(20));
    assert_eq!(t1.until(args.increment(12))?, span.seconds(12));
    assert_eq!(t1.until(args.increment(15))?, span.seconds(15));
    assert_eq!(t1.until(args.increment(20))?, span.seconds(20));
    assert_eq!(t1.until(args.increment(30))?, span.seconds(0));

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainTime/prototype/until/roundingmode-ceil.js
///
/// NOTE: I got tired of writing tests, so I just wrote tests for one rounding
/// mode. We can rely on more coverage of rounding mode for spans for the span
/// tests.
#[test]
fn roundingmode_ceil() -> Result {
    let t1 = time(8, 22, 36, 123_456_789);
    let t2 = time(12, 39, 40, 987_654_289);

    let args = TimeDifference::new(t2).mode(RoundMode::Ceil);
    assert_eq!(t1.until(args.smallest(Unit::Hour))?, 5.hours());
    let span = 4.hours();
    assert_eq!(t1.until(args.smallest(Unit::Minute))?, span.minutes(18));
    let span = span.minutes(17);
    assert_eq!(t1.until(args.smallest(Unit::Second))?, span.seconds(5));
    let span = span.seconds(4);
    assert_eq!(
        t1.until(args.smallest(Unit::Millisecond))?,
        span.milliseconds(865)
    );
    let span = span.milliseconds(864);
    assert_eq!(
        t1.until(args.smallest(Unit::Microsecond))?,
        span.microseconds(198)
    );
    let span = span.microseconds(197);
    assert_eq!(
        t1.until(args.smallest(Unit::Nanosecond))?,
        span.nanoseconds(500)
    );

    let args = TimeDifference::new(t1).mode(RoundMode::Ceil);
    assert_eq!(t2.until(args.smallest(Unit::Hour))?, -4.hours());
    let span = -4.hours();
    assert_eq!(t2.until(args.smallest(Unit::Minute))?, span.minutes(17));
    let span = span.minutes(17);
    assert_eq!(t2.until(args.smallest(Unit::Second))?, span.seconds(4));
    let span = span.seconds(4);
    assert_eq!(
        t2.until(args.smallest(Unit::Millisecond))?,
        span.milliseconds(864)
    );
    let span = span.milliseconds(864);
    assert_eq!(
        t2.until(args.smallest(Unit::Microsecond))?,
        span.microseconds(197)
    );
    let span = span.microseconds(197);
    assert_eq!(
        t2.until(args.smallest(Unit::Nanosecond))?,
        span.nanoseconds(500)
    );

    Ok(())
}
