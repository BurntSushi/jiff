use jiff::{
    civil::{date, DateTime, DateTimeDifference},
    RoundMode, ToSpan, Unit,
};

use crate::tc39_262::Result;

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/until/balance-negative-duration.js
#[test]
fn balance_negative_duration() -> Result {
    let dt1 = date(2000, 5, 2).at(9, 0, 0, 0);
    let dt2 = date(2000, 5, 5).at(10, 0, 0, 0);
    assert_eq!(dt2.until((Unit::Day, dt1))?, -3.days().hours(1));

    let dt1 = date(2000, 5, 2).at(10, 0, 0, 0);
    let dt2 = date(2000, 5, 5).at(9, 0, 0, 0);
    assert_eq!(dt2.until((Unit::Day, dt1))?, -2.days().hours(23));

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/until/balance-negative-time-units.js
#[test]
fn balance_negative_time_units() {
    let dt = date(1996, 5, 2).at(1, 1, 1, 001_001_001);

    assert_eq!(
        dt - date(1996, 5, 2).at(0, 0, 0, 000_000_002),
        1.hour()
            .minutes(1)
            .seconds(1)
            .milliseconds(1)
            .microseconds(0)
            .nanoseconds(999),
    );
    assert_eq!(
        dt - date(1996, 5, 2).at(0, 0, 0, 000_002_000),
        1.hour()
            .minutes(1)
            .seconds(1)
            .milliseconds(0)
            .microseconds(999)
            .nanoseconds(1),
    );
    assert_eq!(
        dt - date(1996, 5, 2).at(0, 0, 0, 002_000_000),
        1.hour()
            .minutes(1)
            .seconds(0)
            .milliseconds(999)
            .microseconds(1)
            .nanoseconds(1),
    );
    assert_eq!(
        dt - date(1996, 5, 2).at(0, 0, 2, 0),
        1.hour()
            .minutes(0)
            .seconds(59)
            .milliseconds(1)
            .microseconds(1)
            .nanoseconds(1),
    );
    assert_eq!(
        dt - date(1996, 5, 2).at(0, 2, 0, 0),
        0.hour()
            .minutes(59)
            .seconds(1)
            .milliseconds(1)
            .microseconds(1)
            .nanoseconds(1),
    );
    assert_eq!(
        dt - date(1996, 5, 2).at(2, 0, 0, 0),
        -0.hour()
            .minutes(58)
            .seconds(58)
            .milliseconds(998)
            .microseconds(998)
            .nanoseconds(999),
    );
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/until/balance.js
#[test]
fn balance() -> Result {
    let a: DateTime = "2017-10-05T08:07:14+00:00[UTC]".parse()?;
    let b: DateTime = "2021-03-05T03:32:45+00:00[UTC]".parse()?;
    let c: DateTime = "2021-03-05T09:32:45+00:00[UTC]".parse()?;

    let span = a.until((Unit::Month, b))?;
    assert_eq!(span.to_string(), "P40m27dT19h25m31s");
    assert_eq!(a + span, b);

    let span = b.until((Unit::Month, a))?;
    assert_eq!(span.to_string(), "-P40m30dT19h25m31s");
    assert_eq!(b + span, a);

    let span = c.until((Unit::Month, a))?;
    assert_eq!(span.to_string(), "-P41mT1h25m31s");
    assert_eq!(c + span, a);

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/until/inverse.js
#[test]
fn inverse() -> Result {
    let dt1 = date(1976, 11, 18).at(15, 23, 30, 123_456_789);
    let dt2 = date(2016, 3, 3).at(18, 0, 0, 0);
    assert_eq!(dt1.until(dt2)?, dt2.since(dt1)?);
    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/until/largestunit-smallestunit-mismatch.js
#[test]
fn largestunit_smallestunit_mismatch() {
    let dt1 = date(2000, 5, 2).at(12, 34, 56, 0);
    let dt2 = date(2001, 6, 3).at(13, 35, 57, 987_654_321);

    let units = [
        Unit::Year,
        Unit::Month,
        Unit::Week,
        Unit::Day,
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
            let args = DateTimeDifference::new(dt2)
                .largest(largest)
                .smallest(smallest);
            assert!(
                dt1.until(args).is_err(),
                "DateTime::until should fail with largest units {largest:?} \
                 and smallest units {smallest:?}",
            );
        }
    }
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/until/no-unnecessary-units.js
#[test]
fn no_unncessary_units() -> Result {
    let dt1 = DateTime::from(date(2021, 2, 28));
    let dt2 = DateTime::from(date(2022, 2, 28));

    assert_eq!(dt1.until((Unit::Month, dt2))?, 12.months());
    assert_eq!(dt1.until((Unit::Year, dt2))?, 1.year());

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/until/round-cross-unit-boundary.js
#[test]
fn round_cross_unit_boundary() -> Result {
    // Date units.
    let dt1 = date(2022, 1, 1).at(0, 0, 0, 0);
    let dt2 = date(2023, 12, 25).at(0, 0, 0, 0);
    let args = DateTimeDifference::new(dt2)
        .largest(Unit::Year)
        .smallest(Unit::Month)
        .mode(RoundMode::Expand);
    assert_eq!(dt1.until(args)?, 2.years());

    // Time units.
    let dt1 = date(2000, 5, 2).at(0, 0, 0, 0);
    let dt2 = date(2000, 5, 2).at(1, 59, 59, 0);
    let args = DateTimeDifference::new(dt2)
        .largest(Unit::Hour)
        .smallest(Unit::Minute)
        .mode(RoundMode::Expand);
    assert_eq!(dt1.until(args)?, 2.hours());

    // Both.
    let dt1 = date(1970, 1, 1).at(0, 0, 0, 0);
    let dt2 = date(1971, 12, 31).at(23, 59, 59, 999_999_999);
    let args = DateTimeDifference::new(dt2)
        .largest(Unit::Year)
        .smallest(Unit::Microsecond)
        .mode(RoundMode::Expand);
    assert_eq!(dt1.until(args)?, 2.years());

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/until/round-negative-duration.js
#[test]
fn round_negative_duration() -> Result {
    let dt1 = date(2000, 5, 2).at(12, 0, 0, 0);
    let dt2 = date(2000, 5, 5).at(0, 0, 0, 0);
    let args = DateTimeDifference::new(dt1).smallest(Unit::Day).increment(2);
    assert_eq!(dt2.until(args)?, -2.days());
    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/until/round-relative-to-receiver.js
#[test]
fn round_relative_to_receiver() -> Result {
    let dt1 = date(2019, 1, 1).at(0, 0, 0, 0);
    let dt2 = date(2020, 7, 2).at(0, 0, 0, 0);

    let args = DateTimeDifference::new(dt2)
        .smallest(Unit::Year)
        .mode(RoundMode::HalfExpand);
    assert_eq!(dt1.until(args)?, 2.years());

    let args = DateTimeDifference::new(dt1)
        .smallest(Unit::Year)
        .mode(RoundMode::HalfExpand);
    assert_eq!(dt2.until(args)?, -1.years());

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/until/roundingincrement-basic.js
#[test]
fn roundingincrement_basic() -> Result {
    let dt1 = date(2019, 1, 8).at(8, 22, 36, 123_456_789);
    let dt2 = date(2021, 9, 7).at(12, 39, 40, 987_654_321);

    let args = DateTimeDifference::new(dt2)
        .smallest(Unit::Hour)
        .mode(RoundMode::HalfExpand)
        .increment(3);
    assert_eq!(dt1.until(args)?, 973.days().hours(3));

    let args = DateTimeDifference::new(dt2)
        .smallest(Unit::Minute)
        .mode(RoundMode::HalfExpand)
        .increment(30);
    assert_eq!(dt1.until(args)?, 973.days().hours(4).minutes(30));

    let args = DateTimeDifference::new(dt2)
        .smallest(Unit::Second)
        .mode(RoundMode::HalfExpand)
        .increment(15);
    assert_eq!(dt1.until(args)?, 973.days().hours(4).minutes(17).seconds(0));

    let args = DateTimeDifference::new(dt2)
        .smallest(Unit::Millisecond)
        .mode(RoundMode::HalfExpand)
        .increment(10);
    assert_eq!(
        dt1.until(args)?,
        973.days().hours(4).minutes(17).seconds(4).milliseconds(860)
    );

    let args = DateTimeDifference::new(dt2)
        .smallest(Unit::Microsecond)
        .mode(RoundMode::HalfExpand)
        .increment(10);
    assert_eq!(
        dt1.until(args)?,
        973.days()
            .hours(4)
            .minutes(17)
            .seconds(4)
            .milliseconds(864)
            .microseconds(200),
    );

    let args = DateTimeDifference::new(dt2)
        .smallest(Unit::Nanosecond)
        .mode(RoundMode::HalfExpand)
        .increment(10);
    assert_eq!(
        dt1.until(args)?,
        973.days()
            .hours(4)
            .minutes(17)
            .seconds(4)
            .milliseconds(864)
            .microseconds(197)
            .nanoseconds(530),
    );

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/until/roundingincrement-cleanly-divides.js
#[test]
fn roundingincrement_cleanly_divides() {
    let dt1 = date(2019, 1, 8).at(8, 22, 36, 123_456_789);
    let dt2 = date(2021, 9, 7).at(12, 39, 40, 987_654_321);

    for increment in [1, 2, 3, 4, 6, 8, 12] {
        let args = DateTimeDifference::new(dt2)
            .smallest(Unit::Hour)
            .increment(increment);
        assert!(dt1.until(args).is_ok());
    }
    for unit in [Unit::Minute, Unit::Second] {
        for increment in [1, 2, 3, 4, 5, 6, 10, 12, 15, 20, 30] {
            let args = DateTimeDifference::new(dt2)
                .smallest(unit)
                .increment(increment);
            assert!(dt1.until(args).is_ok());
        }
    }
    for unit in [Unit::Millisecond, Unit::Microsecond, Unit::Nanosecond] {
        let increments =
            [1, 2, 4, 5, 8, 10, 20, 25, 40, 50, 100, 125, 200, 250, 500];
        for increment in increments {
            let args = DateTimeDifference::new(dt2)
                .smallest(unit)
                .increment(increment);
            assert!(dt1.until(args).is_ok());
        }
    }
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/until/roundingincrement-does-not-divide.js
#[test]
fn roundingincrement_does_not_divide() {
    let dt1 = date(2019, 1, 8).at(8, 22, 36, 123_456_789);
    let dt2 = date(2021, 9, 7).at(12, 39, 40, 987_654_321);

    let non_divisible = [
        (Unit::Hour, 11),
        (Unit::Minute, 29),
        (Unit::Second, 29),
        (Unit::Millisecond, 29),
        (Unit::Microsecond, 29),
        (Unit::Nanosecond, 29),
    ];
    for (unit, increment) in non_divisible {
        let args =
            DateTimeDifference::new(dt2).smallest(unit).increment(increment);
        assert!(dt1.until(args).is_err());
    }

    let equal_divisible_units = [
        (Unit::Hour, 24),
        (Unit::Minute, 60),
        (Unit::Second, 60),
        (Unit::Millisecond, 1000),
        (Unit::Microsecond, 1000),
        (Unit::Nanosecond, 1000),
    ];
    for (unit, increment) in equal_divisible_units {
        let args =
            DateTimeDifference::new(dt2).smallest(unit).increment(increment);
        assert!(dt1.until(args).is_err());
    }
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/until/roundingmode-ceil.js
///
/// We just test ceil and rely on the span specific tests to cover the other
/// rounding modes.
#[test]
fn roundingmode_ceil() -> Result {
    let dt1 = date(2019, 1, 8).at(8, 22, 36, 123_456_789);
    let dt2 = date(2021, 9, 7).at(12, 39, 40, 987_654_289);
    let mkargs = |smallest, dt| {
        DateTimeDifference::new(dt).smallest(smallest).mode(RoundMode::Ceil)
    };

    assert_eq!(dt1.until(mkargs(Unit::Year, dt2))?, 3.years());
    assert_eq!(dt1.until(mkargs(Unit::Month, dt2))?, 32.months());
    assert_eq!(dt1.until(mkargs(Unit::Week, dt2))?, 140.weeks());
    assert_eq!(dt1.until(mkargs(Unit::Day, dt2))?, 974.days());
    let mut span = 973.days();
    assert_eq!(dt1.until(mkargs(Unit::Hour, dt2))?, span.hours(5));
    span = span.hours(4);
    assert_eq!(dt1.until(mkargs(Unit::Minute, dt2))?, span.minutes(18));
    span = span.minutes(17);
    assert_eq!(dt1.until(mkargs(Unit::Second, dt2))?, span.seconds(5));
    span = span.seconds(4);
    assert_eq!(
        dt1.until(mkargs(Unit::Millisecond, dt2))?,
        span.milliseconds(865)
    );
    span = span.milliseconds(864);
    assert_eq!(
        dt1.until(mkargs(Unit::Microsecond, dt2))?,
        span.microseconds(198)
    );
    span = span.microseconds(197);
    assert_eq!(
        dt1.until(mkargs(Unit::Nanosecond, dt2))?,
        span.nanoseconds(500)
    );

    assert_eq!(dt2.until(mkargs(Unit::Year, dt1))?, -2.years());
    assert_eq!(dt2.until(mkargs(Unit::Month, dt1))?, -31.months());
    assert_eq!(dt2.until(mkargs(Unit::Week, dt1))?, -139.weeks());
    assert_eq!(dt2.until(mkargs(Unit::Day, dt1))?, -973.days());
    let mut span = -973.days();
    assert_eq!(dt2.until(mkargs(Unit::Hour, dt1))?, span.hours(4));
    span = span.hours(4);
    assert_eq!(dt2.until(mkargs(Unit::Minute, dt1))?, span.minutes(17));
    span = span.minutes(17);
    assert_eq!(dt2.until(mkargs(Unit::Second, dt1))?, span.seconds(4));
    span = span.seconds(4);
    assert_eq!(
        dt2.until(mkargs(Unit::Millisecond, dt1))?,
        span.milliseconds(864)
    );
    span = span.milliseconds(864);
    assert_eq!(
        dt2.until(mkargs(Unit::Microsecond, dt1))?,
        span.microseconds(197)
    );
    span = span.microseconds(197);
    assert_eq!(
        dt2.until(mkargs(Unit::Nanosecond, dt1))?,
        span.nanoseconds(500)
    );

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/until/subseconds.js
#[test]
fn subseconds() -> Result {
    let dt1 = date(2020, 2, 1).at(0, 0, 0, 0);
    let dt2 = date(2020, 2, 2).at(0, 0, 0, 250_250_250);

    assert_eq!(
        dt1.until((Unit::Millisecond, dt2))?,
        86400_250.milliseconds().microseconds(250).nanoseconds(250)
    );
    assert_eq!(
        dt1.until((Unit::Microsecond, dt2))?,
        86400_250_250i64.microseconds().nanoseconds(250)
    );
    assert_eq!(
        dt1.until((Unit::Nanosecond, dt2))?,
        86400_250_250_250i64.nanoseconds()
    );

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/until/units-changed.js
#[test]
fn units_changed() -> Result {
    let dt1 = date(2020, 2, 1).at(0, 0, 0, 0);
    let dt2 = date(2021, 2, 1).at(0, 0, 0, 0);

    assert_eq!(dt1.until((Unit::Year, dt2))?, 1.year());
    assert_eq!(dt1.until((Unit::Month, dt2))?, 12.months());
    assert_eq!(dt1.until((Unit::Week, dt2))?, 52.weeks().days(2));
    assert_eq!(dt1.until((Unit::Day, dt2))?, 366.days());
    assert_eq!(dt1.until((Unit::Hour, dt2))?, 8784.hours());
    assert_eq!(dt1.until((Unit::Minute, dt2))?, 527040.minutes());
    assert_eq!(dt1.until((Unit::Second, dt2))?, 31_622_400.seconds());
    assert_eq!(
        dt1.until((Unit::Millisecond, dt2))?,
        31_622_400_000i64.milliseconds()
    );
    assert_eq!(
        dt1.until((Unit::Microsecond, dt2))?,
        31_622_400_000_000i64.microseconds()
    );
    assert_eq!(
        dt1.until((Unit::Nanosecond, dt2))?,
        31_622_400_000_000_000i64.nanoseconds()
    );

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/until/weeks-months-mutually-exclusive.js
#[test]
fn weeks_months_mutually_exclusive() -> Result {
    let dt1 = date(1976, 11, 18).at(15, 23, 30, 123_456_789);
    let dt2 = dt1 + 42.days().hours(3);

    assert_eq!(dt1.until((Unit::Week, dt2))?.to_string(), "P6wT3h");
    assert_eq!(dt1.until((Unit::Month, dt2))?.to_string(), "P1m12dT3h");
    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDateTime/prototype/until/wrapping-at-end-of-month.js
#[test]
fn wrapping_at_end_of_month() -> Result {
    let mkdt = |year, month, day| date(year, month, day).at(0, 0, 0, 0);

    // Span between end of longer month to end of following shorter month.
    let end = mkdt(1970, 2, 28);
    for largest in [Unit::Year, Unit::Month] {
        assert_eq!(mkdt(1970, 1, 28).until((largest, end))?, 1.month());
        assert_eq!(mkdt(1970, 1, 29).until((largest, end))?, 30.days());
        assert_eq!(mkdt(1970, 1, 30).until((largest, end))?, 29.days());
        assert_eq!(mkdt(1970, 1, 31).until((largest, end))?, 28.days());
    }

    // Span between end of leap-year January to end of leap-year February.
    let end = mkdt(1972, 2, 29);
    for largest in [Unit::Year, Unit::Month] {
        assert_eq!(mkdt(1972, 1, 29).until((largest, end))?, 1.month());
        assert_eq!(mkdt(1972, 1, 30).until((largest, end))?, 30.days());
        assert_eq!(mkdt(1972, 1, 31).until((largest, end))?, 29.days());
    }

    // Span between end of longer month to end of not-immediately-following
    // shorter month.
    let end = mkdt(1970, 11, 30);
    for largest in [Unit::Year, Unit::Month] {
        assert_eq!(mkdt(1970, 8, 30).until((largest, end))?, 3.months());
        assert_eq!(
            mkdt(1970, 8, 31).until((largest, end))?,
            2.months().days(30)
        );
    }

    // Span between end of longer month in one year to shorter month in
    // later year.
    let end = mkdt(1973, 4, 30);
    assert_eq!(mkdt(1970, 12, 30).until((Unit::Month, end))?, 28.months());
    assert_eq!(
        mkdt(1970, 12, 30).until((Unit::Year, end))?,
        2.years().months(4)
    );
    assert_eq!(
        mkdt(1970, 12, 31).until((Unit::Month, end))?,
        27.months().days(30),
    );
    assert_eq!(
        mkdt(1970, 12, 31).until((Unit::Year, end))?,
        2.years().months(3).days(30),
    );

    // Span where months passes through a month that's the same length or
    // shorter than either the start or end month.
    assert_eq!(
        mkdt(1970, 1, 29).until((Unit::Month, mkdt(1970, 3, 28)))?,
        1.month().days(28)
    );
    assert_eq!(
        mkdt(1970, 1, 31).until((Unit::Year, mkdt(1971, 5, 30)))?,
        1.year().months(3).days(30)
    );

    // Test that 1-day backoff to maintain date/time sign compatibility
    // backs-off from correct end while moving *backwards*
    // in time and does not interfere with month boundaries.
    //
    // See: https://github.com/tc39/proposal-temporal/issues/2820
    let dt1 = date(2023, 2, 28).at(3, 0, 0, 0);
    let dt2 = date(2023, 4, 1).at(2, 0, 0, 0);
    assert_eq!(dt1.until((Unit::Year, dt2))?, 1.month().days(3).hours(23));

    // Test that 1-day backoff to maintain date/time sign compatibility
    // backs-off from correct end while moving *forwards* in time and does not
    // interfere with month boundaries.
    //
    // See: https://github.com/tc39/proposal-temporal/issues/2820
    let dt1 = date(2023, 3, 1).at(2, 0, 0, 0);
    let dt2 = date(2023, 1, 1).at(3, 0, 0, 0);
    assert_eq!(dt1.until((Unit::Year, dt2))?, -1.month().days(30).hours(23));

    Ok(())
}
