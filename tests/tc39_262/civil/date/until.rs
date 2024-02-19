use jiff::{
    civil::{date, Date, DateDifference},
    RoundMode, Span, ToSpan, Unit,
};

use crate::tc39_262::Result;

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDate/prototype/until/basic.js
#[test]
fn basic() {
    let d1 = date(1969, 7, 24);
    let d2 = date(1969, 10, 5);
    assert_eq!(d2 - d1, 73.days());

    let d2 = date(1996, 3, 3);
    assert_eq!(d2 - d1, 9719.days());

    let d2 = date(2019, 7, 24);
    assert_eq!(d2 - d1, 18262.days());
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDate/prototype/until/largestunit-higher-units.js
#[test]
fn largestunit_higher_units() -> Result {
    let d1 = date(1969, 7, 24);
    let d2 = date(2019, 7, 24);
    assert_eq!(d1.until((Unit::Year, d2))?, 50.years());

    let d1 = date(2020, 2, 1);
    let d2 = date(2021, 2, 1);
    assert_eq!(d1.until((Unit::Year, d2))?, 1.year());
    assert_eq!(d1.until((Unit::Month, d2))?, 12.months());
    assert_eq!(d1.until((Unit::Week, d2))?, 52.weeks().days(2));

    let d1 = date(2021, 2, 28);
    let d2 = date(2022, 2, 28);
    assert_eq!(d1.until((Unit::Year, d2))?, 1.year());
    assert_eq!(d1.until((Unit::Month, d2))?, 12.months());
    assert_eq!(d1.until((Unit::Week, d2))?, 52.weeks().days(1));

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDate/prototype/until/largestunit-smallestunit-mismatch.js
#[test]
fn largestunit_smallestunit_mismatch() {
    let d1 = date(2000, 5, 2);
    let d2 = date(2001, 6, 3);

    let units = [Unit::Year, Unit::Month, Unit::Week, Unit::Day];
    for largest in 1..units.len() {
        for smallest in 0..largest {
            let (largest, smallest) = (units[largest], units[smallest]);
            let args =
                DateDifference::new(d2).largest(largest).smallest(smallest);
            assert!(
                d1.until(args).is_err(),
                "Date::until should fail with largest units {largest:?} \
                 and smallest units {smallest:?}",
            );
        }
    }
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDate/prototype/until/round-cross-unit-boundary.js
#[test]
fn round_cross_unit_boundary() -> Result {
    let d1 = date(2022, 1, 1);
    let d2 = date(2023, 12, 25);
    let args = DateDifference::new(d2)
        .largest(Unit::Year)
        .smallest(Unit::Month)
        .mode(RoundMode::Expand);
    assert_eq!(d1.until(args)?, 2.years());
    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDate/prototype/until/rounding-relative.js
#[test]
fn rounding_relative() -> Result {
    let d1 = date(2019, 1, 1);
    let d2 = date(2019, 2, 15);

    let args = DateDifference::new(d2)
        .smallest(Unit::Month)
        .mode(RoundMode::HalfExpand);
    assert_eq!(d1.until(args)?, 2.months());

    let args = DateDifference::new(d1)
        .smallest(Unit::Month)
        .mode(RoundMode::HalfExpand);
    assert_eq!(d2.until(args)?, -1.month());

    let cases = [
        ("2019-03-01", "2019-01-29", 1, 1),
        ("2019-01-29", "2019-03-01", -1, -3),
        ("2019-03-29", "2019-01-30", 1, 29),
        ("2019-01-30", "2019-03-29", -1, -29),
        ("2019-03-30", "2019-01-31", 1, 30),
        ("2019-01-31", "2019-03-30", -1, -28),
        ("2019-03-31", "2019-01-31", 2, 0),
        ("2019-01-31", "2019-03-31", -2, 0),
    ];
    for (end, start, months, days) in cases {
        let (start, end): (Date, Date) = (start.parse()?, end.parse()?);
        let span = start.until((Unit::Month, end))?;
        assert_eq!(span, Span::new().months(months).days(days));
    }
    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDate/prototype/until/roundingincrement.js
#[test]
fn roundingincrement() -> Result {
    let d1 = date(2019, 1, 8);
    let d2 = date(2021, 9, 7);

    let args = DateDifference::new(d2)
        .smallest(Unit::Year)
        .mode(RoundMode::HalfExpand)
        .increment(4);
    assert_eq!(d1.until(args)?, 4.years());

    let args = DateDifference::new(d2)
        .smallest(Unit::Month)
        .mode(RoundMode::HalfExpand)
        .increment(10);
    assert_eq!(d1.until(args)?, 30.months());

    let args = DateDifference::new(d2)
        .smallest(Unit::Week)
        .mode(RoundMode::HalfExpand)
        .increment(12);
    assert_eq!(d1.until(args)?, 144.weeks());

    let args = DateDifference::new(d2)
        .smallest(Unit::Day)
        .mode(RoundMode::HalfExpand)
        .increment(100);
    assert_eq!(d1.until(args)?, 1000.days());

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDate/prototype/until/roundingmode-ceil.js
///
/// We just test one rounding mode and rely on tests for span rounding
/// specifically to cover the other modes.
#[test]
fn roundingmode_ceil() -> Result {
    let d1 = date(2019, 1, 8);
    let d2 = date(2021, 9, 7);

    let args =
        DateDifference::new(d2).smallest(Unit::Year).mode(RoundMode::Ceil);
    assert_eq!(d1.until(args)?, 3.years());
    let args =
        DateDifference::new(d1).smallest(Unit::Year).mode(RoundMode::Ceil);
    assert_eq!(d2.until(args)?, -2.years());

    let args =
        DateDifference::new(d2).smallest(Unit::Month).mode(RoundMode::Ceil);
    assert_eq!(d1.until(args)?, 32.months());
    let args =
        DateDifference::new(d1).smallest(Unit::Month).mode(RoundMode::Ceil);
    assert_eq!(d2.until(args)?, -31.months());

    let args =
        DateDifference::new(d2).smallest(Unit::Week).mode(RoundMode::Ceil);
    assert_eq!(d1.until(args)?, 139.weeks());
    let args =
        DateDifference::new(d1).smallest(Unit::Week).mode(RoundMode::Ceil);
    assert_eq!(d2.until(args)?, -139.weeks());

    let args =
        DateDifference::new(d2).smallest(Unit::Day).mode(RoundMode::Ceil);
    assert_eq!(d1.until(args)?, 973.days());
    let args =
        DateDifference::new(d1).smallest(Unit::Day).mode(RoundMode::Ceil);
    assert_eq!(d2.until(args)?, -973.days());

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDate/prototype/until/smallestunit-higher-units.js
#[test]
fn smallestunit_higher_units() -> Result {
    let d1 = date(2019, 1, 8);
    let d2 = date(2021, 9, 7);

    let args = DateDifference::new(d2)
        .smallest(Unit::Year)
        .mode(RoundMode::HalfExpand);
    assert_eq!(d1.until(args)?, 3.years());

    let args = DateDifference::new(d2)
        .smallest(Unit::Month)
        .mode(RoundMode::HalfExpand);
    assert_eq!(d1.until(args)?, 32.months());

    let args = DateDifference::new(d2)
        .smallest(Unit::Week)
        .mode(RoundMode::HalfExpand);
    assert_eq!(d1.until(args)?, 139.weeks());

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDate/prototype/until/weeks-months.js
#[test]
fn weeks_months() -> Result {
    let d1 = date(1969, 7, 24);
    let d2 = date(1969, 9, 4);

    assert_eq!(d1.until((Unit::Week, d2))?, 6.weeks());
    assert_eq!(d1.until((Unit::Month, d2))?, 1.month().days(11));

    Ok(())
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainDate/prototype/until/wrapping-at-end-of-month.js
#[test]
fn wrapping_at_end_of_month() -> Result {
    // Span between end of longer month to end of following shorter month.
    let end = date(1970, 2, 28);
    for largest in [Unit::Year, Unit::Month] {
        assert_eq!(date(1970, 1, 28).until((largest, end))?, 1.month());
        assert_eq!(date(1970, 1, 29).until((largest, end))?, 30.days());
        assert_eq!(date(1970, 1, 30).until((largest, end))?, 29.days());
        assert_eq!(date(1970, 1, 31).until((largest, end))?, 28.days());
    }

    // Span between end of leap-year January to end of leap-year February.
    let end = date(1972, 2, 29);
    for largest in [Unit::Year, Unit::Month] {
        assert_eq!(date(1972, 1, 29).until((largest, end))?, 1.month());
        assert_eq!(date(1972, 1, 30).until((largest, end))?, 30.days());
        assert_eq!(date(1972, 1, 31).until((largest, end))?, 29.days());
    }

    // Span between end of longer month to end of not-immediately-following
    // shorter month.
    let end = date(1970, 11, 30);
    for largest in [Unit::Year, Unit::Month] {
        assert_eq!(date(1970, 8, 30).until((largest, end))?, 3.months());
        assert_eq!(
            date(1970, 8, 31).until((largest, end))?,
            2.months().days(30),
        );
    }

    // Span between end of longer month in one year to shorter month in
    // later year.
    let end = date(1973, 4, 30);
    assert_eq!(date(1970, 12, 30).until((Unit::Month, end))?, 28.months());
    assert_eq!(
        date(1970, 12, 30).until((Unit::Year, end))?,
        2.years().months(4),
    );
    assert_eq!(
        date(1970, 12, 31).until((Unit::Month, end))?,
        27.months().days(30),
    );
    assert_eq!(
        date(1970, 12, 31).until((Unit::Year, end))?,
        2.years().months(3).days(30),
    );

    // Span where months passes through a month that's the same length or
    // shorter than either the start or end month
    assert_eq!(
        date(1970, 1, 29).until((Unit::Month, date(1970, 3, 28)))?,
        1.month().days(28),
    );
    assert_eq!(
        date(1970, 1, 31).until((Unit::Year, date(1971, 5, 30)))?,
        1.year().months(3).days(30),
    );

    Ok(())
}
