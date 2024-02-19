use jiff::{civil::DateTime, round::Unit, ToSpan};

/// Test that 1-day backoff to maintain date/time sign compatibility backs-off
/// from correct end while moving *forwards* in time and does not interfere
/// with month boundaries.
///
/// Ref: https://github.com/tc39/proposal-temporal/issues/2820
#[test]
fn one_day_backoff1() {
    let dt1 = DateTime::constant(2023, 2, 28, 3, 0, 0, 0);
    let dt2 = DateTime::constant(2023, 4, 1, 2, 0, 0, 0);
    let span = dt1.since_with_largest_unit(Unit::Year, dt2).unwrap();
    assert_eq!(span, -1.month().days(3).hours(23));
}

/// Test that 1-day backoff to maintain date/time sign compatibility backs-off
/// from correct end while moving *forwards* in time and does not interfere
/// with month boundaries.
///
/// Ref: https://github.com/tc39/proposal-temporal/issues/2820
#[test]
fn one_day_backoff2() {
    let dt1 = DateTime::constant(2023, 3, 1, 2, 0, 0, 0);
    let dt2 = DateTime::constant(2023, 1, 1, 3, 0, 0, 0);
    let span = dt1.since_with_largest_unit(Unit::Year, dt2).unwrap();
    assert_eq!(span, 1.month().days(30).hours(23));
}
