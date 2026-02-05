// This module tries to test the API guarantees on errors in the various
// APIs that can produce errors related to units. This includes through the
// "convenience" APIs on the various datetime types, e.g., `Zoned::until`.
//
// Some of these tests may be duplicative of other tests. But this serves
// as a central point on which to test various rounding configuration errors.
//
// (These also weren't drawn directly from the TC39 262 test suite. They are
// of my own devising. However, much of the behavior being tested comes from
// Temporal.)

use jiff::{civil, tz, SignedDuration, Timestamp, ToSpan, Unit};

use crate::tc39_262::Result;

const DT1: civil::DateTime = civil::DateTime::from_parts(D1, T1);
const DT2: civil::DateTime = civil::DateTime::from_parts(D2, T2);
const D1: civil::Date = civil::date(2000, 1, 1);
const D2: civil::Date = civil::date(2000, 2, 1);
const T1: civil::Time = civil::time(21, 15, 0, 0);
const T2: civil::Time = civil::time(23, 30, 0, 0);

#[test]
fn zoned_datetime_smallest_bigger_than_largest() -> Result {
    let zdt1 = DT1.to_zoned(jiff::tz::TimeZone::UTC)?;
    let zdt2 = DT2.to_zoned(jiff::tz::TimeZone::UTC)?;

    let result = zdt1.until(
        jiff::ZonedDifference::new(&zdt2)
            .smallest(Unit::Year)
            .largest(Unit::Day),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"largest unit ('day') cannot be smaller than smallest unit ('year')",
    );

    // We get an error even in the trivial case.
    let result = zdt1.until(
        jiff::ZonedDifference::new(&zdt2)
            .smallest(Unit::Year)
            .largest(Unit::Day),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"largest unit ('day') cannot be smaller than smallest unit ('year')",
    );

    Ok(())
}

#[test]
fn zoned_datetime_round_invalid_increment() -> Result {
    let zdt1 = DT1.to_zoned(jiff::tz::TimeZone::UTC)?;

    let result =
        zdt1.round(jiff::ZonedRound::new().smallest(Unit::Hour).increment(-1));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding datetime: parameter 'rounding increment' is not in the required range of 1..=1000000000",
    );

    let result =
        zdt1.round(jiff::ZonedRound::new().smallest(Unit::Hour).increment(0));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding datetime: parameter 'rounding increment' is not in the required range of 1..=1000000000",
    );

    let result = zdt1.round(
        jiff::ZonedRound::new().smallest(Unit::Hour).increment(1_000_000_001),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding datetime: parameter 'rounding increment' is not in the required range of 1..=1000000000",
    );

    let result =
        zdt1.round(jiff::ZonedRound::new().smallest(Unit::Hour).increment(11));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding datetime: increment for rounding to 'hours' must divide into `24` evenly",
    );

    let result =
        zdt1.round(jiff::ZonedRound::new().smallest(Unit::Hour).increment(13));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding datetime: increment for rounding to 'hours' must divide into `24` evenly",
    );

    let got = zdt1
        .round(jiff::ZonedRound::new().smallest(Unit::Hour).increment(12))?;
    insta::assert_snapshot!(
        got,
        @"2000-01-02T00:00:00+00:00[UTC]",
    );

    let got = zdt1
        .round(jiff::ZonedRound::new().smallest(Unit::Minute).increment(12))?;
    insta::assert_snapshot!(
        got,
        @"2000-01-01T21:12:00+00:00[UTC]",
    );

    let got =
        D1.at(21, 15, 45, 123_456_789).to_zoned(tz::TimeZone::UTC)?.round(
            jiff::ZonedRound::new().smallest(Unit::Nanosecond).increment(500),
        )?;
    insta::assert_snapshot!(
        got,
        @"2000-01-01T21:15:45.123457+00:00[UTC]",
    );

    let result = zdt1.round(
        jiff::ZonedRound::new().smallest(Unit::Nanosecond).increment(501),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding datetime: increment for rounding to 'nanoseconds' must divide into `1000` evenly",
    );

    let result = zdt1.round(
        jiff::ZonedRound::new().smallest(Unit::Nanosecond).increment(1_000),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding datetime: increment for rounding to 'nanoseconds' must divide into `1000` evenly",
    );

    let got = zdt1.round(jiff::ZonedRound::new().smallest(Unit::Day))?;
    insta::assert_snapshot!(
        got,
        @"2000-01-02T00:00:00+00:00[UTC]",
    );

    let result =
        zdt1.round(jiff::ZonedRound::new().smallest(Unit::Day).increment(2));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding datetime: increment for rounding to 'days' must be equal to `1`",
    );

    Ok(())
}

#[test]
fn civil_datetime_smallest_bigger_than_largest() -> Result {
    let result = DT1.until(
        civil::DateTimeDifference::new(DT2)
            .smallest(Unit::Year)
            .largest(Unit::Day),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"largest unit ('day') cannot be smaller than smallest unit ('year')",
    );

    // We get an error even in the trivial case.
    let result = DT1.until(
        civil::DateTimeDifference::new(DT1)
            .smallest(Unit::Year)
            .largest(Unit::Day),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"largest unit ('day') cannot be smaller than smallest unit ('year')",
    );

    Ok(())
}

#[test]
fn civil_datetime_round_invalid_smallest() -> Result {
    let result = DT1.round(civil::DateTimeRound::new().smallest(Unit::Week));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding datetime: rounding to 'weeks' is not supported",
    );

    let result = DT1.round(civil::DateTimeRound::new().smallest(Unit::Month));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding datetime: rounding to 'months' is not supported",
    );

    let result = DT1.round(civil::DateTimeRound::new().smallest(Unit::Year));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding datetime: rounding to 'years' is not supported",
    );

    Ok(())
}

#[test]
fn civil_datetime_round_invalid_increment() -> Result {
    let result = DT1
        .round(civil::DateTimeRound::new().smallest(Unit::Hour).increment(-1));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding datetime: parameter 'rounding increment' is not in the required range of 1..=1000000000",
    );

    let result = DT1
        .round(civil::DateTimeRound::new().smallest(Unit::Hour).increment(0));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding datetime: parameter 'rounding increment' is not in the required range of 1..=1000000000",
    );

    let result = DT1.round(
        civil::DateTimeRound::new()
            .smallest(Unit::Hour)
            .increment(1_000_000_001),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding datetime: parameter 'rounding increment' is not in the required range of 1..=1000000000",
    );

    let result = DT1
        .round(civil::DateTimeRound::new().smallest(Unit::Hour).increment(11));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding datetime: increment for rounding to 'hours' must divide into `24` evenly",
    );

    let result = DT1
        .round(civil::DateTimeRound::new().smallest(Unit::Hour).increment(13));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding datetime: increment for rounding to 'hours' must divide into `24` evenly",
    );

    let got = DT1.round(
        civil::DateTimeRound::new().smallest(Unit::Hour).increment(12),
    )?;
    insta::assert_snapshot!(
        got,
        @"2000-01-02T00:00:00",
    );

    let got = DT1.round(
        civil::DateTimeRound::new().smallest(Unit::Minute).increment(12),
    )?;
    insta::assert_snapshot!(
        got,
        @"2000-01-01T21:12:00",
    );

    let got = D1.at(21, 15, 45, 123_456_789).round(
        civil::DateTimeRound::new().smallest(Unit::Nanosecond).increment(500),
    )?;
    insta::assert_snapshot!(
        got,
        @"2000-01-01T21:15:45.123457",
    );

    let result = DT1.round(
        civil::DateTimeRound::new().smallest(Unit::Nanosecond).increment(501),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding datetime: increment for rounding to 'nanoseconds' must divide into `1000` evenly",
    );

    let result = DT1.round(
        civil::DateTimeRound::new()
            .smallest(Unit::Nanosecond)
            .increment(1_000),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding datetime: increment for rounding to 'nanoseconds' must divide into `1000` evenly",
    );

    let got = DT1.round(civil::DateTimeRound::new().smallest(Unit::Day))?;
    insta::assert_snapshot!(
        got,
        @"2000-01-02T00:00:00",
    );

    let result = DT1
        .round(civil::DateTimeRound::new().smallest(Unit::Day).increment(2));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding datetime: increment for rounding to 'days' must be equal to `1`",
    );

    Ok(())
}

#[test]
fn civil_date_smallest_bigger_than_largest() -> Result {
    let result = D1.until(
        civil::DateDifference::new(D2).smallest(Unit::Year).largest(Unit::Day),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"largest unit ('day') cannot be smaller than smallest unit ('year')",
    );

    // We get an error even in the trivial case.
    let result = D1.until(
        civil::DateDifference::new(D1).smallest(Unit::Year).largest(Unit::Day),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"largest unit ('day') cannot be smaller than smallest unit ('year')",
    );

    Ok(())
}

#[test]
fn civil_date_largest_less_than_day() -> Result {
    let result = D1.until(civil::DateDifference::new(D2).largest(Unit::Hour));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"'hour' not allowed as a date unit for rounding span",
    );

    // We get an error even in the trivial case.
    let result = D1.until(civil::DateDifference::new(D1).largest(Unit::Hour));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"'hour' not allowed as a date unit for rounding span",
    );

    Ok(())
}

#[test]
fn civil_date_smallest_less_than_day() -> Result {
    let result = D1.until(civil::DateDifference::new(D2).smallest(Unit::Hour));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"'hour' not allowed as a date unit for rounding span",
    );

    // We get an error even in the trivial case.
    let result = D1.until(civil::DateDifference::new(D1).smallest(Unit::Hour));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"'hour' not allowed as a date unit for rounding span",
    );

    Ok(())
}

#[test]
fn civil_date_roundingincrement_day() -> Result {
    let result = D1.until(civil::DateDifference::new(D2).increment(0));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding span: parameter 'rounding increment' is not in the required range of 1..=1000000000",
    );

    let result = D1.until(civil::DateDifference::new(D2).increment(-1));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding span: parameter 'rounding increment' is not in the required range of 1..=1000000000",
    );

    let sp = D1.until(
        civil::DateDifference::new(D2)
            .mode(jiff::RoundMode::Expand)
            .increment(7_304_484),
    )?;
    span_eq!(sp, 7_304_484.days());

    // BREADCRUMBS: Notice that the increment value doesn't necessarily lead
    // to an error unless it specifically causes overflow. Hmmmm.
    //
    // Justification for increment being limited to 1e9:
    // https://github.com/tc39/proposal-temporal/issues/2458#issuecomment-1380742911
    //
    // i.e., Fits into a 32-bit integer.
    //
    // So should I do what we do now and only report an error if rounding
    // actually results in overflow and otherwise just forbid anything over
    // 1e9? Or should I be more strict and enforce unit-specific limits?
    // I feel like doing the former... Seems easier to explain.

    let result = D1.until(
        civil::DateDifference::new(D2)
            .mode(jiff::RoundMode::Expand)
            .increment(7_304_485),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed to convert rounded nanoseconds to span for largest unit set to 'days': parameter 'days' is not in the required range of -7304484..=7304484",
    );

    let sp = D1.until(civil::DateDifference::new(D2).increment(7_304_485))?;
    span_eq!(sp, 0.days());

    Ok(())
}

#[test]
fn civil_time_smallest_bigger_than_largest() -> Result {
    let result = T1.until(
        civil::TimeDifference::new(T2)
            .smallest(Unit::Hour)
            .largest(Unit::Minute),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"largest unit ('minute') cannot be smaller than smallest unit ('hour')",
    );

    // We get an error even in a trivial case.
    let result = T1.until(
        civil::TimeDifference::new(T1)
            .smallest(Unit::Hour)
            .largest(Unit::Minute),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"largest unit ('minute') cannot be smaller than smallest unit ('hour')",
    );

    Ok(())
}

#[test]
fn civil_time_largest_greater_than_hour() -> Result {
    let result = T1.until(civil::TimeDifference::new(T2).largest(Unit::Day));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"'day' not allowed as a time unit for rounding span",
    );

    // We get an error even in a trivial case.
    let result = T1.until(civil::TimeDifference::new(T1).largest(Unit::Day));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"'day' not allowed as a time unit for rounding span",
    );

    Ok(())
}

#[test]
fn civil_time_smallest_greater_than_hour() -> Result {
    let result = T1.until(civil::TimeDifference::new(T2).smallest(Unit::Day));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"'day' not allowed as a time unit for rounding span",
    );

    // We get an error even in a trivial case.
    let result = T1.until(civil::TimeDifference::new(T1).smallest(Unit::Day));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"'day' not allowed as a time unit for rounding span",
    );

    Ok(())
}

#[test]
fn civil_time_checked_add_calendar() -> Result {
    let result = T1.checked_add(1.day());
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"operation can only be performed with units of hours or smaller, but found non-zero 'day' units (operations on `jiff::Timestamp`, `jiff::tz::Offset` and `jiff::civil::Time` don't support calendar units in a `jiff::Span`)",
    );

    let result = civil::Time::MAX.checked_add(1.nanosecond());
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"adding duration to time overflowed",
    );

    // Unlike `Timestamp`, with a civil time, adding calendar units using
    // saturating arithmetic works fine. Since the smallest calendar unit is
    // 1 day, and 1 day overflows all `civil::Time` values, adding in the
    // presence of *any* calendar units always saturates to min/max values.
    assert_eq!(T1.saturating_add(1.day()), civil::Time::MAX);
    assert_eq!(T1.saturating_add(-1.day()), civil::Time::MIN);

    Ok(())
}

#[test]
fn civil_time_round_invalid_smallest() -> Result {
    let result = T1.round(civil::TimeRound::new().smallest(Unit::Day));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding time: rounding to 'days' is not supported",
    );

    let result = T1.round(civil::TimeRound::new().smallest(Unit::Week));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding time: rounding to 'weeks' is not supported",
    );

    let result = T1.round(civil::TimeRound::new().smallest(Unit::Month));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding time: rounding to 'months' is not supported",
    );

    let result = T1.round(civil::TimeRound::new().smallest(Unit::Year));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding time: rounding to 'years' is not supported",
    );

    Ok(())
}

#[test]
fn civil_time_round_invalid_increment() -> Result {
    let result =
        T1.round(civil::TimeRound::new().smallest(Unit::Hour).increment(-1));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding time: parameter 'rounding increment' is not in the required range of 1..=1000000000",
    );

    let result =
        T1.round(civil::TimeRound::new().smallest(Unit::Hour).increment(0));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding time: parameter 'rounding increment' is not in the required range of 1..=1000000000",
    );

    let result = T1.round(
        civil::TimeRound::new().smallest(Unit::Hour).increment(1_000_000_001),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding time: parameter 'rounding increment' is not in the required range of 1..=1000000000",
    );

    let result =
        T1.round(civil::TimeRound::new().smallest(Unit::Hour).increment(11));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding time: increment for rounding to 'hours' must divide into `24` evenly",
    );

    let result =
        T1.round(civil::TimeRound::new().smallest(Unit::Hour).increment(13));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding time: increment for rounding to 'hours' must divide into `24` evenly",
    );

    let got =
        T1.round(civil::TimeRound::new().smallest(Unit::Hour).increment(12))?;
    insta::assert_snapshot!(
        got,
        @"00:00:00",
    );

    let got = T1
        .round(civil::TimeRound::new().smallest(Unit::Minute).increment(12))?;
    insta::assert_snapshot!(
        got,
        @"21:12:00",
    );

    let got = civil::time(21, 15, 45, 123_456_789).round(
        civil::TimeRound::new().smallest(Unit::Nanosecond).increment(500),
    )?;
    insta::assert_snapshot!(
        got,
        @"21:15:45.123457",
    );

    let result = T1.round(
        civil::TimeRound::new().smallest(Unit::Nanosecond).increment(501),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding time: increment for rounding to 'nanoseconds' must divide into `1000` evenly",
    );

    let result = T1.round(
        civil::TimeRound::new().smallest(Unit::Nanosecond).increment(1_000),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding time: increment for rounding to 'nanoseconds' must divide into `1000` evenly",
    );

    Ok(())
}

#[test]
fn signed_duration_smallest_greater_than_hour() -> Result {
    let dur = SignedDuration::from_secs(1);
    let result =
        dur.round(jiff::SignedDurationRound::new().smallest(Unit::Day));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"rounding `jiff::SignedDuration` failed because the smallest unit provided, 'days', is a calendar unit (to round by calendar units, you must use a `jiff::Span`)",
    );

    Ok(())
}

#[test]
fn signed_duration_invalid_increment() -> Result {
    let dur = SignedDuration::new(5 * 60 * 60 + 30 * 60 + 15, 123_456_789);

    let result = dur.round(
        jiff::SignedDurationRound::new().smallest(Unit::Hour).increment(-1),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding signed duration: parameter 'rounding increment' is not in the required range of 1..=1000000000",
    );

    let result = dur.round(
        jiff::SignedDurationRound::new().smallest(Unit::Hour).increment(0),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding signed duration: parameter 'rounding increment' is not in the required range of 1..=1000000000",
    );

    let result = dur.round(
        jiff::SignedDurationRound::new()
            .smallest(Unit::Hour)
            .increment(1_000_000_001),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding signed duration: parameter 'rounding increment' is not in the required range of 1..=1000000000",
    );

    let got = dur.round(
        jiff::SignedDurationRound::new()
            .mode(jiff::RoundMode::Expand)
            .smallest(Unit::Hour)
            .increment(999_999_999),
    )?;
    insta::assert_snapshot!(
        got,
        @"PT999999999H",
    );

    let got = dur.round(
        jiff::SignedDurationRound::new()
            .mode(jiff::RoundMode::Expand)
            .smallest(Unit::Hour)
            .increment(1_000_000_000),
    )?;
    insta::assert_snapshot!(
        got,
        @"PT1000000000H",
    );

    Ok(())
}

#[test]
fn span_smallest_bigger_than_largest() -> Result {
    let result = 15.hours().round(
        jiff::SpanRound::new().smallest(Unit::Hour).largest(Unit::Second),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"largest unit ('second') cannot be smaller than smallest unit ('hour')",
    );

    Ok(())
}

#[test]
fn span_day_no_relative() -> Result {
    let result = 15.hours().round(jiff::SpanRound::new().smallest(Unit::Day));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"error with `smallest` rounding option: using unit 'day' in a span or configuration requires that either a relative reference time be given or `jiff::SpanRelativeTo::days_are_24_hours()` is used to indicate invariant 24-hour days, but neither were provided",
    );

    let sp = 15.hours().round(
        jiff::SpanRound::new().smallest(Unit::Day).days_are_24_hours(),
    )?;
    span_eq!(sp, 1.day());

    Ok(())
}

#[test]
fn span_week_no_relative() -> Result {
    let result = 15.hours().round(
        jiff::SpanRound::new()
            .mode(jiff::RoundMode::Expand)
            .smallest(Unit::Week),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"error with `smallest` rounding option: using unit 'week' in a span or configuration requires that either a relative reference time be given or `jiff::SpanRelativeTo::days_are_24_hours()` is used to indicate invariant 24-hour days, but neither were provided",
    );

    let sp = 15.hours().round(
        jiff::SpanRound::new()
            .mode(jiff::RoundMode::Expand)
            .smallest(Unit::Week)
            .days_are_24_hours(),
    )?;
    span_eq!(sp, 1.week());

    let sp = -15.hours().round(
        jiff::SpanRound::new()
            .mode(jiff::RoundMode::Expand)
            .smallest(Unit::Week)
            .days_are_24_hours(),
    )?;
    span_eq!(sp, -1.week());

    Ok(())
}

#[test]
fn span_month_no_relative_marker() -> Result {
    let result = 15.hours().round(
        jiff::SpanRound::new()
            .mode(jiff::RoundMode::Expand)
            .smallest(Unit::Month),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"error with `smallest` rounding option: using unit 'month' in a span or configuration requires that a relative reference time be given, but none was provided",
    );

    let result = 15.hours().round(
        jiff::SpanRound::new()
            .mode(jiff::RoundMode::Expand)
            .smallest(Unit::Month)
            .days_are_24_hours(),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"using unit 'month' in span or configuration requires that a relative reference time be given (`jiff::SpanRelativeTo::days_are_24_hours()` was given but this only permits using days and weeks without a relative reference time)",
    );

    let sp = 15.hours().round(
        jiff::SpanRound::new()
            .mode(jiff::RoundMode::Expand)
            .smallest(Unit::Month)
            .relative(civil::date(2000, 1, 1)),
    )?;
    span_eq!(sp, 1.month());

    let sp = -15.hours().round(
        jiff::SpanRound::new()
            .mode(jiff::RoundMode::Expand)
            .smallest(Unit::Month)
            .relative(civil::date(2000, 1, 1)),
    )?;
    span_eq!(sp, -1.month());

    Ok(())
}

#[test]
fn span_year_no_relative_marker() -> Result {
    let result = 15.hours().round(
        jiff::SpanRound::new()
            .mode(jiff::RoundMode::Expand)
            .smallest(Unit::Year),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"error with `smallest` rounding option: using unit 'year' in a span or configuration requires that a relative reference time be given, but none was provided",
    );

    let result = 15.hours().round(
        jiff::SpanRound::new()
            .mode(jiff::RoundMode::Expand)
            .smallest(Unit::Year)
            .days_are_24_hours(),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"using unit 'year' in span or configuration requires that a relative reference time be given (`jiff::SpanRelativeTo::days_are_24_hours()` was given but this only permits using days and weeks without a relative reference time)",
    );

    let sp = 15.hours().round(
        jiff::SpanRound::new()
            .mode(jiff::RoundMode::Expand)
            .smallest(Unit::Year)
            .relative(civil::date(2000, 1, 1)),
    )?;
    span_eq!(sp, 1.year());

    let sp = -15.hours().round(
        jiff::SpanRound::new()
            .mode(jiff::RoundMode::Expand)
            .smallest(Unit::Year)
            .relative(civil::date(2000, 1, 1)),
    )?;
    span_eq!(sp, -1.year());

    Ok(())
}

#[test]
fn span_day_to_duration() -> Result {
    let result = SignedDuration::try_from(1.day());
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed to convert span to duration without relative datetime (must use `jiff::Span::to_duration` instead): using unit 'day' in a span or configuration requires that either a relative reference time be given or `jiff::SpanRelativeTo::days_are_24_hours()` is used to indicate invariant 24-hour days, but neither were provided",
    );

    let result = std::time::Duration::try_from(1.day());
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed to convert span to duration without relative datetime (must use `jiff::Span::to_duration` instead): using unit 'day' in a span or configuration requires that either a relative reference time be given or `jiff::SpanRelativeTo::days_are_24_hours()` is used to indicate invariant 24-hour days, but neither were provided",
    );

    Ok(())
}

#[test]
fn span_week_to_duration() -> Result {
    let result = SignedDuration::try_from(1.week());
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed to convert span to duration without relative datetime (must use `jiff::Span::to_duration` instead): using unit 'week' in a span or configuration requires that either a relative reference time be given or `jiff::SpanRelativeTo::days_are_24_hours()` is used to indicate invariant 24-hour days, but neither were provided",
    );

    let result = std::time::Duration::try_from(1.week());
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed to convert span to duration without relative datetime (must use `jiff::Span::to_duration` instead): using unit 'week' in a span or configuration requires that either a relative reference time be given or `jiff::SpanRelativeTo::days_are_24_hours()` is used to indicate invariant 24-hour days, but neither were provided",
    );

    Ok(())
}

#[test]
fn span_month_to_duration() -> Result {
    let result =
        1.month().to_duration(jiff::SpanRelativeTo::days_are_24_hours());
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"could not compute normalized relative span when all days are assumed to be 24 hours: using unit 'month' in span or configuration requires that a relative reference time be given (`jiff::SpanRelativeTo::days_are_24_hours()` was given but this only permits using days and weeks without a relative reference time)",
    );

    let result = SignedDuration::try_from(1.month());
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed to convert span to duration without relative datetime (must use `jiff::Span::to_duration` instead): using unit 'month' in a span or configuration requires that a relative reference time be given, but none was provided",
    );

    let result = std::time::Duration::try_from(1.month());
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed to convert span to duration without relative datetime (must use `jiff::Span::to_duration` instead): using unit 'month' in a span or configuration requires that a relative reference time be given, but none was provided",
    );

    Ok(())
}

#[test]
fn span_year_to_duration() -> Result {
    let result =
        1.year().to_duration(jiff::SpanRelativeTo::days_are_24_hours());
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"could not compute normalized relative span when all days are assumed to be 24 hours: using unit 'year' in span or configuration requires that a relative reference time be given (`jiff::SpanRelativeTo::days_are_24_hours()` was given but this only permits using days and weeks without a relative reference time)",
    );

    let result = SignedDuration::try_from(1.year());
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed to convert span to duration without relative datetime (must use `jiff::Span::to_duration` instead): using unit 'year' in a span or configuration requires that a relative reference time be given, but none was provided",
    );

    let result = std::time::Duration::try_from(1.year());
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed to convert span to duration without relative datetime (must use `jiff::Span::to_duration` instead): using unit 'year' in a span or configuration requires that a relative reference time be given, but none was provided",
    );

    Ok(())
}

#[test]
fn offset_checked_add_calendar() -> Result {
    let result = tz::Offset::UTC.checked_add(1.day());
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"operation can only be performed with units of hours or smaller, but found non-zero 'day' units (operations on `jiff::Timestamp`, `jiff::tz::Offset` and `jiff::civil::Time` don't support calendar units in a `jiff::Span`)",
    );

    Ok(())
}

#[test]
fn offset_saturating_add_calendar() -> Result {
    // TODO: This is weird and should change.
    // See: https://github.com/BurntSushi/jiff/issues/499
    let offset = tz::Offset::MIN.saturating_add(1.day());
    assert_eq!(offset, tz::Offset::MAX);

    let offset = tz::Offset::MIN.saturating_add(24.hours());
    assert_eq!(offset, tz::Offset::from_seconds(-(1 * 3600 + 59 * 60 + 59))?);

    Ok(())
}

#[test]
fn offset_round_invalid_unit() -> Result {
    let offset = tz::Offset::from_seconds(5 * 60 * 60 + 30 * 60 + 30)?;

    let result = offset.round(tz::OffsetRound::new().smallest(Unit::Year));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"'year' not allowed when rounding time zone offset (must use hours, minutes or seconds)",
    );

    let result = offset.round(tz::OffsetRound::new().smallest(Unit::Month));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"'month' not allowed when rounding time zone offset (must use hours, minutes or seconds)",
    );

    let result = offset.round(tz::OffsetRound::new().smallest(Unit::Week));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"'week' not allowed when rounding time zone offset (must use hours, minutes or seconds)",
    );

    let result = offset.round(tz::OffsetRound::new().smallest(Unit::Day));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"'day' not allowed when rounding time zone offset (must use hours, minutes or seconds)",
    );

    let result =
        offset.round(tz::OffsetRound::new().smallest(Unit::Millisecond));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"'millisecond' not allowed when rounding time zone offset (must use hours, minutes or seconds)",
    );

    let result =
        offset.round(tz::OffsetRound::new().smallest(Unit::Microsecond));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"'microsecond' not allowed when rounding time zone offset (must use hours, minutes or seconds)",
    );

    let result =
        offset.round(tz::OffsetRound::new().smallest(Unit::Nanosecond));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"'nanosecond' not allowed when rounding time zone offset (must use hours, minutes or seconds)",
    );

    let got = offset.round(tz::OffsetRound::new().smallest(Unit::Hour))?;
    assert_eq!(got, tz::Offset::from_seconds(6 * 60 * 60)?);

    let got = offset.round(tz::OffsetRound::new().smallest(Unit::Minute))?;
    assert_eq!(got, tz::Offset::from_seconds(5 * 60 * 60 + 31 * 60)?);

    let got = offset
        .round(tz::OffsetRound::new().smallest(Unit::Second).increment(20))?;
    assert_eq!(got, tz::Offset::from_seconds(5 * 60 * 60 + 30 * 60 + 40)?);

    Ok(())
}

#[test]
fn offset_round_invalid_increment() -> Result {
    let offset = tz::Offset::from_seconds(5 * 60 * 60 + 30 * 60 + 30)?;

    let result = offset
        .round(tz::OffsetRound::new().smallest(Unit::Hour).increment(-1));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding time zone offset: parameter 'rounding increment' is not in the required range of 1..=1000000000",
    );

    let result =
        offset.round(tz::OffsetRound::new().smallest(Unit::Hour).increment(0));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding time zone offset: parameter 'rounding increment' is not in the required range of 1..=1000000000",
    );

    let result = offset.round(
        tz::OffsetRound::new().smallest(Unit::Hour).increment(1_000_000_001),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding time zone offset: parameter 'rounding increment' is not in the required range of 1..=1000000000",
    );

    let result = offset.round(
        tz::OffsetRound::new()
            .mode(jiff::RoundMode::Expand)
            .smallest(Unit::Hour)
            .increment(999_999_999),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"rounding time zone offset resulted in a duration that overflows: parameter 'time zone offset total seconds' is not in the required range of -93599..=93599",
    );

    let result = offset.round(
        tz::OffsetRound::new()
            .mode(jiff::RoundMode::Expand)
            .smallest(Unit::Hour)
            .increment(1_000_000_000),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"rounding time zone offset resulted in a duration that overflows: parameter 'time zone offset total seconds' is not in the required range of -93599..=93599",
    );

    let got = offset.round(
        tz::OffsetRound::new().smallest(Unit::Hour).increment(1_000_000_000),
    )?;
    insta::assert_snapshot!(
        got,
        @"+00",
    );

    let got = offset.round(
        tz::OffsetRound::new()
            .mode(jiff::RoundMode::Expand)
            .smallest(Unit::Hour)
            .increment(25),
    )?;
    insta::assert_snapshot!(
        got,
        @"+25",
    );

    let result = offset.round(
        tz::OffsetRound::new()
            .mode(jiff::RoundMode::Expand)
            .smallest(Unit::Hour)
            .increment(26),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"rounding time zone offset resulted in a duration that overflows: parameter 'time zone offset total seconds' is not in the required range of -93599..=93599",
    );

    Ok(())
}

#[test]
fn timestamp_checked_add_calendar() -> Result {
    let result = Timestamp::UNIX_EPOCH.checked_add(1.day());
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"operation can only be performed with units of hours or smaller, but found non-zero 'day' units (operations on `jiff::Timestamp`, `jiff::tz::Offset` and `jiff::civil::Time` don't support calendar units in a `jiff::Span`)",
    );

    Ok(())
}

#[test]
fn timestamp_saturating_add_calendar() -> Result {
    let result = Timestamp::UNIX_EPOCH.saturating_add(1.day());
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"operation can only be performed with units of hours or smaller, but found non-zero 'day' units (operations on `jiff::Timestamp`, `jiff::tz::Offset` and `jiff::civil::Time` don't support calendar units in a `jiff::Span`)",
    );

    Ok(())
}

#[test]
fn timestamp_round_invalid_unit() -> Result {
    let ts: Timestamp = "2024-03-05T17:31:15.123456789Z".parse()?;

    let result = ts.round(jiff::TimestampRound::new().smallest(Unit::Day));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding timestamp: rounding to 'days' is not supported",
    );

    let result = ts.round(jiff::TimestampRound::new().smallest(Unit::Week));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding timestamp: rounding to 'weeks' is not supported",
    );

    let result = ts.round(jiff::TimestampRound::new().smallest(Unit::Month));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding timestamp: rounding to 'months' is not supported",
    );

    let result = ts.round(jiff::TimestampRound::new().smallest(Unit::Year));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding timestamp: rounding to 'years' is not supported",
    );

    Ok(())
}

#[test]
fn timestamp_round_invalid_increment_hour() -> Result {
    let ts: Timestamp = "2024-03-05T17:31:15.123456789Z".parse()?;

    let result = ts
        .round(jiff::TimestampRound::new().smallest(Unit::Hour).increment(11));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding timestamp: increment for rounding to 'hours' must divide into `24` evenly",
    );

    let result = ts
        .round(jiff::TimestampRound::new().smallest(Unit::Hour).increment(13));
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding timestamp: increment for rounding to 'hours' must divide into `24` evenly",
    );

    let got = ts.round(
        jiff::TimestampRound::new().smallest(Unit::Hour).increment(12),
    )?;
    insta::assert_snapshot!(
        got,
        @"2024-03-05T12:00:00Z",
    );

    Ok(())
}

#[test]
fn timestamp_round_invalid_increment_minute() -> Result {
    let ts: Timestamp = "2024-03-05T17:31:15.123456789Z".parse()?;

    let result = ts.round(
        jiff::TimestampRound::new().smallest(Unit::Minute).increment(719),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding timestamp: increment for rounding to 'minutes' must divide into `1440` evenly",
    );

    let result = ts.round(
        jiff::TimestampRound::new().smallest(Unit::Minute).increment(721),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding timestamp: increment for rounding to 'minutes' must divide into `1440` evenly",
    );

    let got = ts.round(
        jiff::TimestampRound::new().smallest(Unit::Minute).increment(720),
    )?;
    insta::assert_snapshot!(
        got,
        @"2024-03-05T12:00:00Z",
    );

    Ok(())
}

#[test]
fn timestamp_round_invalid_increment_second() -> Result {
    let ts: Timestamp = "2024-03-05T17:31:15.123456789Z".parse()?;

    let result = ts.round(
        jiff::TimestampRound::new().smallest(Unit::Second).increment(43_199),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding timestamp: increment for rounding to 'seconds' must divide into `86400` evenly",
    );

    let result = ts.round(
        jiff::TimestampRound::new().smallest(Unit::Second).increment(43_201),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding timestamp: increment for rounding to 'seconds' must divide into `86400` evenly",
    );

    let got = ts.round(
        jiff::TimestampRound::new().smallest(Unit::Second).increment(43_200),
    )?;
    insta::assert_snapshot!(
        got,
        @"2024-03-05T12:00:00Z",
    );

    Ok(())
}

#[test]
fn timestamp_round_invalid_increment_millisecond() -> Result {
    let ts: Timestamp = "2024-03-05T17:31:15.123456789Z".parse()?;

    let result = ts.round(
        jiff::TimestampRound::new()
            .smallest(Unit::Millisecond)
            .increment(43_199_000),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding timestamp: increment for rounding to 'milliseconds' must divide into `86400000` evenly",
    );

    let result = ts.round(
        jiff::TimestampRound::new()
            .smallest(Unit::Millisecond)
            .increment(43_201_000),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding timestamp: increment for rounding to 'milliseconds' must divide into `86400000` evenly",
    );

    let got = ts.round(
        jiff::TimestampRound::new()
            .smallest(Unit::Millisecond)
            .increment(43_200_000),
    )?;
    insta::assert_snapshot!(
        got,
        @"2024-03-05T12:00:00Z",
    );

    Ok(())
}

#[test]
fn timestamp_round_invalid_increment_microsecond() -> Result {
    let ts: Timestamp = "2024-03-05T17:31:15.123456789Z".parse()?;

    let result = ts.round(
        jiff::TimestampRound::new().smallest(Unit::Microsecond).increment(7),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding timestamp: increment for rounding to 'microseconds' must divide into `86400000000` evenly",
    );

    // This increment is technically legal according to our divisibility
    // rules, but exceeds the `1..=1_000_000_000` range.
    let result = ts.round(
        jiff::TimestampRound::new()
            .smallest(Unit::Microsecond)
            .increment(43_200_000_000),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding timestamp: parameter 'rounding increment' is not in the required range of 1..=1000000000",
    );

    Ok(())
}

#[test]
fn timestamp_round_invalid_increment_nanosecond() -> Result {
    let ts: Timestamp = "2024-03-05T17:31:15.123456789Z".parse()?;

    let result = ts.round(
        jiff::TimestampRound::new().smallest(Unit::Nanosecond).increment(7),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding timestamp: increment for rounding to 'nanoseconds' must divide into `86400000000000` evenly",
    );

    // This increment is technically legal according to our divisibility
    // rules, but exceeds the `1..=1_000_000_000` range.
    let result = ts.round(
        jiff::TimestampRound::new()
            .smallest(Unit::Nanosecond)
            .increment(43_200_000_000_000),
    );
    insta::assert_snapshot!(
        result.unwrap_err(),
        @"failed rounding timestamp: parameter 'rounding increment' is not in the required range of 1..=1000000000",
    );

    let got = ts.round(
        jiff::TimestampRound::new()
            .smallest(Unit::Nanosecond)
            .increment(1_000_000_000),
    )?;
    insta::assert_snapshot!(
        got,
        @"2024-03-05T17:31:15Z",
    );

    // Use a somewhat extreme value.
    let got = ts.round(
        jiff::TimestampRound::new()
            .smallest(Unit::Nanosecond)
            .increment(960_000_000),
    )?;
    insta::assert_snapshot!(
        got,
        @"2024-03-05T17:31:14.88Z",
    );

    Ok(())
}
