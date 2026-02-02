/*!
This module provides logic for validating rounding increments.

Each of the types we support rounding for have their own logic for how the
rounding increment is validated. For example, when rounding timestamps, only
rounding increments up to hours are supported. But when rounding datetimes,
rounding increments up to days are supported. Similarly, rounding increments
for time units must divide evenly into 1 unit of the next highest unit.
*/

use crate::{
    error::{util::RoundingIncrementError as E, Error, ErrorContext},
    util::{b, rangeint::RFrom, t},
    Unit,
};

/// Validates the given rounding increment for the given unit.
///
/// This validation ensures the rounding increment is valid for rounding spans.
pub(crate) fn for_span_ranged(
    unit: Unit,
    increment: i64,
) -> Result<t::NoUnits128, Error> {
    for_span(unit, increment).map(t::NoUnits::borked).map(t::NoUnits128::rfrom)
}

pub(crate) fn for_span(unit: Unit, increment: i64) -> Result<i64, Error> {
    // Indexed by `Unit`.
    static LIMIT: &[i64] = &[
        b::NANOS_PER_MICRO,
        b::MICROS_PER_MILLI,
        b::MILLIS_PER_SEC,
        b::SECS_PER_MIN,
        b::MINS_PER_HOUR,
        b::HOURS_PER_CIVIL_DAY,
    ];
    // We allow any kind of increment for calendar units, but for time units,
    // they have to divide evenly into the next highest unit (and also be less
    // than that). The reason for this is that calendar units vary, where as
    // for time units, given a balanced span, you know that time units will
    // always spill over into days so that hours/minutes/... will never exceed
    // 24/60/...
    if unit >= Unit::Day {
        Ok(increment)
    } else {
        get_with_limit(unit, increment, LIMIT).context(E::ForSpan)
    }
}

/// Validates the given rounding increment for the given unit.
///
/// This validation ensures the rounding increment is valid for rounding
/// datetimes (both civil and time zone aware).
pub(crate) fn for_datetime(unit: Unit, increment: i64) -> Result<i64, Error> {
    // Indexed by `Unit`.
    static LIMIT: &[i64] = &[
        b::NANOS_PER_MICRO,
        b::MICROS_PER_MILLI,
        b::MILLIS_PER_SEC,
        b::SECS_PER_MIN,
        b::MINS_PER_HOUR,
        b::HOURS_PER_CIVIL_DAY,
        2,
    ];
    get_with_limit(unit, increment, LIMIT).context(E::ForDateTime)
}

/// Validates the given rounding increment for the given unit.
///
/// This validation ensures the rounding increment is valid for rounding
/// civil times.
pub(crate) fn for_time(unit: Unit, increment: i64) -> Result<i64, Error> {
    // Indexed by `Unit`.
    static LIMIT: &[i64] = &[
        b::NANOS_PER_MICRO,
        b::MICROS_PER_MILLI,
        b::MILLIS_PER_SEC,
        b::SECS_PER_MIN,
        b::MINS_PER_HOUR,
        b::HOURS_PER_CIVIL_DAY,
    ];
    get_with_limit(unit, increment, LIMIT).context(E::ForTime)
}

/// Validates the given rounding increment for the given unit.
///
/// This validation ensures the rounding increment is valid for rounding
/// timestamps.
pub(crate) fn for_timestamp(unit: Unit, increment: i64) -> Result<i64, Error> {
    // Indexed by `Unit`.
    static MAX: &[i64] = &[
        b::NANOS_PER_CIVIL_DAY,
        b::MICROS_PER_CIVIL_DAY,
        b::MILLIS_PER_CIVIL_DAY,
        b::SECS_PER_CIVIL_DAY,
        b::MINS_PER_CIVIL_DAY,
        b::HOURS_PER_CIVIL_DAY,
    ];
    get_with_max(unit, increment, MAX).context(E::ForTimestamp)
}

fn get_with_limit(
    unit: Unit,
    increment: i64,
    limit: &[i64],
) -> Result<i64, E> {
    if increment <= 0 {
        return Err(E::GreaterThanZero { unit });
    }
    let Some(&must_divide) = limit.get(unit as usize) else {
        return Err(E::Unsupported { unit });
    };
    if increment >= must_divide || must_divide % increment != 0 {
        Err(E::InvalidDivide { unit, must_divide })
    } else {
        Ok(increment)
    }
}

fn get_with_max(unit: Unit, increment: i64, max: &[i64]) -> Result<i64, E> {
    if increment <= 0 {
        return Err(E::GreaterThanZero { unit });
    }
    let Some(&must_divide) = max.get(unit as usize) else {
        return Err(E::Unsupported { unit });
    };
    if increment > must_divide || must_divide % increment != 0 {
        Err(E::InvalidDivide { unit, must_divide })
    } else {
        Ok(increment)
    }
}
