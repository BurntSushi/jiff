/*!
A collection of datetime related utility functions.

These routines are written on Rust's native primitive integer types instead of
Jiff's internal ranged integer types. In some sense, we should do the latter,
but in practice there are two problems.

Firstly, some of these routines need to be `const` so that we can use them in
`const` constructors like `Date::constant`. But Jiff's ranged integers are
nowhere near able to be `const`.

Secondly, some of these routines are difficult to write using Jiff's
ranged integers. Particularly the more complicated ones like the conversions
between Unix epoch days and Gregorian calendar dates. I was able to do it,
but when benchmarking, I noticed that the codegen was not as good as when
normal primitive integers are used. This generally shouldn't happen, because
Jiff's ranged integers are _supposed_ to compile away completely when debug
assertions aren't enabled. Alas, it's just simpler to write it out this way.

Note that these routines assume that their inputs are within Jiff's defined
ranges. For example, `year` must be in the range `-9999..=9999`.
*/

use crate::util::t;

/// Returns true if and only if the given year is a leap year.
///
/// A leap year is a year with 366 days. Typical years have 365 days.
#[inline]
pub(crate) const fn is_leap_year(year: i16) -> bool {
    // From: https://github.com/BurntSushi/jiff/pull/23
    let d = if year % 25 != 0 { 4 } else { 16 };
    (year % d) == 0
}

/// Return the number of days in the given month.
#[inline]
pub(crate) const fn days_in_month(year: i16, month: i8) -> i8 {
    // From: https://github.com/BurntSushi/jiff/pull/23
    if month == 2 {
        if is_leap_year(year) {
            29
        } else {
            28
        }
    } else {
        30 | (month ^ month >> 3)
    }
}

/// Converts a Gregorian date to days since the Unix epoch.
///
/// This is Neri-Schneider. There's no branching or divisions.
///
/// Ref: https://github.com/cassioneri/eaf/blob/684d3cc32d14eee371d0abe4f683d6d6a49ed5c1/algorithms/neri_schneider.hpp#L83
#[inline(always)]
#[allow(non_upper_case_globals, non_snake_case)]
pub(crate) fn to_unix_epoch_day(year: i16, month: i8, day: i8) -> i32 {
    const s: u32 = 82;
    const K: u32 = 719468 + 146097 * s;
    const L: u32 = 400 * s;

    let year = year as u32;
    let month = month as u32;
    let day = day as u32;

    let J = month <= 2;
    let Y = year.wrapping_add(L).wrapping_sub(J as u32);
    let M = if J { month + 12 } else { month };
    let D = day - 1;
    let C = Y / 100;

    let y_star = 1461 * Y / 4 - C + C / 4;
    let m_star = (979 * M - 2919) / 32;
    let N = y_star + m_star + D;

    let N_U = N.wrapping_sub(K);
    N_U as i32
}

/// Converts days since the Unix epoch to a Gregorian date.
///
/// This is Neri-Schneider. There's no branching or divisions.
///
/// Ref: <https://github.com/cassioneri/eaf/blob/684d3cc32d14eee371d0abe4f683d6d6a49ed5c1/algorithms/neri_schneider.hpp#L40C3-L40C34>
#[inline(always)]
#[allow(non_upper_case_globals, non_snake_case)]
pub(crate) fn from_unix_epoch_day(days: i32) -> (i16, i8, i8) {
    const s: u32 = 82;
    const K: u32 = 719468 + 146097 * s;
    const L: u32 = 400 * s;

    let N_U = days as u32;
    let N = N_U.wrapping_add(K);

    let N_1 = 4 * N + 3;
    let C = N_1 / 146097;
    let N_C = (N_1 % 146097) / 4;

    let N_2 = 4 * N_C + 3;
    let P_2 = 2939745 * u64::from(N_2);
    let Z = (P_2 / 4294967296) as u32;
    let N_Y = (P_2 % 4294967296) as u32 / 2939745 / 4;
    let Y = 100 * C + Z;

    let N_3 = 2141 * N_Y + 197913;
    let M = N_3 / 65536;
    let D = (N_3 % 65536) / 2141;

    let J = N_Y >= 306;
    let year = Y.wrapping_sub(L).wrapping_add(J as u32) as i16;
    let month = (if J { M - 12 } else { M }) as i8;
    let day = (D + 1) as i8;
    (year, month, day)
}

/// Converts `HH:MM:SS` to a second in a single civil day.
#[inline(always)]
pub(crate) fn to_day_second(hour: i8, minute: i8, second: i8) -> i32 {
    let mut seconds: i32 = 0;
    seconds += i32::from(hour) * (t::SECONDS_PER_HOUR.value() as i32);
    seconds += i32::from(minute) * (t::SECONDS_PER_MINUTE.value() as i32);
    seconds += i32::from(second);
    seconds
}

/// Converts a second in a single civil day to `HH:MM::SS`.
#[inline(always)]
pub(crate) fn from_day_second(mut seconds: i32) -> (i8, i8, i8) {
    let (mut hour, mut minute, mut second) = (0, 0, 0);
    if seconds != 0 {
        hour = (seconds / t::SECONDS_PER_HOUR.value() as i32) as i8;
        seconds %= t::SECONDS_PER_HOUR.value() as i32;
        if seconds != 0 {
            minute = (seconds / t::SECONDS_PER_MINUTE.value() as i32) as i8;
            second = (seconds % t::SECONDS_PER_MINUTE.value() as i32) as i8;
        }
    }
    (hour, minute, second)
}

/// Converts `HH:MM:SS.nnnnnnnnn` to a nanosecond in a single civil day.
#[inline(always)]
pub(crate) fn to_day_nanosecond(
    hour: i8,
    minute: i8,
    second: i8,
    subsec: i32,
) -> i64 {
    let mut nanos: i64 = 0;
    nanos += i64::from(hour) * t::NANOS_PER_HOUR.value();
    nanos += i64::from(minute) * t::NANOS_PER_MINUTE.value();
    nanos += i64::from(second) * t::NANOS_PER_SECOND.value();
    nanos += i64::from(subsec);
    nanos
}

/// Converts a nanosecond in a single civil day to `HH:MM::SS.nnnnnnnnn`.
#[inline(always)]
pub(crate) fn from_day_nanosecond(mut nanos: i64) -> (i8, i8, i8, i32) {
    let (mut hour, mut minute, mut second, mut subsec) = (0, 0, 0, 0);
    if nanos != 0 {
        hour = (nanos / t::NANOS_PER_HOUR.value()) as i8;
        nanos %= t::NANOS_PER_HOUR.value();
        if nanos != 0 {
            minute = (nanos / t::NANOS_PER_MINUTE.value()) as i8;
            nanos %= t::NANOS_PER_MINUTE.value();
            if nanos != 0 {
                second = (nanos / t::NANOS_PER_SECOND.value()) as i8;
                subsec = (nanos % t::NANOS_PER_SECOND.value()) as i32;
            }
        }
    }
    (hour, minute, second, subsec)
}

/// Converts a Unix timestamp with an offset to a Gregorian datetime.
#[inline(always)]
pub(crate) fn timestamp_to_datetime_zulu(
    mut secs: i64,
    mut subsec: i32,
    offset: i32,
) -> (i16, i8, i8, i8, i8, i8, i32) {
    secs += i64::from(offset);
    let mut days = secs.div_euclid(86_400) as i32;
    secs = secs.rem_euclid(86_400);
    if subsec < 0 {
        if secs > 0 {
            secs -= 1;
            subsec += t::NANOS_PER_SECOND.value() as i32;
        } else {
            days -= 1;
            secs += 86_399;
            subsec += 1_000_000_000;
        }
    }

    let (year, month, day) = from_unix_epoch_day(days);
    let hour = (secs / t::SECONDS_PER_HOUR.value()) as i8;
    secs %= t::SECONDS_PER_HOUR.value();
    let minute = (secs / t::SECONDS_PER_MINUTE.value()) as i8;
    let second = (secs % t::SECONDS_PER_MINUTE.value()) as i8;
    (year, month, day, hour, minute, second, subsec)
}

/// Converts a Gregorian datetime and its offset to a Unix timestamp.
#[inline(always)]
pub(crate) fn datetime_zulu_to_timestamp(
    year: i16,
    month: i8,
    day: i8,
    hour: i8,
    minute: i8,
    second: i8,
    mut subsec: i32,
    offset: i32,
) -> (i64, i32) {
    let day = to_unix_epoch_day(year, month, day);
    let mut secs = i64::from(day) * t::SECONDS_PER_CIVIL_DAY.value();
    secs += i64::from(hour) * t::SECONDS_PER_HOUR.value();
    secs += i64::from(minute) * t::SECONDS_PER_MINUTE.value();
    secs += i64::from(second);
    secs -= i64::from(offset);
    if day < 0 && subsec != 0 {
        secs += 1;
        subsec -= 1_000_000_000;
    }
    (secs, subsec)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn t_is_leap_year() {
        assert!(is_leap_year(2024));
        assert!(!is_leap_year(2023));
        assert!(!is_leap_year(2025));
        assert!(is_leap_year(2000));
        assert!(!is_leap_year(1900));
        assert!(!is_leap_year(1800));
        assert!(!is_leap_year(1700));
        assert!(is_leap_year(1600));
        assert!(is_leap_year(0));
        assert!(!is_leap_year(-1));
        assert!(!is_leap_year(-2));
        assert!(!is_leap_year(-3));
        assert!(is_leap_year(-4));
        assert!(!is_leap_year(-100));
        assert!(!is_leap_year(-200));
        assert!(!is_leap_year(-300));
        assert!(is_leap_year(400));
        assert!(!is_leap_year(9999));
        assert!(!is_leap_year(-9999));
    }

    #[test]
    fn t_days_in_month() {
        assert_eq!(28, days_in_month(-9999, 2));
    }

    // N.B. The other routines are generally covered by tests in
    // `src/civil/date.rs`. But adding tests here too probably makes sense.
}
