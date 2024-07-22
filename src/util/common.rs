/*!
A collection of datetime related utility functions.

# Constant functions

This module also contains some utilities for making some API items `const`.

One of the main reasons why more of this crate isn't `const` is because of
our ranged integer types. We very specifically use those types wherever we
do arithmetic as a mitigation for the absolute insance boundary conditions
that one must deal with in a datetime library. Unfortunately, these range
integer types are very difficult to make use of in `const` context. One of
the main blockers is the fact that Rust doesn't support `const` methods in
traits. That means we'd be unable to do `x + y` where `x` and `y` are range
integers. (Normal `x + y` arithmetic only works in `const` today because of
special support for Rust's standard integer types.)

With that said, it is sometimes useful to provide APIs that are const. For
example, `Date::new`. But we still need to do some checking on the inputs
to ensure they are valid. Since most of our arithmetic code is defined
using range integers, we have to re-write some it here using standard
primitive types.

In general, this code should not be used unless it is specifically required
to make something `const` AND if it is worth making it `const` in the first
place. Remember, much of this library _could_ be `const` if we were willing
to write `const`-compatible code, but I deemed it far too annoying to do
so.

# Algorithms

Algorithms are taken from
Neri C, Schneider L. "Euclidean affine functions and their application to calendar algorithms":
- https://github.com/cassioneri/eaf/
- https://www.youtube.com/watch?v=0s9F4QWAl-E
*/

use crate::util::t::{Day, Month, Year, C};

/// Returns true if and only if the given year is a leap year.
///
/// A leap year is a year with 366 days. Typical years have 365 days.
#[inline]
pub(crate) fn is_leap_year(year: Year) -> bool {
    let d = if year % C(25) != 0 { C(4) } else { C(16) };
    (year % d) == 0
}

/// Returns true if and only if the given year is a leap year.
///
/// A leap year is a year with 366 days. Typical years have 365 days.
///
/// This doesn't used range integers and is thus `const`.
#[inline]
pub(crate) const fn is_leap_year_unranged(year: i16) -> bool {
    let d = if year % 25 != 0 { 4 } else { 16 };
    (year % d) == 0
}

/// Saturates the given day in the month.
///
/// That is, if the day exceeds the maximum number of days in the given year
/// and month, then this returns the maximum. Otherwise, it returns the day
/// given.
#[inline]
pub(crate) fn saturate_day_in_month(
    year: Year,
    month: Month,
    day: Day,
) -> Day {
    day.min(days_in_month(year, month))
}

/// Returns the number of days in the given year and month.
///
/// This correctly returns `29` when the year is a leap year and the month is
/// February.
#[inline]
pub(crate) fn days_in_month(year: Year, month: Month) -> Day {
    if month == 2 {
        if is_leap_year(year) {
            Day::N::<29>()
        } else {
            Day::N::<28>()
        }
    } else {
        let month = month.get();
        if (month ^ month >> 3) & 1 == 0 {
            Day::N::<30>()
        } else {
            Day::N::<31>()
        }
    }
}

/// Return the number of days in the given month.
///
/// When the given month is invalid, this returns `0`.
#[inline]
pub(crate) const fn days_in_month_unranged(year: i16, month: i8) -> i8 {
    if !Month::contains(month) {
        return 0;
    }
    if month == 2 {
        if is_leap_year_unranged(year) {
            29
        } else {
            28
        }
    } else {
        30 | (month ^ month >> 3)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn t_is_leap_year() {
        let is_leap_year = |y: i16| is_leap_year(Year::new(y).unwrap());
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
        let days_in_month = |year: i16, month| {
            days_in_month(Year::new(year).unwrap(), Month::new(month).unwrap())
        };
        assert_eq!(28, days_in_month(-9999, 2).get());
    }
}
