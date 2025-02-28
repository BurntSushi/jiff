/*!
This module defines the internal core time data types.

This includes physical time (i.e., a timestamp) and civil time.

These types exist to provide a home for the core algorithms in a datetime
crate. For example, converting from a timestamp to a Gregorian calendar date
and clock time.

These routines are specifically implemented on simple primitive integer types
and implicitly assume that the inputs are valid (i.e., within Jiff's minimum
and maximum ranges).

These exist to provide `const` capabilities, and also to provide a small
reusable core of important algorithms that can be shared between `jiff` and
`jiff-static`.

# Naming

The types in this module are prefixed with letter `I` to make it clear that
they are internal types. Specifically, to distinguish them from Jiff's public
types. For example, `Date` versus `IDate`.
*/

// #![allow(warnings)]

#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub(crate) struct ITimestamp {
    pub(crate) second: i64,
    pub(crate) nanosecond: i32,
}

impl ITimestamp {
    /// Converts a Unix timestamp with an offset to a Gregorian datetime.
    ///
    /// The offset should correspond to the number of seconds required to
    /// add to this timestamp to get the local time.
    #[inline(always)]
    pub(crate) const fn to_datetime(&self, offset: IOffset) -> IDateTime {
        let ITimestamp { mut second, mut nanosecond } = *self;
        second += offset.second as i64;
        let mut epoch_day = second.div_euclid(86_400) as i32;
        second = second.rem_euclid(86_400);
        if nanosecond < 0 {
            if second > 0 {
                second -= 1;
                nanosecond += 1_000_000_000;
            } else {
                epoch_day -= 1;
                second += 86_399;
                nanosecond += 1_000_000_000;
            }
        }

        let date = IEpochDay { epoch_day }.to_date();
        let mut time = ITimeSecond { second: second as i32 }.to_time();
        time.subsec_nanosecond = nanosecond;
        IDateTime { date, time }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub(crate) struct IOffset {
    pub(crate) second: i32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub(crate) struct IDateTime {
    pub(crate) date: IDate,
    pub(crate) time: ITime,
}

impl IDateTime {
    /// Converts a Gregorian datetime and its offset to a Unix timestamp.
    ///
    /// The offset should correspond to the number of seconds required to
    /// subtract from this datetime in order to get to UTC.
    #[inline(always)]
    pub(crate) const fn to_timestamp(&self, offset: IOffset) -> ITimestamp {
        let epoch_day = self.date.to_epoch_day().epoch_day;
        let mut second = (epoch_day as i64) * 86_400
            + (self.time.to_second().second as i64);
        let mut nanosecond = self.time.subsec_nanosecond;
        second -= offset.second as i64;
        if epoch_day < 0 && nanosecond != 0 {
            second += 1;
            nanosecond -= 1_000_000_000;
        }
        ITimestamp { second, nanosecond }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub(crate) struct IEpochDay {
    pub(crate) epoch_day: i32,
}

impl IEpochDay {
    /// Converts days since the Unix epoch to a Gregorian date.
    ///
    /// This is Neri-Schneider. There's no branching or divisions.
    ///
    /// Ref: <https://github.com/cassioneri/eaf/blob/684d3cc32d14eee371d0abe4f683d6d6a49ed5c1/algorithms/neri_schneider.hpp#L40C3-L40C34>
    #[inline(always)]
    #[allow(non_upper_case_globals, non_snake_case)] // to mimic source
    pub(crate) const fn to_date(&self) -> IDate {
        const s: u32 = 82;
        const K: u32 = 719468 + 146097 * s;
        const L: u32 = 400 * s;

        let N_U = self.epoch_day as u32;
        let N = N_U.wrapping_add(K);

        let N_1 = 4 * N + 3;
        let C = N_1 / 146097;
        let N_C = (N_1 % 146097) / 4;

        let N_2 = 4 * N_C + 3;
        let P_2 = 2939745 * (N_2 as u64);
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
        IDate { year, month, day }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub(crate) struct IDate {
    pub(crate) year: i16,
    pub(crate) month: i8,
    pub(crate) day: i8,
}

impl IDate {
    /// Converts a Gregorian date to days since the Unix epoch.
    ///
    /// This is Neri-Schneider. There's no branching or divisions.
    ///
    /// Ref: https://github.com/cassioneri/eaf/blob/684d3cc32d14eee371d0abe4f683d6d6a49ed5c1/algorithms/neri_schneider.hpp#L83
    #[inline(always)]
    #[allow(non_upper_case_globals, non_snake_case)] // to mimic source
    pub(crate) const fn to_epoch_day(&self) -> IEpochDay {
        const s: u32 = 82;
        const K: u32 = 719468 + 146097 * s;
        const L: u32 = 400 * s;

        let year = self.year as u32;
        let month = self.month as u32;
        let day = self.day as u32;

        let J = month <= 2;
        let Y = year.wrapping_add(L).wrapping_sub(J as u32);
        let M = if J { month + 12 } else { month };
        let D = day - 1;
        let C = Y / 100;

        let y_star = 1461 * Y / 4 - C + C / 4;
        let m_star = (979 * M - 2919) / 32;
        let N = y_star + m_star + D;

        let N_U = N.wrapping_sub(K);
        let epoch_day = N_U as i32;
        IEpochDay { epoch_day }
    }
}

/// Represents a clock time.
///
/// This uses units of hours, minutes, seconds and fractional seconds (to
/// nanosecond precision).
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub(crate) struct ITime {
    pub(crate) hour: i8,
    pub(crate) minute: i8,
    pub(crate) second: i8,
    pub(crate) subsec_nanosecond: i32,
}

impl ITime {
    pub(crate) const ZERO: ITime =
        ITime { hour: 0, minute: 0, second: 0, subsec_nanosecond: 0 };

    #[inline(always)]
    pub(crate) const fn to_second(&self) -> ITimeSecond {
        let mut second: i32 = 0;
        second += (self.hour as i32) * 3600;
        second += (self.minute as i32) * 60;
        second += self.second as i32;
        ITimeSecond { second }
    }

    #[inline(always)]
    pub(crate) const fn to_nanosecond(&self) -> ITimeNanosecond {
        let mut nanosecond: i64 = 0;
        nanosecond += (self.hour as i64) * 3_600_000_000_000;
        nanosecond += (self.minute as i64) * 60_000_000_000;
        nanosecond += (self.second as i64) * 1_000_000_000;
        nanosecond += self.subsec_nanosecond as i64;
        ITimeNanosecond { nanosecond }
    }
}

/// Represents a single point in the day, to second precision.
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub(crate) struct ITimeSecond {
    pub(crate) second: i32,
}

impl ITimeSecond {
    #[inline(always)]
    pub(crate) const fn to_time(&self) -> ITime {
        let mut second = self.second;
        let mut time = ITime::ZERO;
        if second != 0 {
            time.hour = (second / 3600) as i8;
            second %= 3600;
            if second != 0 {
                time.minute = (second / 60) as i8;
                time.second = (second % 60) as i8;
            }
        }
        time
    }
}

/// Represents a single point in the day, to nanosecond precision.
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub(crate) struct ITimeNanosecond {
    pub(crate) nanosecond: i64,
}

impl ITimeNanosecond {
    #[inline(always)]
    pub(crate) const fn to_time(&self) -> ITime {
        let mut nanosecond = self.nanosecond;
        let mut time = ITime::ZERO;
        if nanosecond != 0 {
            time.hour = (nanosecond / 3_600_000_000_000) as i8;
            nanosecond %= 3_600_000_000_000;
            if nanosecond != 0 {
                time.minute = (nanosecond / 60_000_000_000) as i8;
                nanosecond %= 60_000_000_000;
                if nanosecond != 0 {
                    time.second = (nanosecond / 1_000_000_000) as i8;
                    time.subsec_nanosecond =
                        (nanosecond % 1_000_000_000) as i32;
                }
            }
        }
        time
    }
}

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip_epochday_date() {
        for year in -9999..=9999 {
            for month in 1..=12 {
                for day in 1..=days_in_month(year, month) {
                    let date = IDate { year, month, day };
                    let epoch_day = date.to_epoch_day();
                    let date_roundtrip = epoch_day.to_date();
                    assert_eq!(date, date_roundtrip);
                }
            }
        }
    }

    #[test]
    fn roundtrip_second_time() {
        for second in 0..=86_399 {
            let second = ITimeSecond { second };
            let time = second.to_time();
            let second_roundtrip = time.to_second();
            assert_eq!(second, second_roundtrip);
        }
    }

    #[test]
    fn roundtrip_nanosecond_time() {
        for second in 0..=86_399 {
            for nanosecond in
                [0, 250_000_000, 500_000_000, 750_000_000, 900_000_000]
            {
                let nanosecond = ITimeNanosecond {
                    nanosecond: (second * 1_000_000_000 + nanosecond),
                };
                let time = nanosecond.to_time();
                let nanosecond_roundtrip = time.to_nanosecond();
                assert_eq!(nanosecond, nanosecond_roundtrip);
            }
        }
    }

    #[test]
    fn leap_year() {
        assert!(!is_leap_year(1900));
        assert!(is_leap_year(2000));
        assert!(!is_leap_year(2001));
        assert!(!is_leap_year(2002));
        assert!(!is_leap_year(2003));
        assert!(is_leap_year(2004));
    }

    #[test]
    fn number_of_days_in_month() {
        assert_eq!(days_in_month(2024, 1), 31);
        assert_eq!(days_in_month(2024, 2), 29);
        assert_eq!(days_in_month(2024, 3), 31);
        assert_eq!(days_in_month(2024, 4), 30);
        assert_eq!(days_in_month(2024, 5), 31);
        assert_eq!(days_in_month(2024, 6), 30);
        assert_eq!(days_in_month(2024, 7), 31);
        assert_eq!(days_in_month(2024, 8), 31);
        assert_eq!(days_in_month(2024, 9), 30);
        assert_eq!(days_in_month(2024, 10), 31);
        assert_eq!(days_in_month(2024, 11), 30);
        assert_eq!(days_in_month(2024, 12), 31);

        assert_eq!(days_in_month(2025, 1), 31);
        assert_eq!(days_in_month(2025, 2), 28);
        assert_eq!(days_in_month(2025, 3), 31);
        assert_eq!(days_in_month(2025, 4), 30);
        assert_eq!(days_in_month(2025, 5), 31);
        assert_eq!(days_in_month(2025, 6), 30);
        assert_eq!(days_in_month(2025, 7), 31);
        assert_eq!(days_in_month(2025, 8), 31);
        assert_eq!(days_in_month(2025, 9), 30);
        assert_eq!(days_in_month(2025, 10), 31);
        assert_eq!(days_in_month(2025, 11), 30);
        assert_eq!(days_in_month(2025, 12), 31);

        assert_eq!(days_in_month(1900, 2), 28);
        assert_eq!(days_in_month(2000, 2), 29);
    }
}
