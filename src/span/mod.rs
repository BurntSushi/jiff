use core::cmp::Ordering;

use alloc::borrow::Cow;

use crate::{
    civil,
    error::{err, Error},
    instant::Instant,
    round::{
        clamp_relative_span, RelativeCow, RelativeRange, RelativeTo, Round,
        Unit,
    },
    util::{
        rangeint::{ri64, ri8, RFrom, RInto, TryRFrom, TryRInto},
        t::{self, NoUnits, NoUnits128, Sign, C},
    },
};

pub(crate) use self::duration::TimeDuration;

mod duration;

// TODO: The Eq impl will need to be more sophisticated. It should return
// equal for any two durations that correspond to the same amount of time,
// regardless of units.
//
// Really though? That seems perhaps surprisingly expensive, to the point
// where we might want to put that in its own distinct method...

#[derive(Clone, Copy, Eq, PartialEq)]
pub struct Span {
    pub(crate) sign: Sign,
    pub(crate) years: t::SpanYears,
    pub(crate) months: t::SpanMonths,
    pub(crate) weeks: t::SpanWeeks,
    pub(crate) days: t::SpanDays,
    pub(crate) hours: t::SpanHours,
    pub(crate) minutes: t::SpanMinutes,
    pub(crate) seconds: t::SpanSeconds,
    pub(crate) milliseconds: t::SpanMilliseconds,
    pub(crate) microseconds: t::SpanMicroseconds,
    pub(crate) nanoseconds: t::SpanNanoseconds,
}

/// Infallible routines for setting units on a `Span`.
///
/// These are useful when the units are determined by the programmer or when
/// they have been validated elsewhere. In general, use these routines when
/// constructing an invalid `Span` should be considered a bug in the program.
impl Span {
    pub fn new() -> Span {
        Span::default()
    }

    pub fn years<I: Into<i64>>(self, years: I) -> Span {
        self.try_years(years).expect("value for years is out of bounds")
    }

    pub fn months<I: Into<i64>>(self, months: I) -> Span {
        self.try_months(months).expect("value for months is out of bounds")
    }

    pub fn weeks<I: Into<i64>>(self, weeks: I) -> Span {
        self.try_weeks(weeks).expect("value for weeks is out of bounds")
    }

    pub fn days<I: Into<i64>>(self, days: I) -> Span {
        self.try_days(days).expect("value for days is out of bounds")
    }

    pub fn hours<I: Into<i64>>(self, hours: I) -> Span {
        self.try_hours(hours).expect("value for hours is out of bounds")
    }

    pub fn minutes<I: Into<i64>>(self, minutes: I) -> Span {
        self.try_minutes(minutes).expect("value for minutes is out of bounds")
    }

    pub fn seconds<I: Into<i64>>(self, seconds: I) -> Span {
        self.try_seconds(seconds).expect("value for seconds is out of bounds")
    }

    pub fn milliseconds<I: Into<i64>>(self, milliseconds: I) -> Span {
        self.try_milliseconds(milliseconds)
            .expect("value for milliseconds is out of bounds")
    }

    pub fn microseconds<I: Into<i64>>(self, microseconds: I) -> Span {
        self.try_microseconds(microseconds)
            .expect("value for microseconds is out of bounds")
    }

    pub fn nanoseconds<I: Into<i64>>(self, nanoseconds: I) -> Span {
        self.try_nanoseconds(nanoseconds)
            .expect("value for nanoseconds is out of bounds")
    }

    pub fn round(self, options: impl Into<Round>) -> Span {
        self.try_round(options).expect("rounding failed")
    }
}

/// Fallible methods for setting units on a `Span`.
///
/// These methods are useful when the span is made up of user provided values
/// that may not be in range.
impl Span {
    pub fn try_years<I: Into<i64>>(self, years: I) -> Result<Span, Error> {
        type Range = ri64<{ t::SpanYears::MIN }, { t::SpanYears::MAX }>;
        let years = Range::try_new("years", years)?;
        Ok(self.years_ranged(years))
    }

    pub fn try_months<I: Into<i64>>(self, months: I) -> Result<Span, Error> {
        type Range = ri64<{ t::SpanMonths::MIN }, { t::SpanMonths::MAX }>;
        let months = Range::try_new("months", months)?;
        Ok(self.months_ranged(months))
    }

    pub fn try_weeks<I: Into<i64>>(self, weeks: I) -> Result<Span, Error> {
        type Range = ri64<{ t::SpanWeeks::MIN }, { t::SpanWeeks::MAX }>;
        let weeks = Range::try_new("weeks", weeks)?;
        Ok(self.weeks_ranged(weeks))
    }

    pub fn try_days<I: Into<i64>>(self, days: I) -> Result<Span, Error> {
        type Range = ri64<{ t::SpanDays::MIN }, { t::SpanDays::MAX }>;
        let days = Range::try_new("days", days)?;
        Ok(self.days_ranged(days))
    }

    pub fn try_hours<I: Into<i64>>(self, hours: I) -> Result<Span, Error> {
        type Range = ri64<{ t::SpanHours::MIN }, { t::SpanHours::MAX }>;
        let hours = Range::try_new("hours", hours)?;
        Ok(self.hours_ranged(hours))
    }

    pub fn try_minutes<I: Into<i64>>(self, minutes: I) -> Result<Span, Error> {
        type Range = ri64<{ t::SpanMinutes::MIN }, { t::SpanMinutes::MAX }>;
        let minutes = Range::try_new("minutes", minutes.into())?;
        Ok(self.minutes_ranged(minutes))
    }

    pub fn try_seconds<I: Into<i64>>(self, seconds: I) -> Result<Span, Error> {
        type Range = ri64<{ t::SpanSeconds::MIN }, { t::SpanSeconds::MAX }>;
        let seconds = Range::try_new("seconds", seconds.into())?;
        Ok(self.seconds_ranged(seconds))
    }

    pub fn try_milliseconds<I: Into<i64>>(
        self,
        milliseconds: I,
    ) -> Result<Span, Error> {
        type Range =
            ri64<{ t::SpanMilliseconds::MIN }, { t::SpanMilliseconds::MAX }>;
        let milliseconds =
            Range::try_new("milliseconds", milliseconds.into())?;
        Ok(self.milliseconds_ranged(milliseconds))
    }

    pub fn try_microseconds<I: Into<i64>>(
        self,
        microseconds: I,
    ) -> Result<Span, Error> {
        type Range =
            ri64<{ t::SpanMicroseconds::MIN }, { t::SpanMicroseconds::MAX }>;
        let microseconds =
            Range::try_new("microseconds", microseconds.into())?;
        Ok(self.microseconds_ranged(microseconds))
    }

    pub fn try_nanoseconds<I: Into<i64>>(
        self,
        nanoseconds: I,
    ) -> Result<Span, Error> {
        type Range =
            ri64<{ t::SpanNanoseconds::MIN }, { t::SpanNanoseconds::MAX }>;
        let nanoseconds = Range::try_new("nanoseconds", nanoseconds.into())?;
        Ok(self.nanoseconds_ranged(nanoseconds))
    }

    pub fn try_round(self, options: impl Into<Round>) -> Result<Span, Error> {
        options.into().round_span(&self)
    }

    pub fn checked_add(
        self,
        relative: Option<RelativeTo>,
        span: Span,
    ) -> Result<Span, Error> {
        let unit = self.largest_unit().max(span.largest_unit());
        let start = match relative {
            Some(r) => {
                if !r.is_variable(unit) {
                    return checked_add_invariant(unit, &self, &span);
                }
                r
            }
            None => {
                if unit.is_definitively_variable() {
                    return Err(err!(
                        "using largest unit (which is '{unit}') in given span \
                         requires that a relative reference time be given, \
                         but none was provided",
                        unit = unit.singular(),
                    ));
                }
                return checked_add_invariant(unit, &self, &span);
            }
        };
        let mid = start.checked_add(self)?;
        let end = mid.checked_add(span)?;
        start.until_with_largest_unit(unit, &end)
    }

    pub fn checked_sub(
        self,
        relative: Option<RelativeTo>,
        span: Span,
    ) -> Result<Span, Error> {
        self.checked_add(relative, -span)
    }

    pub fn compare(
        &self,
        relative: Option<RelativeTo>,
        span: &Span,
    ) -> Result<Ordering, Error> {
        let unit = self.largest_unit().max(span.largest_unit());
        let start = match relative {
            Some(r) => {
                if !r.is_variable(unit) {
                    let nanos1 = self.to_invariant_nanoseconds();
                    let nanos2 = span.to_invariant_nanoseconds();
                    return Ok(nanos1.cmp(&nanos2));
                }
                r
            }
            None => {
                if unit.is_definitively_variable() {
                    return Err(err!(
                        "using largest unit (which is '{unit}') in given span \
                         requires that a relative reference time be given, \
                         but none was provided",
                        unit = unit.singular(),
                    ));
                }
                let nanos1 = self.to_invariant_nanoseconds();
                let nanos2 = span.to_invariant_nanoseconds();
                return Ok(nanos1.cmp(&nanos2));
            }
        };
        let end1 = start.checked_add(*self)?.to_nanosecond()?;
        let end2 = start.checked_add(*span)?.to_nanosecond()?;
        Ok(end1.cmp(&end2))
    }

    pub fn total(
        &self,
        unit: Unit,
        relative: Option<RelativeTo>,
    ) -> Result<f64, Error> {
        let max_unit = unit.max(self.largest_unit());
        let relative = match relative {
            Some(r) => {
                if !r.is_variable(max_unit) {
                    return Ok(total_invariant(unit, self));
                }
                r.to_balanced_span(unit, *self)?
            }
            None => {
                if max_unit.is_definitively_variable() {
                    return Err(err!(
                        "using unit '{unit}' requires that a relative \
                         reference time be given, but none was provided",
                        unit = max_unit.singular(),
                    ));
                }
                return Ok(total_invariant(unit, self));
            }
        };
        if !relative.range.is_variable(unit) {
            return Ok(total_invariant(unit, &relative.span));
        }

        assert!(unit >= Unit::Day);
        let sign = relative.span.get_sign_ranged();
        let (relative_start, relative_end) = match relative.range {
            RelativeRange::Civil { ref start, ref end } => {
                let start = RelativeCow::Civil(Cow::Borrowed(start));
                let end = RelativeCow::Civil(Cow::Borrowed(end));
                (start, end)
            }
            RelativeRange::Zoned { ref start, ref end } => {
                let start = RelativeCow::Zoned(Cow::Borrowed(start));
                let end = RelativeCow::Zoned(Cow::Borrowed(end));
                (start, end)
            }
        };
        let (relative0, relative1) = clamp_relative_span(
            &relative.span.without_lower(unit),
            &relative_start,
            unit,
            sign.rinto(),
        )?;
        let denom = (relative1 - relative0).get() as f64;
        let numer = (relative_end.to_nanosecond() - relative0).get() as f64;
        let unit_val = relative.span.get_units_ranged(unit).get() as f64;
        Ok(unit_val + (numer / denom) * (sign.get() as f64))
    }
}

fn checked_add_invariant(
    unit: Unit,
    span1: &Span,
    span2: &Span,
) -> Result<Span, Error> {
    assert!(unit <= Unit::Day);
    let nanos1 = span1.to_invariant_nanoseconds();
    let nanos2 = span2.to_invariant_nanoseconds();
    let sum = nanos1 + nanos2;
    Span::from_invariant_nanoseconds(unit, sum)
}

fn total_invariant(unit: Unit, span: &Span) -> f64 {
    assert!(unit <= Unit::Day);
    let nanos = span.to_invariant_nanoseconds();
    (nanos.get() as f64) / (unit.nanoseconds().get() as f64)
}

/// Routines for accessing the individual units in a `Span`.
impl Span {
    pub fn get_years(&self) -> i16 {
        self.get_years_ranged().get()
    }

    pub fn get_months(&self) -> i32 {
        self.get_months_ranged().get()
    }

    pub fn get_weeks(&self) -> i32 {
        self.get_weeks_ranged().get()
    }

    pub fn get_days(&self) -> i32 {
        self.get_days_ranged().get()
    }

    pub fn get_hours(&self) -> i32 {
        self.get_hours_ranged().get()
    }

    pub fn get_minutes(&self) -> i64 {
        self.get_minutes_ranged().get()
    }

    pub fn get_seconds(&self) -> i64 {
        self.get_seconds_ranged().get()
    }

    pub fn get_milliseconds(&self) -> i64 {
        self.get_milliseconds_ranged().get()
    }

    pub fn get_microseconds(&self) -> i64 {
        self.get_microseconds_ranged().get()
    }

    pub fn get_nanoseconds(&self) -> i64 {
        self.get_nanoseconds_ranged().get()
    }
}

/// Routines for manipulating `Span` values.
impl Span {
    pub fn abs(self) -> Span {
        Span { sign: ri8::N::<1>(), ..self }
    }

    pub fn negate(self) -> Span {
        Span { sign: -self.sign, ..self }
    }

    pub fn is_negative(self) -> bool {
        self.get_sign_ranged() < 0
    }

    pub fn is_zero(self) -> bool {
        self.years == 0
            && self.months == 0
            && self.weeks == 0
            && self.days == 0
            && self.hours == 0
            && self.minutes == 0
            && self.seconds == 0
            && self.milliseconds == 0
            && self.microseconds == 0
            && self.nanoseconds == 0
    }

    pub fn checked_mul(mut self, rhs: i64) -> Result<Span, Error> {
        if rhs == 0 {
            return Ok(Span::default());
        } else if rhs == 1 {
            return Ok(self);
        }
        self.sign *= t::Sign::try_new("span factor", rhs.signum())
            .expect("signum fits in ri8");
        // This is all somewhat odd, but since each of our span fields uses
        // a different primitive representation and range of allowed values,
        // we only seek to perform multiplications when they will actually
        // do something. Otherwise, we risk multiplying the mins/maxs of a
        // ranged integer and causing a spurious panic. Basically, the idea
        // here is the allowable values for our multiple depend on what we're
        // actually going to multiply with it. If our span has non-zero years,
        // then our multiple can't exceed the bounds of `SpanYears`, otherwise
        // it is guaranteed to overflow.
        if self.years != 0 {
            let rhs = t::SpanYears::try_new("years multiple", rhs)?;
            self.years = self.years.try_checked_mul("years", rhs)?;
        }
        if self.months != 0 {
            let rhs = t::SpanMonths::try_new("months multiple", rhs)?;
            self.months = self.months.try_checked_mul("months", rhs)?;
        }
        if self.weeks != 0 {
            let rhs = t::SpanWeeks::try_new("weeks multiple", rhs)?;
            self.weeks = self.weeks.try_checked_mul("weeks", rhs)?;
        }
        if self.days != 0 {
            let rhs = t::SpanDays::try_new("days multiple", rhs)?;
            self.days = self.days.try_checked_mul("days", rhs)?;
        }
        if self.hours != 0 {
            let rhs = t::SpanHours::try_new("hours multiple", rhs)?;
            self.hours = self.hours.try_checked_mul("hours", rhs)?;
        }
        if self.minutes != 0 {
            let rhs = t::SpanMinutes::try_new("minutes multiple", rhs)?;
            self.minutes = self.minutes.try_checked_mul("minutes", rhs)?;
        }
        if self.seconds != 0 {
            let rhs = t::SpanSeconds::try_new("seconds multiple", rhs)?;
            self.seconds = self.seconds.try_checked_mul("seconds", rhs)?;
        }
        if self.milliseconds != 0 {
            let rhs =
                t::SpanMilliseconds::try_new("milliseconds multiple", rhs)?;
            self.milliseconds =
                self.milliseconds.try_checked_mul("milliseconds", rhs)?;
        }
        if self.microseconds != 0 {
            let rhs =
                t::SpanMicroseconds::try_new("microseconds multiple", rhs)?;
            self.microseconds =
                self.microseconds.try_checked_mul("microseconds", rhs)?;
        }
        if self.nanoseconds != 0 {
            let rhs =
                t::SpanNanoseconds::try_new("nanoseconds multiple", rhs)?;
            self.nanoseconds =
                self.nanoseconds.try_checked_mul("nanoseconds", rhs)?;
        }
        Ok(self)
    }
}

/// Crate internal APIs that operate on ranged integer types.
impl Span {
    pub(crate) fn years_ranged(self, years: impl RInto<t::SpanYears>) -> Span {
        let years = years.rinto();
        let mut span = Span { years: years.abs(), ..self };
        span.sign = self.resign(years, &span);
        span
    }

    pub(crate) fn months_ranged(
        self,
        months: impl RInto<t::SpanMonths>,
    ) -> Span {
        let months = months.rinto();
        let mut span = Span { months: months.abs(), ..self };
        span.sign = self.resign(months, &span);
        span
    }

    pub(crate) fn weeks_ranged(self, weeks: impl RInto<t::SpanWeeks>) -> Span {
        let weeks = weeks.rinto();
        let mut span = Span { weeks: weeks.abs(), ..self };
        span.sign = self.resign(weeks, &span);
        span
    }

    pub(crate) fn days_ranged(self, days: impl RInto<t::SpanDays>) -> Span {
        let days = days.rinto();
        let mut span = Span { days: days.abs(), ..self };
        span.sign = self.resign(days, &span);
        span
    }

    pub(crate) fn hours_ranged(self, hours: impl RInto<t::SpanHours>) -> Span {
        let hours = hours.rinto();
        let mut span = Span { hours: hours.abs(), ..self };
        span.sign = self.resign(hours, &span);
        span
    }

    pub(crate) fn minutes_ranged(
        self,
        minutes: impl RInto<t::SpanMinutes>,
    ) -> Span {
        let minutes = minutes.rinto();
        let mut span = Span { minutes: minutes.abs(), ..self };
        span.sign = self.resign(minutes, &span);
        span
    }

    pub(crate) fn seconds_ranged(
        self,
        seconds: impl RInto<t::SpanSeconds>,
    ) -> Span {
        let seconds = seconds.rinto();
        let mut span = Span { seconds: seconds.abs(), ..self };
        span.sign = self.resign(seconds, &span);
        span
    }

    pub(crate) fn milliseconds_ranged(
        self,
        milliseconds: impl RInto<t::SpanMilliseconds>,
    ) -> Span {
        let milliseconds = milliseconds.rinto();
        let mut span = Span { milliseconds: milliseconds.abs(), ..self };
        span.sign = self.resign(milliseconds, &span);
        span
    }

    pub(crate) fn microseconds_ranged(
        self,
        microseconds: impl RInto<t::SpanMicroseconds>,
    ) -> Span {
        let microseconds = microseconds.rinto();
        let mut span = Span { microseconds: microseconds.abs(), ..self };
        span.sign = self.resign(microseconds, &span);
        span
    }

    pub(crate) fn nanoseconds_ranged(
        self,
        nanoseconds: impl RInto<t::SpanNanoseconds>,
    ) -> Span {
        let nanoseconds = nanoseconds.rinto();
        let mut span = Span { nanoseconds: nanoseconds.abs(), ..self };
        span.sign = self.resign(nanoseconds, &span);
        span
    }

    pub(crate) fn try_years_ranged(
        self,
        years: impl TryRInto<t::SpanYears>,
    ) -> Result<Span, Error> {
        let years = years.try_rinto("years")?;
        Ok(self.years_ranged(years))
    }

    pub(crate) fn try_months_ranged(
        self,
        months: impl TryRInto<t::SpanMonths>,
    ) -> Result<Span, Error> {
        let months = months.try_rinto("months")?;
        Ok(self.months_ranged(months))
    }

    pub(crate) fn try_weeks_ranged(
        self,
        weeks: impl TryRInto<t::SpanWeeks>,
    ) -> Result<Span, Error> {
        let weeks = weeks.try_rinto("weeks")?;
        Ok(self.weeks_ranged(weeks))
    }

    pub(crate) fn try_days_ranged(
        self,
        days: impl TryRInto<t::SpanDays>,
    ) -> Result<Span, Error> {
        let days = days.try_rinto("days")?;
        Ok(self.days_ranged(days))
    }

    pub(crate) fn try_hours_ranged(
        self,
        hours: impl TryRInto<t::SpanHours>,
    ) -> Result<Span, Error> {
        let hours = hours.try_rinto("hours")?;
        Ok(self.hours_ranged(hours))
    }

    pub(crate) fn try_minutes_ranged(
        self,
        minutes: impl TryRInto<t::SpanMinutes>,
    ) -> Result<Span, Error> {
        let minutes = minutes.try_rinto("minutes")?;
        Ok(self.minutes_ranged(minutes))
    }

    pub(crate) fn try_seconds_ranged(
        self,
        seconds: impl TryRInto<t::SpanSeconds>,
    ) -> Result<Span, Error> {
        let seconds = seconds.try_rinto("seconds")?;
        Ok(self.seconds_ranged(seconds))
    }

    pub(crate) fn try_milliseconds_ranged(
        self,
        milliseconds: impl TryRInto<t::SpanMilliseconds>,
    ) -> Result<Span, Error> {
        let milliseconds = milliseconds.try_rinto("milliseconds")?;
        Ok(self.milliseconds_ranged(milliseconds))
    }

    pub(crate) fn try_microseconds_ranged(
        self,
        microseconds: impl TryRInto<t::SpanMicroseconds>,
    ) -> Result<Span, Error> {
        let microseconds = microseconds.try_rinto("microseconds")?;
        Ok(self.microseconds_ranged(microseconds))
    }

    pub(crate) fn try_nanoseconds_ranged(
        self,
        nanoseconds: impl TryRInto<t::SpanNanoseconds>,
    ) -> Result<Span, Error> {
        let nanoseconds = nanoseconds.try_rinto("nanoseconds")?;
        Ok(self.nanoseconds_ranged(nanoseconds))
    }

    pub(crate) fn try_units_ranged(
        self,
        unit: Unit,
        value: impl RInto<NoUnits>,
    ) -> Result<Span, Error> {
        let value = value.rinto();
        match unit {
            Unit::Year => self.try_years_ranged(value),
            Unit::Month => self.try_months_ranged(value),
            Unit::Week => self.try_weeks_ranged(value),
            Unit::Day => self.try_days_ranged(value),
            Unit::Hour => self.try_hours_ranged(value),
            Unit::Minute => self.try_minutes_ranged(value),
            Unit::Second => self.try_seconds_ranged(value),
            Unit::Millisecond => self.try_milliseconds_ranged(value),
            Unit::Microsecond => self.try_microseconds_ranged(value),
            Unit::Nanosecond => self.try_nanoseconds_ranged(value),
        }
    }

    pub(crate) fn get_years_ranged(&self) -> t::SpanYears {
        self.years * self.sign
    }

    pub(crate) fn get_months_ranged(&self) -> t::SpanMonths {
        self.months * self.sign
    }

    pub(crate) fn get_weeks_ranged(&self) -> t::SpanWeeks {
        self.weeks * self.sign
    }

    pub(crate) fn get_days_ranged(&self) -> t::SpanDays {
        self.days * self.sign
    }

    pub(crate) fn get_hours_ranged(&self) -> t::SpanHours {
        self.hours * self.sign
    }

    pub(crate) fn get_minutes_ranged(&self) -> t::SpanMinutes {
        self.minutes * self.sign
    }

    pub(crate) fn get_seconds_ranged(&self) -> t::SpanSeconds {
        self.seconds * self.sign
    }

    pub(crate) fn get_milliseconds_ranged(&self) -> t::SpanMilliseconds {
        self.milliseconds * self.sign
    }

    pub(crate) fn get_microseconds_ranged(&self) -> t::SpanMicroseconds {
        self.microseconds * self.sign
    }

    pub(crate) fn get_nanoseconds_ranged(&self) -> t::SpanNanoseconds {
        self.nanoseconds * self.sign
    }

    pub(crate) fn get_sign_ranged(&self) -> ri8<-1, 1> {
        self.sign
    }

    pub(crate) fn get_units_ranged(&self, unit: Unit) -> NoUnits {
        match unit {
            Unit::Year => self.get_years_ranged().rinto(),
            Unit::Month => self.get_months_ranged().rinto(),
            Unit::Week => self.get_weeks_ranged().rinto(),
            Unit::Day => self.get_days_ranged().rinto(),
            Unit::Hour => self.get_hours_ranged().rinto(),
            Unit::Minute => self.get_minutes_ranged().rinto(),
            Unit::Second => self.get_seconds_ranged().rinto(),
            Unit::Millisecond => self.get_milliseconds_ranged().rinto(),
            Unit::Microsecond => self.get_microseconds_ranged().rinto(),
            Unit::Nanosecond => self.get_nanoseconds_ranged().rinto(),
        }
    }
}

/// Crate internal helper routines.
impl Span {
    pub(crate) fn load_civil_datetime(&mut self, datetime: civil::DateTime) {
        self.load_civil_date(datetime.date());
        self.load_civil_time(datetime.time());
    }

    pub(crate) fn load_civil_date(&mut self, date: civil::Date) {
        *self = self
            .years_ranged(date.year_ranged())
            .months_ranged(date.month_ranged())
            .days_ranged(date.day_ranged());
    }

    pub(crate) fn load_civil_time(&mut self, time: civil::Time) {
        let (milli, micro, nano) = time.to_subsec_parts_ranged();
        *self = self
            .hours_ranged(time.hour_ranged())
            .minutes_ranged(time.minute_ranged())
            .seconds_ranged(time.utc_second_ranged())
            .milliseconds_ranged(milli)
            .microseconds_ranged(micro)
            .nanoseconds_ranged(nano);
    }

    pub(crate) fn to_civil_datetime(&self) -> civil::DateTime {
        civil::DateTime::from_parts(self.to_civil_date(), self.to_civil_time())
    }

    pub(crate) fn to_civil_date(&self) -> civil::Date {
        civil::Date::new_ranged(
            self.get_years_ranged(),
            self.get_months_ranged().abs(),
            self.get_days_ranged().abs(),
        )
        .expect("valid date from span")
    }

    pub(crate) fn to_civil_time(&self) -> civil::Time {
        civil::Time::new_ranged(
            self.get_hours_ranged().abs(),
            self.get_minutes_ranged().abs(),
            self.get_seconds_ranged().abs(),
        )
        .with_subsec_parts_ranged(
            self.get_milliseconds_ranged().abs(),
            self.get_microseconds_ranged().abs(),
            self.get_nanoseconds_ranged().abs(),
        )
    }

    /// Converts the given number of nanoseconds to a `Span` whose units do not
    /// exceed `largest`.
    ///
    /// Note that `largest` is capped at `Unit::Day`. That is, if any unit
    /// greater than `Unit::Day` is given, then it is treated as `Unit::Day`.
    /// And also note that days in this context are civil days. That is, they
    /// are always 24 hours long. Callers needing to deal with variable length
    /// days should do so outside of this routine and should not provide a
    /// `largest` unit bigger than `Unit::Hour`.
    pub(crate) fn from_invariant_nanoseconds(
        largest: Unit,
        nanos: impl RInto<NoUnits128>,
    ) -> Result<Span, Error> {
        let nanos = nanos.rinto();
        let mut span = Span::new();
        match largest {
            Unit::Year | Unit::Month | Unit::Week | Unit::Day => {
                let micros = nanos.div_ceil(t::NANOS_PER_MICRO);
                span = span.try_nanoseconds_ranged(
                    nanos.rem_ceil(t::NANOS_PER_MICRO),
                )?;
                let millis = micros.div_ceil(t::MICROS_PER_MILLI);
                span = span.try_microseconds_ranged(
                    micros.rem_ceil(t::MICROS_PER_MILLI),
                )?;
                let secs = millis.div_ceil(t::MILLIS_PER_SECOND);
                span = span.try_milliseconds_ranged(
                    millis.rem_ceil(t::MILLIS_PER_SECOND),
                )?;
                let mins = secs.div_ceil(t::SECONDS_PER_MINUTE);
                span = span.try_seconds_ranged(
                    secs.rem_ceil(t::SECONDS_PER_MINUTE),
                )?;
                let hours = mins.div_ceil(t::MINUTES_PER_HOUR);
                span = span
                    .try_minutes_ranged(mins.rem_ceil(t::MINUTES_PER_HOUR))?;
                let days = hours.div_ceil(t::HOURS_PER_CIVIL_DAY);
                span = span.try_hours_ranged(
                    hours.rem_ceil(t::HOURS_PER_CIVIL_DAY),
                )?;
                span = span.try_days_ranged(days)?;
                Ok(span)
            }
            Unit::Hour => {
                let micros = nanos.div_ceil(t::NANOS_PER_MICRO);
                span = span.try_nanoseconds_ranged(
                    nanos.rem_ceil(t::NANOS_PER_MICRO),
                )?;
                let millis = micros.div_ceil(t::MICROS_PER_MILLI);
                span = span.try_microseconds_ranged(
                    micros.rem_ceil(t::MICROS_PER_MILLI),
                )?;
                let secs = millis.div_ceil(t::MILLIS_PER_SECOND);
                span = span.try_milliseconds_ranged(
                    millis.rem_ceil(t::MILLIS_PER_SECOND),
                )?;
                let mins = secs.div_ceil(t::SECONDS_PER_MINUTE);
                span = span.try_seconds_ranged(
                    secs.rem_ceil(t::SECONDS_PER_MINUTE),
                )?;
                let hours = mins.div_ceil(t::MINUTES_PER_HOUR);
                span = span
                    .try_minutes_ranged(mins.rem_ceil(t::MINUTES_PER_HOUR))?;
                span = span.try_hours_ranged(hours)?;
                Ok(span)
            }
            Unit::Minute => {
                let micros = nanos.div_ceil(t::NANOS_PER_MICRO);
                span = span.try_nanoseconds_ranged(
                    nanos.rem_ceil(t::NANOS_PER_MICRO),
                )?;
                let millis = micros.div_ceil(t::MICROS_PER_MILLI);
                span = span.try_microseconds_ranged(
                    micros.rem_ceil(t::MICROS_PER_MILLI),
                )?;
                let secs = millis.div_ceil(t::MILLIS_PER_SECOND);
                span = span.try_milliseconds_ranged(
                    millis.rem_ceil(t::MILLIS_PER_SECOND),
                )?;
                let mins = secs.div_ceil(t::SECONDS_PER_MINUTE);
                span =
                    span.try_seconds(secs.rem_ceil(t::SECONDS_PER_MINUTE))?;
                span = span.try_minutes_ranged(mins)?;
                Ok(span)
            }
            Unit::Second => {
                let micros = nanos.div_ceil(t::NANOS_PER_MICRO);
                span = span.try_nanoseconds_ranged(
                    nanos.rem_ceil(t::NANOS_PER_MICRO),
                )?;
                let millis = micros.div_ceil(t::MICROS_PER_MILLI);
                span = span.try_microseconds_ranged(
                    micros.rem_ceil(t::MICROS_PER_MILLI),
                )?;
                let secs = millis.div_ceil(t::MILLIS_PER_SECOND);
                span = span.try_milliseconds_ranged(
                    millis.rem_ceil(t::MILLIS_PER_SECOND),
                )?;
                span = span.try_seconds_ranged(secs)?;
                Ok(span)
            }
            Unit::Millisecond => {
                let micros = nanos.div_ceil(t::NANOS_PER_MICRO);
                span = span.try_nanoseconds_ranged(
                    nanos.rem_ceil(t::NANOS_PER_MICRO),
                )?;
                let millis = micros.div_ceil(t::MICROS_PER_MILLI);
                span = span.try_microseconds_ranged(
                    micros.rem_ceil(t::MICROS_PER_MILLI),
                )?;
                span = span.try_milliseconds_ranged(millis)?;
                Ok(span)
            }
            Unit::Microsecond => {
                let micros = nanos.div_ceil(t::NANOS_PER_MICRO);
                span = span.try_nanoseconds_ranged(
                    nanos.rem_ceil(t::NANOS_PER_MICRO),
                )?;
                span = span.try_microseconds_ranged(micros)?;
                Ok(span)
            }
            Unit::Nanosecond => {
                span = span.try_nanoseconds_ranged(nanos)?;
                Ok(span)
            }
        }
    }

    /// Converts the non-variable units of this `Span` to a total number of
    /// nanoseconds.
    ///
    /// This includes days, even though they can be of irregular length during
    /// time zone transitions. If this applies, then callers should set the
    /// days to `0` before calling this routine.
    ///
    /// All units above days are always ignored.
    pub(crate) fn to_invariant_nanoseconds(&self) -> NoUnits128 {
        let mut nanos = NoUnits128::rfrom(self.get_nanoseconds_ranged());
        nanos += NoUnits128::rfrom(self.get_microseconds_ranged())
            * t::NANOS_PER_MICRO;
        nanos += NoUnits128::rfrom(self.get_milliseconds_ranged())
            * t::NANOS_PER_MILLI;
        nanos +=
            NoUnits128::rfrom(self.get_seconds_ranged()) * t::NANOS_PER_SECOND;
        nanos +=
            NoUnits128::rfrom(self.get_minutes_ranged()) * t::NANOS_PER_MINUTE;
        nanos +=
            NoUnits128::rfrom(self.get_hours_ranged()) * t::NANOS_PER_HOUR;
        nanos +=
            NoUnits128::rfrom(self.get_days_ranged()) * t::NANOS_PER_CIVIL_DAY;
        nanos
    }

    /// Returns an equivalent span, but with all units greater than or equal to
    /// the one given set to zero.
    pub(crate) fn only_lower(self, unit: Unit) -> Span {
        let mut span = self;
        // Unit::Nanosecond is the minimum, so nothing can be smaller than it.
        if unit <= Unit::Microsecond {
            span = span.microseconds_ranged(C(0));
        }
        if unit <= Unit::Millisecond {
            span = span.milliseconds_ranged(C(0));
        }
        if unit <= Unit::Second {
            span = span.seconds_ranged(C(0));
        }
        if unit <= Unit::Minute {
            span = span.minutes_ranged(C(0));
        }
        if unit <= Unit::Hour {
            span = span.hours_ranged(C(0));
        }
        if unit <= Unit::Day {
            span = span.days_ranged(C(0));
        }
        if unit <= Unit::Week {
            span = span.weeks_ranged(C(0));
        }
        if unit <= Unit::Month {
            span = span.months_ranged(C(0));
        }
        if unit <= Unit::Year {
            span = span.years_ranged(C(0));
        }
        span
    }

    /// Returns an equivalent span, but with all units less than the one given
    /// set to zero.
    pub(crate) fn without_lower(self, unit: Unit) -> Span {
        let mut span = self;
        if unit > Unit::Nanosecond {
            span = span.nanoseconds_ranged(C(0));
        }
        if unit > Unit::Microsecond {
            span = span.microseconds_ranged(C(0));
        }
        if unit > Unit::Millisecond {
            span = span.milliseconds_ranged(C(0));
        }
        if unit > Unit::Second {
            span = span.seconds_ranged(C(0));
        }
        if unit > Unit::Minute {
            span = span.minutes_ranged(C(0));
        }
        if unit > Unit::Hour {
            span = span.hours_ranged(C(0));
        }
        if unit > Unit::Day {
            span = span.days_ranged(C(0));
        }
        if unit > Unit::Week {
            span = span.weeks_ranged(C(0));
        }
        if unit > Unit::Month {
            span = span.months_ranged(C(0));
        }
        // Unit::Year is the max, so nothing can be bigger than it.
        span
    }

    /// Returns the time parts of this span if and only if this span contains
    /// no non-time parts.
    ///
    /// # Errors
    ///
    /// This returns an error if this span exceeds what can be represented
    /// in a `TimeDuration`. It also returns an error if there are any non-zero
    /// units of days or greater.
    pub(crate) fn time_parts_to_duration(
        &self,
    ) -> Result<TimeDuration, Error> {
        if let Some(err) = self.smallest_non_time_non_zero_unit_error() {
            return Err(err);
        }
        self.only_time_parts_to_duration()
    }

    /// Returns *only* the time parts of this span as a [`TimeDuration`].
    ///
    /// That is, the `years`, `months`, `weeks` and `days` fields on a span
    /// are ignored.
    ///
    /// # Errors
    ///
    /// This returns an error if this span exceeds what can be represented
    /// in a `TimeDuration`.
    pub(crate) fn only_time_parts_to_duration(
        &self,
    ) -> Result<TimeDuration, Error> {
        TimeDuration::from_span(self)
    }

    /// Returns *only* the time/day parts of this span as a [`TimeDuration`].
    /// This assumes that all days are civil days. That is, that a day is
    /// always exactly `86,400` seconds long.
    ///
    /// # Errors
    ///
    /// This returns an error if this span exceeds what can be represented
    /// in a `TimeDuration`. It also returns an error if there are any non-zero
    /// units of months or years.
    pub(crate) fn time_civil_day_parts_to_duration(
        &self,
    ) -> Result<TimeDuration, Error> {
        if let Some(err) =
            self.smallest_non_time_non_civil_day_non_zero_unit_error()
        {
            return Err(err);
        }
        self.only_time_civil_day_parts_to_duration()
    }

    /// Returns *only* the time/day parts of this span as a [`TimeDuration`].
    /// This assumes that all days are civil days. That is, that a day is
    /// always exactly `86,400` seconds long.
    ///
    /// That is, the `years` and `months` fields on a span are ignored.
    ///
    /// # Errors
    ///
    /// This returns an error if this span exceeds what can be represented
    /// in a `TimeDuration`.
    pub(crate) fn only_time_civil_day_parts_to_duration(
        &self,
    ) -> Result<TimeDuration, Error> {
        TimeDuration::from_span(self)
    }

    /// Returns an error corresponding to the smallest non-time non-zero unit.
    ///
    /// If all non-time units are zero, then this returns `None`.
    pub(crate) fn smallest_non_time_non_zero_unit_error(
        &self,
    ) -> Option<Error> {
        if self.days != 0 {
            Some(t::SpanDays::error("days", self.days.get()))
        } else if self.weeks != 0 {
            Some(t::SpanWeeks::error("weeks", self.weeks.get()))
        } else if self.months != 0 {
            Some(t::SpanMonths::error("months", self.months.get()))
        } else if self.years != 0 {
            Some(t::SpanYears::error("years", self.years.get()))
        } else {
            None
        }
    }

    /// Returns the largest non-zero unit in this span.
    ///
    /// If all components of this span are zero, then `Unit::Nanosecond` is
    /// returned.
    pub(crate) fn largest_unit(&self) -> Unit {
        if self.years != 0 {
            Unit::Year
        } else if self.months != 0 {
            Unit::Month
        } else if self.weeks != 0 {
            Unit::Week
        } else if self.days != 0 {
            Unit::Day
        } else if self.hours != 0 {
            Unit::Hour
        } else if self.minutes != 0 {
            Unit::Minute
        } else if self.seconds != 0 {
            Unit::Second
        } else if self.milliseconds != 0 {
            Unit::Millisecond
        } else if self.microseconds != 0 {
            Unit::Microsecond
        } else {
            Unit::Nanosecond
        }
    }

    /// Returns an error corresponding to the smallest non-time/day/week
    /// non-zero unit.
    ///
    /// If all non-time/day/week units are zero, then this returns `None`.
    pub(crate) fn smallest_non_time_non_civil_day_non_zero_unit_error(
        &self,
    ) -> Option<Error> {
        if self.get_months_ranged() != 0 {
            Some(t::SpanMonths::error("months", self.months.get()))
        } else if self.get_years_ranged() != 0 {
            Some(t::SpanYears::error("years", self.years.get()))
        } else {
            None
        }
    }

    /// Given some new units to set on this span and the span updates with the
    /// new units, this determines the what the sign of `new_span` should be.
    fn resign(&self, units: impl RInto<NoUnits>, new: &Span) -> Sign {
        let units = units.rinto();
        // Negative units anywhere always makes the entire span negative.
        if units < 0 {
            return Sign::N::<-1>();
        }

        // FIXME: This seems pretty sub-optimal. We're doing a lot of work
        // every time we set a unit just to figure out the sign. There's gotta
        // be a better way.
        let was_is_zero = self.sign == 0;
        let new_is_zero = new.years == 0
            && new.months == 0
            && new.weeks == 0
            && new.days == 0
            && new.hours == 0
            && new.minutes == 0
            && new.seconds == 0
            && new.milliseconds == 0
            && new.microseconds == 0
            && new.nanoseconds == 0;
        match (was_is_zero, new_is_zero) {
            (_, true) => Sign::N::<0>(),
            (true, false) => units.signum().rinto(),
            // If the old and new span are both non-zero, and we know our new
            // units are not negative, then the sign remains unchanged.
            (false, false) => new.sign,
        }
    }
}

impl core::fmt::Display for Span {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        todo!()
    }
}

impl core::fmt::Debug for Span {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("Span")
            .field("sign", &self.sign.debug())
            .field("years", &self.years.debug())
            .field("months", &self.months.debug())
            .field("weeks", &self.weeks.debug())
            .field("days", &self.days.debug())
            .field("hours", &self.hours.debug())
            .field("minutes", &self.minutes.debug())
            .field("seconds", &self.seconds.debug())
            .field("milliseconds", &self.milliseconds.debug())
            .field("microseconds", &self.microseconds.debug())
            .field("nanoseconds", &self.nanoseconds.debug())
            .finish()
    }
}

impl Default for Span {
    fn default() -> Span {
        Span {
            sign: ri8::N::<0>(),
            years: C(0).rinto(),
            months: C(0).rinto(),
            weeks: C(0).rinto(),
            days: C(0).rinto(),
            hours: C(0).rinto(),
            minutes: C(0).rinto(),
            seconds: C(0).rinto(),
            milliseconds: C(0).rinto(),
            microseconds: C(0).rinto(),
            nanoseconds: C(0).rinto(),
        }
    }
}

impl core::ops::Neg for Span {
    type Output = Span;

    fn neg(self) -> Span {
        self.negate()
    }
}

/// This multiplies each unit in a span by an integer.
///
/// This panics on overflow. For checked arithmetic, use [`Span::checked_mul`].
impl core::ops::Mul<i64> for Span {
    type Output = Span;

    fn mul(self, rhs: i64) -> Span {
        self.checked_mul(rhs)
            .expect("multiplying `Span` by a scalar overflowed")
    }
}

// FIXME: This impl isn't so great, because it's probably generating Span
// values that are too big because of it combining all fields together.
// Instead, we might consider generating one unit at a time, and then using the
// "remainder" to determine the bounds with which to compute the next unit.
//
// Or perhaps even easier, generate only seconds/nanoseconds and then choose
// different rounding strategies from there to test how other fields are used.
// Year, I like that. But we need rounding. And we'll want to consider how to
// deal with the (yet to be added) `relative_to` field.
//
// OK for now, I'm just going to generate `TimeDuration` values and convert
// them to `Span` values. It won't get us full treatment, but I think it's the
// best we can do until we have the `Span` type built out a bit more.
#[cfg(test)]
impl quickcheck::Arbitrary for Span {
    fn arbitrary(g: &mut quickcheck::Gen) -> Span {
        TimeDuration::arbitrary(g).to_span()
    }

    fn shrink(&self) -> alloc::boxed::Box<dyn Iterator<Item = Self>> {
        alloc::boxed::Box::new(
            self.only_time_parts_to_duration()
                .unwrap()
                .shrink()
                .map(|d| d.to_span()),
        )
    }
}
/*
#[cfg(test)]
impl quickcheck::Arbitrary for Span {
    fn arbitrary(g: &mut quickcheck::Gen) -> Span {
        let sign =
            if bool::arbitrary(g) { ri8::N::<1>() } else { ri8::N::<-1>() };
        let years = SpanYears::arbitrary(g);
        let months = SpanMonths::arbitrary(g);
        let weeks = SpanWeeks::arbitrary(g);
        let days = SpanDays::arbitrary(g);
        let hours = SpanHours::arbitrary(g);
        let minutes = SpanMinutes::arbitrary(g);
        let seconds = SpanSeconds::arbitrary(g);
        let nanoseconds = SpanNanoseconds::arbitrary(g);
        Span {
            sign,
            years,
            months,
            weeks,
            days,
            hours,
            minutes,
            seconds,
            nanoseconds,
        }
    }

    fn shrink(&self) -> alloc::boxed::Box<dyn Iterator<Item = Self>> {
        alloc::boxed::Box::new(
            (
                (self.sign, self.years, self.months, self.weeks, self.days),
                (self.hours, self.minutes, self.seconds, self.nanoseconds),
            )
                .shrink()
                .filter_map(
                    |(
                        (sign, years, months, weeks, days),
                        (hours, minutes, seconds, nanoseconds),
                    )| {
                        if sign == 0 {
                            None
                        } else {
                            Some(Span {
                                sign,
                                years,
                                months,
                                weeks,
                                days,
                                hours,
                                minutes,
                                seconds,
                                nanoseconds,
                            })
                        }
                    },
                ),
        )
    }
}
*/

pub trait ToSpan: Sized {
    fn years(self) -> Span;
    fn months(self) -> Span;
    fn weeks(self) -> Span;
    fn days(self) -> Span;
    fn hours(self) -> Span;
    fn minutes(self) -> Span;
    fn seconds(self) -> Span;
    fn milliseconds(self) -> Span;
    fn microseconds(self) -> Span;
    fn nanoseconds(self) -> Span;

    fn year(self) -> Span {
        self.years()
    }
    fn month(self) -> Span {
        self.months()
    }
    fn week(self) -> Span {
        self.weeks()
    }
    fn day(self) -> Span {
        self.days()
    }
    fn hour(self) -> Span {
        self.hours()
    }
    fn minute(self) -> Span {
        self.minutes()
    }
    fn second(self) -> Span {
        self.seconds()
    }
    fn millisecond(self) -> Span {
        self.milliseconds()
    }
    fn microsecond(self) -> Span {
        self.microseconds()
    }
    fn nanosecond(self) -> Span {
        self.nanoseconds()
    }
}

macro_rules! impl_to_span {
    ($ty:ty) => {
        impl ToSpan for $ty {
            fn years(self) -> Span {
                Span::new().years(self)
            }
            fn months(self) -> Span {
                Span::new().months(self)
            }
            fn weeks(self) -> Span {
                Span::new().weeks(self)
            }
            fn days(self) -> Span {
                Span::new().days(self)
            }
            fn hours(self) -> Span {
                Span::new().hours(self)
            }
            fn minutes(self) -> Span {
                Span::new().minutes(self)
            }
            fn seconds(self) -> Span {
                Span::new().seconds(self)
            }
            fn milliseconds(self) -> Span {
                Span::new().milliseconds(self)
            }
            fn microseconds(self) -> Span {
                Span::new().microseconds(self)
            }
            fn nanoseconds(self) -> Span {
                Span::new().nanoseconds(self)
            }
        }
    };
}

impl_to_span!(i8);
impl_to_span!(i16);
impl_to_span!(i32);
impl_to_span!(i64);

#[cfg(test)]
mod tests {
    use crate::round::{RelativeTo, RoundMode};

    use super::*;

    #[test]
    fn test_total() {
        let span = 130.hours().minutes(20);
        let total = span.total(Unit::Second, None).unwrap();
        assert_eq!(total, 469200.0);

        let span = 123456789.seconds();
        let total = span.total(Unit::Day, None).unwrap();
        assert_eq!(total, 1428.8980208333332);

        let span = 2756.hours();
        let dt = civil::DateTime::constant(2020, 1, 1, 0, 0, 0, 0);
        let zdt = dt.to_zoned("Europe/Rome").unwrap();
        let relative = RelativeTo::Zoned(zdt);
        let total = span.total(Unit::Month, Some(relative.clone())).unwrap();
        assert_eq!(total, 3.7958333333333334);

        let relative = RelativeTo::Civil(dt);
        let total = span.total(Unit::Month, Some(relative.clone())).unwrap();
        assert_eq!(total, 3.7944444444444443);
    }

    #[test]
    fn test_compare() {
        let span1 = 79.hours().minutes(10);
        let span2 = 3.days().hours(7).seconds(630);
        let span3 = 3.days().hours(6).minutes(50);
        let mut array = [span1, span2, span3];
        array.sort_by(|sp1, sp2| sp1.compare(None, sp2).unwrap());
        assert_eq!(array, [span3, span1, span2]);

        let dt = civil::DateTime::constant(2020, 11, 1, 0, 0, 0, 0);
        let zdt = dt.to_zoned("America/Los_Angeles").unwrap();
        let relative = RelativeTo::Zoned(zdt);
        array.sort_by(|sp1, sp2| {
            sp1.compare(Some(relative.clone()), sp2).unwrap()
        });
        assert_eq!(array, [span1, span3, span2]);
    }

    #[test]
    fn test_checked_add() {
        let span1 = 1.hour();
        let span2 = 30.minutes();
        let sum = span1.checked_add(None, span2).unwrap();
        assert_eq!(sum, 1.hour().minutes(30));

        let span1 = 1.hour().minutes(30);
        let span2 = 2.hours().minutes(45);
        let sum = span1.checked_add(None, span2).unwrap();
        assert_eq!(sum, 4.hours().minutes(15));

        let span = 50
            .years()
            .months(50)
            .days(50)
            .hours(50)
            .minutes(50)
            .seconds(50)
            .milliseconds(500)
            .microseconds(500)
            .nanoseconds(500);
        let relative = RelativeTo::Civil(civil::DateTime::constant(
            1900, 1, 1, 0, 0, 0, 0,
        ));
        let sum = span.checked_add(Some(relative), span).unwrap();
        let expected = 108
            .years()
            .months(7)
            .days(12)
            .hours(5)
            .minutes(41)
            .seconds(41)
            .milliseconds(1)
            .microseconds(1)
            .nanoseconds(0);
        assert_eq!(sum, expected);

        let span = 1.month().days(15);
        let relative = RelativeTo::Civil(civil::DateTime::constant(
            2000, 2, 1, 0, 0, 0, 0,
        ));
        let sum = span.checked_add(Some(relative), span).unwrap();
        assert_eq!(sum, 3.months());
        let relative = RelativeTo::Civil(civil::DateTime::constant(
            2000, 3, 1, 0, 0, 0, 0,
        ));
        let sum = span.checked_add(Some(relative), span).unwrap();
        assert_eq!(sum, 2.months().days(30));
    }

    #[test]
    fn test_round_day_time() {
        let span = 29.seconds();
        let rounded = span.round(Unit::Minute);
        assert_eq!(rounded, 0.minute());

        let span = 30.seconds();
        let rounded = span.round(Unit::Minute);
        assert_eq!(rounded, 1.minute());

        let span = 8.seconds();
        let rounded =
            span.round(Unit::Nanosecond.largest(Some(Unit::Microsecond)));
        assert_eq!(rounded, 8_000_000.microseconds());

        let span = 130.minutes();
        let rounded = span.round(Round::new().largest(Some(Unit::Day)));
        assert_eq!(rounded, 2.hours().minutes(10));

        let span = 10.minutes().seconds(52);
        let rounded = span.round(Unit::Minute);
        assert_eq!(rounded, 11.minutes());

        let span = 10.minutes().seconds(52);
        let rounded = span.round(Unit::Minute.mode(RoundMode::Trunc));
        assert_eq!(rounded, 10.minutes());

        let span = 2.hours().minutes(34).seconds(18);
        let rounded = span.round(Round::new().largest(Some(Unit::Second)));
        assert_eq!(rounded, 9258.seconds());

        let span = 6.minutes();
        let rounded =
            span.round(Unit::Minute.increment(5).mode(RoundMode::Ceil));
        assert_eq!(rounded, 10.minutes());
    }

    #[test]
    fn test_round_relative_zoned_calendar() {
        let span = 2756.hours();
        let relative: crate::Zoned =
            civil::DateTime::constant(2020, 1, 1, 0, 0, 0, 0)
                .to_zoned("America/New_York")
                .unwrap();
        let options = Round::new()
            .largest(Some(Unit::Year))
            .smallest(Unit::Day)
            .relative_to_zoned(relative);
        let rounded = span.round(options);
        assert_eq!(rounded, 3.months().days(24));

        let span = 24.hours().nanoseconds(5);
        let relative: crate::Zoned =
            civil::DateTime::constant(2000, 10, 29, 0, 0, 0, 0)
                .to_zoned("America/Vancouver")
                .unwrap();
        let options = Round::new()
            .largest(Some(Unit::Day))
            .smallest(Unit::Minute)
            .relative_to_zoned(relative)
            .mode(RoundMode::Expand)
            .increment(30);
        let rounded = span.round(options);
        // It seems like this is the correct answer, although it apparently
        // differs from Temporal and the FullCalendar polyfill. I'm not sure
        // what accounts for the difference in the implementation.
        //
        // See: https://github.com/tc39/proposal-temporal/pull/2758#discussion_r1597255245
        assert_eq!(rounded, 24.hours().minutes(30));

        // Ref: https://github.com/tc39/proposal-temporal/issues/2816#issuecomment-2115608460
        let span = -1.month().hours(24);
        let relative: crate::Zoned =
            civil::DateTime::constant(2024, 4, 11, 2, 0, 0, 0)
                .to_zoned("America/New_York")
                .unwrap();
        let options = Round::new()
            .smallest(Unit::Millisecond)
            .relative_to_zoned(relative.clone());
        let rounded = span.round(options);
        assert_eq!(rounded, -1.month().days(1).hours(1));
        let dt = relative.checked_add(span).unwrap();
        let diff = relative.until_with_largest_unit(Unit::Month, &dt).unwrap();
        assert_eq!(diff, -1.month().days(1).hours(1));

        // Like the above, but don't use a datetime near a DST transition. In
        // this case, a day is a normal 24 hours. (Unlike above, where the
        // duration includes a 23 hour day, and so an additional hour has to be
        // added to the span to account for that.)
        let span = -1.month().hours(24);
        let relative: crate::Zoned =
            civil::DateTime::constant(2024, 6, 11, 2, 0, 0, 0)
                .to_zoned("America/New_York")
                .unwrap();
        let options = Round::new()
            .smallest(Unit::Millisecond)
            .relative_to_zoned(relative.clone());
        let rounded = span.round(options);
        assert_eq!(rounded, -1.month().days(1));
    }

    #[test]
    fn test_round_relative_zoned_time() {
        let span = 2756.hours();
        let relative: crate::Zoned =
            civil::DateTime::constant(2020, 1, 1, 0, 0, 0, 0)
                .to_zoned("America/New_York")
                .unwrap();
        let options =
            Round::new().largest(Some(Unit::Year)).relative_to_zoned(relative);
        let rounded = span.round(options);
        assert_eq!(rounded, 3.months().days(23).hours(21));

        let span = 2756.hours();
        let relative: crate::Zoned =
            civil::DateTime::constant(2020, 9, 1, 0, 0, 0, 0)
                .to_zoned("America/New_York")
                .unwrap();
        let options =
            Round::new().largest(Some(Unit::Year)).relative_to_zoned(relative);
        let rounded = span.round(options);
        assert_eq!(rounded, 3.months().days(23).hours(19));

        let span = 3.hours();
        let relative: crate::Zoned =
            civil::DateTime::constant(2020, 3, 8, 0, 0, 0, 0)
                .to_zoned("America/New_York")
                .unwrap();
        let options =
            Round::new().largest(Some(Unit::Year)).relative_to_zoned(relative);
        let rounded = span.round(options);
        assert_eq!(rounded, 3.hours());
    }

    #[test]
    fn test_round_relative_day_time() {
        let span = 2756.hours();
        let relative = civil::DateTime::constant(2020, 1, 1, 0, 0, 0, 0);
        let options =
            Round::new().largest(Some(Unit::Year)).relative_to_civil(relative);
        let rounded = span.round(options);
        assert_eq!(rounded, 3.months().days(23).hours(20));

        let span = 2756.hours();
        let relative = civil::DateTime::constant(2020, 9, 1, 0, 0, 0, 0);
        let options =
            Round::new().largest(Some(Unit::Year)).relative_to_civil(relative);
        let rounded = span.round(options);
        assert_eq!(rounded, 3.months().days(23).hours(20));

        let span = 190.days();
        let relative = civil::DateTime::constant(2020, 1, 1, 0, 0, 0, 0);
        let options =
            Round::new().largest(Some(Unit::Year)).relative_to_civil(relative);
        let rounded = span.round(options);
        assert_eq!(rounded, 6.months().days(8));

        let span = 30
            .days()
            .hours(23)
            .minutes(59)
            .seconds(59)
            .milliseconds(999)
            .microseconds(999)
            .nanoseconds(999);
        let relative = civil::DateTime::constant(2024, 5, 1, 0, 0, 0, 0);
        let options = Round::new()
            .smallest(Unit::Microsecond)
            .largest(Some(Unit::Year))
            .relative_to_civil(relative);
        let rounded = span.round(options);
        assert_eq!(rounded, 1.month());

        let span = 364
            .days()
            .hours(23)
            .minutes(59)
            .seconds(59)
            .milliseconds(999)
            .microseconds(999)
            .nanoseconds(999);
        let relative = civil::DateTime::constant(2023, 1, 1, 0, 0, 0, 0);
        let options = Round::new()
            .smallest(Unit::Microsecond)
            .largest(Some(Unit::Year))
            .relative_to_civil(relative);
        let rounded = span.round(options);
        assert_eq!(rounded, 1.year());

        let span = 365
            .days()
            .hours(23)
            .minutes(59)
            .seconds(59)
            .milliseconds(999)
            .microseconds(999)
            .nanoseconds(999);
        let relative = civil::DateTime::constant(2023, 1, 1, 0, 0, 0, 0);
        let options = Round::new()
            .smallest(Unit::Microsecond)
            .largest(Some(Unit::Year))
            .relative_to_civil(relative);
        let rounded = span.round(options);
        assert_eq!(rounded, 1.year().days(1));

        let span = 365
            .days()
            .hours(23)
            .minutes(59)
            .seconds(59)
            .milliseconds(999)
            .microseconds(999)
            .nanoseconds(999);
        let relative = civil::DateTime::constant(2024, 1, 1, 0, 0, 0, 0);
        let options = Round::new()
            .smallest(Unit::Microsecond)
            .largest(Some(Unit::Year))
            .relative_to_civil(relative);
        let rounded = span.round(options);
        assert_eq!(rounded, 1.year());

        let span = 3.hours();
        let relative = civil::DateTime::constant(2020, 3, 8, 0, 0, 0, 0);
        let options =
            Round::new().largest(Some(Unit::Year)).relative_to_civil(relative);
        let rounded = span.round(options);
        assert_eq!(rounded, 3.hours());
    }

    #[test]
    fn span_sign() {
        assert_eq!(Span::new().get_sign_ranged(), 0);
        assert_eq!(Span::new().days(1).get_sign_ranged(), 1);
        assert_eq!(Span::new().days(-1).get_sign_ranged(), -1);
        assert_eq!(Span::new().days(1).days(0).get_sign_ranged(), 0);
        assert_eq!(Span::new().days(-1).days(0).get_sign_ranged(), 0);
        assert_eq!(Span::new().years(1).days(1).days(0).get_sign_ranged(), 1);
        assert_eq!(
            Span::new().years(-1).days(-1).days(0).get_sign_ranged(),
            -1
        );
    }

    #[test]
    fn span_size() {
        #[cfg(target_pointer_width = "64")]
        {
            #[cfg(debug_assertions)]
            {
                assert_eq!(core::mem::align_of::<Span>(), 8);
                assert_eq!(core::mem::size_of::<Span>(), 184);
            }
            #[cfg(not(debug_assertions))]
            {
                assert_eq!(core::mem::align_of::<Span>(), 8);
                assert_eq!(core::mem::size_of::<Span>(), 64);
            }
        }
    }

    quickcheck::quickcheck! {
        fn prop_roundtrip_span_nanoseconds(span: Span) -> quickcheck::TestResult {
            let largest = span.largest_unit();
            if largest > Unit::Day {
                return quickcheck::TestResult::discard();
            }
            let nanos = span.to_invariant_nanoseconds();
            let got = Span::from_invariant_nanoseconds(largest, nanos).unwrap();
            quickcheck::TestResult::from_bool(nanos == got.to_invariant_nanoseconds())
        }
    }
}
