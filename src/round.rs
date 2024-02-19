use alloc::borrow::Cow;

use crate::{
    civil::{self, DateTime},
    error::{err, Error, ErrorContext},
    instant::{Instant, TimeScale},
    span::Span,
    tz::TimeZone,
    util::{
        rangeint::{ri128, RFrom, RInto},
        t::{
            self, Constant, NoUnits, NoUnits128, UnixNanoseconds,
            ZonedDayNanoseconds, C, C128,
        },
    },
    zoned::Zoned,
};

// Indexed by `Unit`.
static MAX_INCREMENT_INSTANT: &[Constant] = &[
    t::NANOS_PER_CIVIL_DAY,
    t::MICROS_PER_CIVIL_DAY,
    t::MILLIS_PER_CIVIL_DAY,
    t::SECONDS_PER_CIVIL_DAY,
    t::MINUTES_PER_CIVIL_DAY,
    t::HOURS_PER_CIVIL_DAY,
];

// Indexed by `Unit`.
static LIMIT_INCREMENT_CIVIL_DATETIME: &[Constant] = &[
    t::NANOS_PER_MICRO,
    t::MICROS_PER_MILLI,
    t::MILLIS_PER_SECOND,
    t::SECONDS_PER_MINUTE,
    t::MINUTES_PER_HOUR,
    t::HOURS_PER_CIVIL_DAY,
    Constant(2),
];

// Indexed by `Unit`.
static LIMIT_INCREMENT_CIVIL_TIME: &[Constant] = &[
    t::NANOS_PER_MICRO,
    t::MICROS_PER_MILLI,
    t::MILLIS_PER_SECOND,
    t::SECONDS_PER_MINUTE,
    t::MINUTES_PER_HOUR,
    t::HOURS_PER_CIVIL_DAY,
];

// Indexed by `Unit`.
static LIMIT_INCREMENT_SPAN: &[Constant] = &[
    t::NANOS_PER_MICRO,
    t::MICROS_PER_MILLI,
    t::MILLIS_PER_SECOND,
    t::SECONDS_PER_MINUTE,
    t::MINUTES_PER_HOUR,
    t::HOURS_PER_CIVIL_DAY,
];

#[derive(Clone, Debug)]
pub struct Round {
    largest: Option<Unit>,
    smallest: Unit,
    mode: RoundMode,
    increment: NoUnits,
    relative: Option<RelativeTo>,
}

impl Round {
    pub fn new() -> Round {
        Round::default()
    }

    pub fn smallest(self, unit: Unit) -> Round {
        Round { smallest: unit, ..self }
    }

    pub fn largest(self, unit: Option<Unit>) -> Round {
        Round { largest: unit, ..self }
    }

    pub fn mode(self, mode: RoundMode) -> Round {
        Round { mode, ..self }
    }

    pub fn increment(self, increment: i64) -> Round {
        // OK because `NoUnits` specifically allows any `i64` value.
        let increment = NoUnits::new(increment).unwrap();
        Round { increment, ..self }
    }

    pub fn relative_to_civil(self, datetime: DateTime) -> Round {
        let relative = Some(RelativeTo::from(datetime));
        Round { relative, ..self }
    }

    pub fn relative_to_zoned<S: TimeScale>(self, zoned: Zoned<S>) -> Round {
        let relative = Some(RelativeTo::from(zoned));
        Round { relative, ..self }
    }

    fn get_increment_with_max(
        &self,
        op: &'static str,
        max: &[Constant],
    ) -> Result<NoUnits128, Error> {
        if self.increment <= 0 {
            return Err(err!(
                "rounding increment {given} for {what} units must be \
                 greater than zero and less than or equal to {max}",
                given = self.increment.get(),
                what = self.smallest.singular(),
                max = i64::MAX,
            ));
        }
        let Some(must_divide) = max.get(self.smallest as usize) else {
            return Err(err!(
                "{op} does not support unit {unit}",
                unit = self.smallest.singular()
            ));
        };
        let must_divide = NoUnits::rfrom(*must_divide);
        if self.increment > must_divide || must_divide % self.increment != C(0)
        {
            Err(err!(
                "rounding increment {given} for {what} units \
                 must be 1) less than {must_divide}, 2) divide into \
                 it evenly and 3) greater than zero",
                given = self.increment.get(),
                what = self.smallest.singular(),
            ))
        } else {
            Ok(NoUnits128::rfrom(self.increment))
        }
    }

    fn get_increment_with_limit(
        &self,
        op: &'static str,
        limit: &[Constant],
    ) -> Result<NoUnits128, Error> {
        if self.increment <= 0 {
            return Err(err!(
                "rounding increment {given} for {what} units must be \
                 greater than zero and less than or equal to {max}",
                given = self.increment.get(),
                what = self.smallest.singular(),
                max = i64::MAX,
            ));
        }
        let Some(must_divide) = limit.get(self.smallest as usize) else {
            return Err(err!(
                "{op} does not support unit {unit}",
                unit = self.smallest.singular()
            ));
        };
        let must_divide = NoUnits::rfrom(*must_divide);
        if self.increment >= must_divide
            || must_divide % self.increment != C(0)
        {
            Err(err!(
                "rounding increment {given} for {what} units \
                 must be 1) less than {must_divide}, 2) divide into \
                 it evenly and 3) greater than zero",
                given = self.increment.get(),
                what = self.smallest.singular(),
            ))
        } else {
            Ok(NoUnits128::rfrom(self.increment))
        }
    }
}

impl Default for Round {
    fn default() -> Round {
        Round {
            largest: None,
            smallest: Unit::Nanosecond,
            mode: RoundMode::default(),
            increment: C(1).rinto(),
            relative: None,
        }
    }
}

impl From<Unit> for Round {
    fn from(unit: Unit) -> Round {
        Round::default().smallest(unit)
    }
}

// BREADCRUMBS: I kind of feel like the routines below should be on the
// DateTime and Time types, respectively. Morphing everything into a `Span`
// feels a little weird, although it is convenient. In particular, dealing with
// points in time is different than dealing with durations. The nice thing
// about using a `Span` though is that it carries all of the fields. So when
// balancing a `Time` overflows into days, then it's very easy and natural to
// capture that overflow in the `Span` itself.
//
// I also kind of wonder if we're handling negative values correctly. With
// `Time` it seemed fine since it's always positive. But dates can be negative.

impl Round {
    pub(crate) fn round_datetime(
        &self,
        day_length: Option<ZonedDayNanoseconds>,
        dt: DateTime,
    ) -> Result<DateTime, Error> {
        // ref: https://tc39.es/proposal-temporal/#sec-temporal.plaindatetime.prototype.round

        let day_length = NoUnits128::rfrom(
            day_length.unwrap_or(t::NANOS_PER_CIVIL_DAY.rinto()),
        );
        let increment = self.get_increment_with_limit(
            "datetime",
            LIMIT_INCREMENT_CIVIL_DATETIME,
        )?;
        // We permit rounding to any time unit and days, but nothing else.
        // We should support this, but Temporal doesn't. So for now, we're
        // sticking to what Temporal does because they're probably not doing
        // it for good reasons.
        match self.smallest {
            Unit::Year | Unit::Month | Unit::Week => {
                return Err(err!(
                    "rounding datetimes does not support unit {unit}",
                    unit = self.smallest.singular()
                ));
            }
            // We don't do any rounding in this case, so just bail now.
            Unit::Nanosecond if increment == 1 => {
                return Ok(dt);
            }
            _ => {}
        }

        let time_nanos = dt.time().to_civil_nanosecond();
        let sign = NoUnits128::rfrom(dt.date().year_ranged().signum());
        let time_rounded = self.mode.round_by_unit_in_nanoseconds(
            time_nanos,
            self.smallest,
            increment,
        );
        let days = sign * time_rounded.div_ceil(day_length);
        let time_nanos = time_rounded.rem_ceil(day_length);
        let time = civil::Time::from_civil_nanosecond(time_nanos);

        let date_days = t::SpanDays::rfrom(dt.date().day_ranged());
        let date_days_minus_1 =
            date_days.try_checked_sub("days", C(1)).with_context(|| {
                err!("failed to subtract 1 day from days in {dt}")
            })?;
        let days_len = date_days_minus_1
            .try_checked_add("days", days)
            .with_context(|| {
                err!("failed to add {days} days to {date_days} days from {dt}")
            })?;
        // OK because the first day of any month is always valid.
        let start = dt.date().first_of_month();
        let end = start
            .checked_add(Span::new().days_ranged(days_len))
            .with_context(|| {
                err!("adding {days_len} days to {start} failed")
            })?;
        Ok(DateTime::from_parts(end, time))
    }

    pub(crate) fn round_time(
        &self,
        time: civil::Time,
    ) -> Result<civil::Time, Error> {
        let increment = self.get_increment_with_limit(
            "time",
            LIMIT_INCREMENT_CIVIL_DATETIME,
        )?;
        let nanos = time.to_civil_nanosecond();
        let rounded = self.mode.round_by_unit_in_nanoseconds(
            nanos,
            self.smallest,
            increment,
        );
        let limit = NoUnits128::rfrom(t::CivilDayNanosecond::MAX_SELF) + C(1);
        Ok(civil::Time::from_civil_nanosecond(rounded % limit))
    }

    pub(crate) fn round_instant<S: TimeScale>(
        &self,
        instant: Instant<S>,
    ) -> Result<Instant<S>, Error> {
        use crate::instant::private::Nanoseconds;

        let increment =
            self.get_increment_with_max("instant", MAX_INCREMENT_INSTANT)?;
        let nanosecond = instant.as_nanosecond_ranged().to_no_units();
        let rounded = self.mode.round_by_unit_in_nanoseconds(
            nanosecond,
            self.smallest,
            increment,
        );
        let nanosecond = S::Nanoseconds::from_no_units(rounded);
        Ok(Instant::from_nanosecond_ranged(nanosecond))
    }

    pub(crate) fn round_span(&self, span: &Span) -> Result<Span, Error> {
        // We allow any kind of increment for calendar units, but for time
        // units, they have to divide evenly into the next highest unit (and
        // also be less than that). The reason for this is that calendar
        // units vary, where as for time units, given a balanced span, you
        // know that time units will always spill over into days so that
        // hours/minutes/... will never exceed 24/60/...
        let increment = match self.smallest {
            Unit::Year | Unit::Month | Unit::Week | Unit::Day => {
                self.increment.rinto()
            }
            _ => self.get_increment_with_limit(
                "rounding span",
                LIMIT_INCREMENT_SPAN,
            )?,
        };
        let mode = self.mode;
        let smallest = self.smallest;
        let existing_largest = span.largest_unit();
        let largest =
            self.largest.unwrap_or_else(|| smallest.max(existing_largest));
        let max = existing_largest.max(largest);
        if largest < smallest {
            return Err(err!(
                "largest unit ('{largest}') cannot be smaller than \
                 smallest unit ('{smallest}')",
                largest = largest.singular(),
                smallest = smallest.singular(),
            ));
        }
        let relative = match self.relative {
            Some(ref r) => {
                // If our reference point is civil time, then its units are
                // invariant as long as we are using day-or-lower everywhere.
                // That is, the length of the duration is independent of the
                // reference point. In which case, rounding is a simple matter
                // of converting the span to a number of nanoseconds and then
                // rounding that.
                if !r.is_variable(max) {
                    return Ok(round_day_time(
                        &span, smallest, largest, increment, mode,
                    )?);
                }
                r.to_balanced_span(largest, *span)?
            }
            None => {
                // This is only okay if none of our units are above 'day'.
                // That is, a reference point is only necessary when there is
                // no reasonable invariant interpretation of the span. And this
                // is only true when everything is less than 'day'.
                if smallest.is_definitively_variable() {
                    return Err(err!(
                        "using unit '{unit}' in round option 'smallest' \
                         requires that a relative reference time be given, \
                         but none was provided",
                        unit = smallest.singular(),
                    ));
                }
                if largest.is_definitively_variable() {
                    return Err(err!(
                        "using unit '{unit}' in round option 'largest' \
                         requires that a relative reference time be given, \
                         but none was provided",
                        unit = largest.singular(),
                    ));
                }
                if existing_largest.is_definitively_variable() {
                    return Err(err!(
                        "using largest unit (which is '{unit}') in given span \
                         requires that a relative reference time be given, \
                         but none was provided",
                        unit = existing_largest.singular(),
                    ));
                }
                assert!(max <= Unit::Day);
                return Ok(round_day_time(
                    &span, smallest, largest, increment, mode,
                )?);
            }
        };
        if span.get_sign_ranged() != 0
            && relative.span.get_sign_ranged() != 0
            && span.get_sign_ranged() != relative.span.get_sign_ranged()
        {
            // I haven't quite figured out when this case is hit. I think it's
            // actually impossible right? Balancing a duration should not flip
            // the sign.
            //
            // ref: https://github.com/fullcalendar/temporal-polyfill/blob/9e001042864394247181d1a5d591c18057ce32d2/packages/temporal-polyfill/src/internal/durationMath.ts#L236-L238
            unreachable!(
                "balanced span should have same sign as original span"
            )
        }
        round_relative(&relative, smallest, largest, increment, mode)
    }
}

/// # Examples
///
/// This example demonstrates that `Unit` has an ordering defined such that
/// bigger units compare greater than smaller units.
///
/// ```
/// use jiff::round::Unit;
///
/// assert!(Unit::Year > Unit::Nanosecond);
/// assert!(Unit::Day > Unit::Hour);
/// assert!(Unit::Hour > Unit::Minute);
/// assert!(Unit::Hour > Unit::Minute);
/// assert_eq!(Unit::Hour, Unit::Hour);
/// ```
#[non_exhaustive]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub enum Unit {
    Year = 9,
    Month = 8,
    Week = 7,
    Day = 6,
    Hour = 5,
    Minute = 4,
    Second = 3,
    Millisecond = 2,
    Microsecond = 1,
    Nanosecond = 0,
}

impl Unit {
    pub fn mode(self, mode: RoundMode) -> Round {
        Round::from(self).mode(mode)
    }

    pub fn largest(self, unit: Option<Unit>) -> Round {
        Round::from(self).largest(unit)
    }

    pub fn increment(self, increment: i64) -> Round {
        Round::from(self).increment(increment)
    }

    pub fn relative_to_civil(self, datetime: DateTime) -> Round {
        Round::from(self).relative_to_civil(datetime)
    }

    pub fn relative_to_zoned<S: TimeScale>(self, zoned: Zoned<S>) -> Round {
        Round::from(self).relative_to_zoned(zoned)
    }

    /// Returns the next biggest unit, if one exists.
    pub(crate) fn next(&self) -> Option<Unit> {
        match *self {
            Unit::Year => None,
            Unit::Month => Some(Unit::Year),
            Unit::Week => Some(Unit::Month),
            Unit::Day => Some(Unit::Week),
            Unit::Hour => Some(Unit::Day),
            Unit::Minute => Some(Unit::Hour),
            Unit::Second => Some(Unit::Minute),
            Unit::Millisecond => Some(Unit::Second),
            Unit::Microsecond => Some(Unit::Millisecond),
            Unit::Nanosecond => Some(Unit::Microsecond),
        }
    }

    /// Returns the number of nanoseconds in this unit as a 128-bit integer.
    ///
    /// # Panics
    ///
    /// When this unit is definitively variable. That is, years, months or
    /// weeks.
    pub(crate) fn nanoseconds(self) -> NoUnits128 {
        match self {
            Unit::Nanosecond => Constant(1),
            Unit::Microsecond => t::NANOS_PER_MICRO,
            Unit::Millisecond => t::NANOS_PER_MILLI,
            Unit::Second => t::NANOS_PER_SECOND,
            Unit::Minute => t::NANOS_PER_MINUTE,
            Unit::Hour => t::NANOS_PER_HOUR,
            Unit::Day => t::NANOS_PER_CIVIL_DAY,
            unit => unreachable!("{unit:?} has no definitive time interval"),
        }
        .rinto()
    }

    /// Returns true when this unit is definitively variable.
    ///
    /// In effect, this is any unit bigger than 'day', because any such unit
    /// can vary in time depending on its reference point. A 'day' can as well,
    /// but we sorta special case 'day' to mean '24 hours' for cases where
    /// the user is dealing with civil time.
    pub(crate) fn is_definitively_variable(self) -> bool {
        matches!(self, Unit::Year | Unit::Month | Unit::Week)
    }

    /// A human readable singular description of this unit of time.
    pub(crate) fn singular(&self) -> &'static str {
        match *self {
            Unit::Year => "year",
            Unit::Month => "month",
            Unit::Week => "week",
            Unit::Day => "day",
            Unit::Hour => "hour",
            Unit::Minute => "minute",
            Unit::Second => "second",
            Unit::Millisecond => "millisecond",
            Unit::Microsecond => "microsecond",
            Unit::Nanosecond => "nanosecond",
        }
    }

    /// A human readable plural description of this unit of time.
    pub(crate) fn plural(&self) -> &'static str {
        match *self {
            Unit::Year => "years",
            Unit::Month => "months",
            Unit::Week => "weeks",
            Unit::Day => "days",
            Unit::Hour => "hours",
            Unit::Minute => "minutes",
            Unit::Second => "seconds",
            Unit::Millisecond => "milliseconds",
            Unit::Microsecond => "microseconds",
            Unit::Nanosecond => "nanoseconds",
        }
    }
}

#[cfg(test)]
impl Unit {
    fn from_usize(n: usize) -> Option<Unit> {
        match n {
            0 => Some(Unit::Nanosecond),
            1 => Some(Unit::Microsecond),
            2 => Some(Unit::Millisecond),
            3 => Some(Unit::Second),
            4 => Some(Unit::Minute),
            5 => Some(Unit::Hour),
            6 => Some(Unit::Day),
            7 => Some(Unit::Week),
            8 => Some(Unit::Month),
            9 => Some(Unit::Year),
            _ => None,
        }
    }

    fn to_usize(self) -> usize {
        self as usize
    }
}

#[cfg(test)]
impl quickcheck::Arbitrary for Unit {
    fn arbitrary(g: &mut quickcheck::Gen) -> Unit {
        Unit::from_usize(usize::arbitrary(g) % 10).unwrap()
    }

    fn shrink(&self) -> alloc::boxed::Box<dyn Iterator<Item = Self>> {
        alloc::boxed::Box::new(
            (*self as usize)
                .shrink()
                .map(|n| Unit::from_usize(n % 10).unwrap()),
        )
    }
}

#[non_exhaustive]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub enum RoundMode {
    /// Rounds toward positive infinity.
    Ceil,
    /// Rounds toward negative infinity.
    Floor,
    /// Rounds away from zero.
    Expand,
    /// Rounds toward zero.
    Trunc,
    /// Rounds at ties toward positive infinity.
    HalfCeil,
    /// Rounds at ties toeard negative infinity.
    HalfFloor,
    /// Rounds at ties away from zero.
    #[default]
    HalfExpand,
    /// Rounds at ties toward zero.
    HalfTrunc,
    /// Rounds at ties toward an even rounding increment multiple.
    HalfEven,
}

impl RoundMode {
    /// Given a `quantity` in nanoseconds and an `increment` in units of
    /// `unit`, this rounds it according to this mode and returns the result
    /// in units of `unit`.
    fn round_by_unit(
        self,
        quantity: impl RInto<NoUnits128>,
        unit: Unit,
        increment: impl RInto<NoUnits128>,
    ) -> NoUnits128 {
        let per = unit.nanoseconds();
        self.round_by_unit_in_nanoseconds(quantity, unit, increment) / per
    }

    /// Given a `quantity` in nanoseconds and an `increment` in units of
    /// `unit`, this rounds it according to this mode and returns the result
    /// in nanoseconds.
    fn round_by_unit_in_nanoseconds(
        self,
        quantity: impl RInto<NoUnits128>,
        unit: Unit,
        increment: impl RInto<NoUnits128>,
    ) -> NoUnits128 {
        let quantity = quantity.rinto();
        let increment = unit.nanoseconds() * increment.rinto();
        let rounded = self.round(quantity, increment);
        rounded
    }

    fn round(
        self,
        quantity: impl RInto<NoUnits128>,
        increment: impl RInto<NoUnits128>,
    ) -> NoUnits128 {
        // ref: https://tc39.es/proposal-temporal/#sec-temporal-roundnumbertoincrement
        fn inner(
            mode: RoundMode,
            quantity: NoUnits128,
            increment: NoUnits128,
        ) -> NoUnits128 {
            let mut quotient = quantity.div_ceil(increment);
            let remainder = quantity.rem_ceil(increment);
            if remainder == 0 {
                return quantity;
            }
            let sign = if remainder < 0 { C128(-1) } else { C128(1) };
            let tiebreaker = (remainder * C128(2)).abs();
            let tie = tiebreaker == increment;
            let expand_is_nearer = tiebreaker > increment;
            // ref: https://tc39.es/proposal-temporal/#sec-temporal-roundnumbertoincrement
            match mode {
                RoundMode::Ceil => {
                    if sign > 0 {
                        quotient += sign;
                    }
                }
                RoundMode::Floor => {
                    if sign < 0 {
                        quotient += sign;
                    }
                }
                RoundMode::Expand => {
                    quotient += sign;
                }
                RoundMode::Trunc => {}
                RoundMode::HalfCeil => {
                    if expand_is_nearer || (tie && sign > 0) {
                        quotient += sign;
                    }
                }
                RoundMode::HalfFloor => {
                    if expand_is_nearer || (tie && sign < 0) {
                        quotient += sign;
                    }
                }
                RoundMode::HalfExpand => {
                    if expand_is_nearer || tie {
                        quotient += sign;
                    }
                }
                RoundMode::HalfTrunc => {
                    if expand_is_nearer {
                        quotient += sign;
                    }
                }
                RoundMode::HalfEven => {
                    if expand_is_nearer || (tie && quotient % C(2) == 1) {
                        quotient += sign;
                    }
                }
            }
            // We use saturating arithmetic here because this can overflow
            // when `quantity` is the max value. Since we're rounding, we just
            // refuse to go over the maximum. I'm not 100% convinced this is
            // correct, but I think the only alternative is to return an error,
            // and I'm not sure that's ideal either.
            quotient.saturating_mul(increment)
        }
        inner(self, quantity.rinto(), increment.rinto())
    }

    fn round_float(self, quantity: f64, increment: NoUnits128) -> NoUnits128 {
        let quotient = quantity / (increment.get() as f64);
        let rounded = match self {
            RoundMode::Ceil => quotient.ceil(),
            RoundMode::Floor => quotient.floor(),
            RoundMode::Expand => {
                if quotient < 0.0 {
                    quotient.floor()
                } else {
                    quotient.ceil()
                }
            }
            RoundMode::Trunc => quotient.trunc(),
            RoundMode::HalfCeil => {
                if quotient % 1.0 == 0.5 {
                    quotient.ceil()
                } else {
                    quotient.round()
                }
            }
            RoundMode::HalfFloor => {
                if quotient % 1.0 == 0.5 {
                    quotient.floor()
                } else {
                    quotient.round()
                }
            }
            RoundMode::HalfExpand => {
                quotient.signum() * quotient.abs().round()
            }
            RoundMode::HalfTrunc => {
                if quotient % 1.0 == 0.5 {
                    quotient.trunc()
                } else {
                    quotient.round()
                }
            }
            RoundMode::HalfEven => {
                if quotient % 1.0 == 0.5 {
                    quotient.trunc() + (quotient % 2.0)
                } else {
                    quotient.round()
                }
            }
        };
        let rounded = NoUnits128::rfrom(NoUnits::new(rounded as i64).unwrap());
        rounded.saturating_mul(increment)
    }
}

/// A reference datetime to use when rounding a span.
///
/// The reference datetime may have an associated time zone if the caller wants
/// rounding to take time zones and DST into account when rounding.
#[derive(Clone, Debug)]
pub enum RelativeTo {
    Civil(DateTime),
    // FIXME: The fact that we just assume a Unix time scale here is very
    // annoying. Threading a type parameter through here is immensely annoying.
    // We'd need a "dummy" type for the case of a civil datetime, for example.
    // This would infect `RelativeTo` as well, and thus, in turn, infect
    // `Round`. That's awful.
    //
    // What if `Instant` only supported `Unix` and `TAI`, and we used runtime
    // state to determine its time scale instead of pushing it into the type
    // system? Having it in the type system is very useful because it's nice
    // to know that you have leap second support or not. But the type parameter
    // is just brutal.
    Zoned(Zoned),
}

impl RelativeTo {
    fn is_zoned(&self) -> bool {
        matches!(*self, RelativeTo::Zoned { .. })
    }

    /// Returns true when the given unit is variable relative to this reference
    /// point.
    ///
    /// In effect, days and greater are variable when the reference point has
    /// a time zone. Otherwise, only weeks and greater are variable.
    pub(crate) fn is_variable(&self, unit: Unit) -> bool {
        if unit.is_definitively_variable() {
            return true;
        }
        unit == Unit::Day && self.is_zoned()
    }

    pub(crate) fn checked_add(&self, span: Span) -> Result<RelativeTo, Error> {
        match *self {
            RelativeTo::Civil(ref datetime) => Ok(RelativeTo::Civil(
                datetime.checked_add(span).with_context(|| {
                    err!("failed to add {datetime} to {span}",)
                })?,
            )),
            RelativeTo::Zoned(ref zoned) => {
                Ok(RelativeTo::Zoned(zoned.checked_add(span).with_context(
                    || err!("failed to add {zoned} to {span}",),
                )?))
            }
        }
    }

    pub(crate) fn until_with_largest_unit(
        &self,
        largest: Unit,
        other: &RelativeTo,
    ) -> Result<Span, Error> {
        match (self, other) {
            (&RelativeTo::Civil(dt1), &RelativeTo::Civil(dt2)) => Ok(dt1
                .until_with_largest_unit(largest, dt2)
                .with_context(|| {
                    err!(
                        "failed to get span between {dt1} and {dt2} \
                         with largest unit as {unit}",
                        unit = largest.plural(),
                    )
                })?),
            (&RelativeTo::Zoned(ref zdt1), &RelativeTo::Zoned(ref zdt2)) => {
                Ok(zdt1.until_with_largest_unit(largest, zdt2).with_context(
                    || {
                        err!(
                            "failed to get span between {zdt1} and {zdt2} \
                             with largest unit as {unit}",
                            unit = largest.plural(),
                        )
                    },
                )?)
            }
            _ => todo!(),
        }
    }

    pub(crate) fn to_balanced_span(
        &self,
        largest: Unit,
        span: Span,
    ) -> Result<RelativeSpan, Error> {
        let range = match *self {
            RelativeTo::Civil(datetime) => {
                let instant =
                    TimeZone::UTC.to_instant(datetime).with_context(|| {
                        err!("failed to convert {datetime} to instant")
                    })?;
                let start = RelativeCivil { datetime, instant };
                let end = start.checked_add(span)?;
                RelativeRange::Civil { start, end }
            }
            RelativeTo::Zoned(ref zoned) => {
                let datetime = zoned.to_datetime();
                let zoned = zoned.clone();
                let start = RelativeZoned { datetime, zoned };
                let end = start.checked_add(span)?;
                RelativeRange::Zoned { start, end }
            }
        };
        let span = range.to_balanced_span(largest)?;
        Ok(RelativeSpan { span, range })
    }

    pub(crate) fn to_nanosecond(&self) -> Result<NoUnits128, Error> {
        match *self {
            RelativeTo::Civil(dt) => {
                let instant =
                    TimeZone::UTC.to_instant(dt).with_context(|| {
                        err!("failed to convert {dt} to instant")
                    })?;
                Ok(instant.as_nanosecond_ranged().rinto())
            }
            RelativeTo::Zoned(ref zdt) => {
                Ok(zdt.to_instant().as_nanosecond_ranged().rinto())
            }
        }
    }
}

impl From<DateTime> for RelativeTo {
    fn from(datetime: DateTime) -> RelativeTo {
        RelativeTo::Civil(datetime)
    }
}

impl<S: TimeScale> From<Zoned<S>> for RelativeTo {
    fn from(zoned: Zoned<S>) -> RelativeTo {
        RelativeTo::Zoned(zoned.to_unix_scale())
    }
}

#[derive(Clone, Debug)]
pub(crate) struct RelativeSpan {
    pub(crate) span: Span,
    pub(crate) range: RelativeRange,
}

#[derive(Clone, Debug)]
pub(crate) enum RelativeRange {
    Civil { start: RelativeCivil, end: RelativeCivil },
    Zoned { start: RelativeZoned, end: RelativeZoned },
}

impl RelativeRange {
    fn is_zoned(&self) -> bool {
        matches!(*self, RelativeRange::Zoned { .. })
    }

    /// Returns true when the given unit is variable relative to this reference
    /// point.
    ///
    /// In effect, days and greater are variable when the reference point has
    /// a time zone. Otherwise, only weeks and greater are variable.
    pub(crate) fn is_variable(&self, unit: Unit) -> bool {
        if unit.is_definitively_variable() {
            return true;
        }
        unit == Unit::Day && self.is_zoned()
    }

    fn to_balanced_span(&self, largest: Unit) -> Result<Span, Error> {
        match *self {
            RelativeRange::Civil { ref start, ref end } => start
                .datetime
                .until_with_largest_unit(largest, end.datetime)
                .with_context(|| {
                    err!(
                        "failed to get span between {start} and {end} \
                         with largest unit as {unit}",
                        start = start.datetime,
                        end = end.datetime,
                        unit = largest.plural(),
                    )
                }),
            RelativeRange::Zoned { ref start, ref end } => start
                .zoned
                .until_with_largest_unit(largest, &end.zoned)
                .with_context(|| {
                    err!(
                        "failed to get span between {start} and {end} \
                         with largest unit as {unit}",
                        start = start.zoned,
                        end = end.zoned,
                        unit = largest.plural(),
                    )
                }),
        }
    }

    fn start(&self) -> RelativeCow<'_> {
        match *self {
            RelativeRange::Civil { ref start, .. } => {
                RelativeCow::Civil(Cow::Borrowed(start))
            }
            RelativeRange::Zoned { ref start, .. } => {
                RelativeCow::Zoned(Cow::Borrowed(start))
            }
        }
    }

    fn end(&self) -> RelativeCow<'_> {
        match *self {
            RelativeRange::Civil { ref end, .. } => {
                RelativeCow::Civil(Cow::Borrowed(end))
            }
            RelativeRange::Zoned { ref end, .. } => {
                RelativeCow::Zoned(Cow::Borrowed(end))
            }
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) enum RelativeCow<'a> {
    Civil(Cow<'a, RelativeCivil>),
    Zoned(Cow<'a, RelativeZoned>),
}

impl<'a> RelativeCow<'a> {
    fn checked_add(&self, span: Span) -> Result<RelativeCow<'static>, Error> {
        match *self {
            RelativeCow::Civil(ref r) => {
                Ok(RelativeCow::Civil(Cow::Owned(r.checked_add(span)?)))
            }
            RelativeCow::Zoned(ref r) => {
                Ok(RelativeCow::Zoned(Cow::Owned(r.checked_add(span)?)))
            }
        }
    }

    pub(crate) fn to_nanosecond(&self) -> NoUnits128 {
        match *self {
            RelativeCow::Civil(ref r) => {
                r.instant.as_nanosecond_ranged().rinto()
            }
            RelativeCow::Zoned(ref r) => {
                r.zoned.to_instant().as_nanosecond_ranged().rinto()
            }
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct RelativeCivil {
    datetime: DateTime,
    instant: Instant,
}

impl RelativeCivil {
    /// Returns true when the given unit is variable relative to this reference
    /// point.
    ///
    /// In effect, days and greater are variable when the reference point has
    /// a time zone. Otherwise, only weeks and greater are variable.
    fn is_variable(&self, unit: Unit) -> bool {
        unit.is_definitively_variable()
    }

    fn checked_add(&self, span: Span) -> Result<RelativeCivil, Error> {
        let datetime = self.datetime.checked_add(span).with_context(|| {
            err!(
                "failed to add {datetime} to {span}",
                datetime = self.datetime,
            )
        })?;
        let instant =
            TimeZone::UTC.to_instant(datetime).with_context(|| {
                err!("failed to convert {datetime} to instant")
            })?;
        Ok(RelativeCivil { datetime, instant })
    }
}

#[derive(Clone, Debug)]
pub(crate) struct RelativeZoned {
    datetime: DateTime,
    zoned: Zoned,
}

impl RelativeZoned {
    /// Returns true when the given unit is variable relative to this reference
    /// point.
    ///
    /// In effect, days and greater are variable when the reference point has
    /// a time zone. Otherwise, only weeks and greater are variable.
    fn is_variable(&self, unit: Unit) -> bool {
        unit.is_definitively_variable() || unit == Unit::Day
    }

    fn checked_add(&self, span: Span) -> Result<RelativeZoned, Error> {
        let zoned = self.zoned.checked_add(span).with_context(|| {
            err!("failed to add {zoned} to {span}", zoned = self.zoned)
        })?;
        let datetime = zoned.to_datetime();
        Ok(RelativeZoned { datetime, zoned })
    }
}

fn round_day_time(
    span: &Span,
    smallest: Unit,
    largest: Unit,
    increment: NoUnits128,
    mode: RoundMode,
) -> Result<Span, Error> {
    assert!(smallest <= Unit::Day);
    assert!(largest <= Unit::Day);
    let nanos = span.to_invariant_nanoseconds();
    let rounded =
        mode.round_by_unit_in_nanoseconds(nanos, smallest, increment);
    Span::from_invariant_nanoseconds(largest, rounded).with_context(|| {
        err!(
            "failed to convert rounded nanoseconds {rounded} \
             to span for largest unit as {unit}",
            unit = largest.plural(),
        )
    })
}

fn round_relative(
    relative: &RelativeSpan,
    smallest: Unit,
    largest: Unit,
    increment: NoUnits128,
    mode: RoundMode,
) -> Result<Span, Error> {
    if relative.span.get_sign_ranged() == 0 {
        return Ok(relative.span);
    }
    let nudge = match relative.range {
        RelativeRange::Civil { ref start, ref end } => {
            if smallest.is_definitively_variable() {
                nudge_relative_span(
                    &relative.span,
                    &RelativeCow::Civil(Cow::Borrowed(start)),
                    &RelativeCow::Civil(Cow::Borrowed(end)),
                    smallest,
                    increment,
                    mode,
                )?
            } else {
                let relative_end = end.instant.as_nanosecond_ranged();
                nudge_relative_day_time_span(
                    &relative.span,
                    relative_end.rinto(),
                    smallest,
                    largest,
                    increment,
                    mode,
                )?
            }
        }
        RelativeRange::Zoned { ref start, ref end } => {
            if relative.range.is_variable(smallest) {
                nudge_relative_span(
                    &relative.span,
                    &RelativeCow::Zoned(Cow::Borrowed(start)),
                    &RelativeCow::Zoned(Cow::Borrowed(end)),
                    smallest,
                    increment,
                    mode,
                )?
            } else {
                nudge_relative_zoned_time_span(
                    &relative.span,
                    start,
                    smallest,
                    increment,
                    mode,
                )?
            }
        }
    };
    if nudge.grew_big_unit && smallest != Unit::Week {
        Ok(bubble(relative, &nudge, smallest, largest)?)
    } else {
        Ok(nudge.span)
    }
}

#[derive(Debug)]
struct Nudge {
    span: Span,
    rounded_relative_end: NoUnits128,
    grew_big_unit: bool,
}

fn nudge_relative_span(
    balanced: &Span,
    relative_start: &RelativeCow<'_>,
    relative_end: &RelativeCow<'_>,
    smallest: Unit,
    increment: NoUnits128,
    mode: RoundMode,
) -> Result<Nudge, Error> {
    assert!(smallest >= Unit::Day);
    let sign = balanced.get_sign_ranged();
    let truncated =
        increment * balanced.get_units_ranged(smallest).div_ceil(increment);
    let span = balanced
        .without_lower(smallest)
        .try_units_ranged(smallest, truncated)
        .with_context(|| {
            err!(
                "failed to set {unit} to {truncated} on span {balanced}",
                unit = smallest.singular()
            )
        })?;
    let (relative0, relative1) = clamp_relative_span(
        &span,
        relative_start,
        smallest,
        (increment * sign).rinto(),
    )?;

    // FIXME: This is brutal. This is the only non-optional floating point
    // used so far in Jiff. We do expose floating point for things like
    // `Span::total`, but that's optional and not a core part of Jiff's
    // functionality. This is in the core part of Jiff's span rounding...
    let denom = (relative1 - relative0).get() as f64;
    let numer = (relative_end.to_nanosecond() - relative0).get() as f64;
    let exact = (truncated.get() as f64)
        + (numer / denom) * (sign.get() as f64) * (increment.get() as f64);
    let rounded = mode.round_float(exact, increment);
    let grew_big_unit =
        ((rounded.get() as f64) - exact).signum() == (sign.get() as f64);

    let span =
        span.try_units_ranged(smallest, rounded).with_context(|| {
            err!(
                "failed to set {unit} to {truncated} on span {span}",
                unit = smallest.singular()
            )
        })?;
    let rounded_relative_end =
        if grew_big_unit { relative1 } else { relative0 };
    Ok(Nudge { span, rounded_relative_end, grew_big_unit })
}

fn nudge_relative_zoned_time_span(
    balanced: &Span,
    relative_start: &RelativeZoned,
    smallest: Unit,
    increment: NoUnits128,
    mode: RoundMode,
) -> Result<Nudge, Error> {
    let sign = balanced.get_sign_ranged();
    let time_nanos = balanced.only_lower(Unit::Day).to_invariant_nanoseconds();
    let mut rounded_time_nanos =
        mode.round_by_unit_in_nanoseconds(time_nanos, smallest, increment);
    let (relative0, relative1) = clamp_relative_span(
        &balanced.without_lower(Unit::Day),
        &RelativeCow::Zoned(Cow::Borrowed(relative_start)),
        Unit::Day,
        sign.rinto(),
    )?;
    let day_nanos = relative1 - relative0;
    let beyond_day_nanos = rounded_time_nanos - day_nanos;

    let mut day_delta = NoUnits::N::<0>();
    let rounded_relative_end =
        if beyond_day_nanos == 0 || beyond_day_nanos.signum() == sign {
            day_delta += C(1);
            rounded_time_nanos = mode.round_by_unit_in_nanoseconds(
                beyond_day_nanos,
                smallest,
                increment,
            );
            relative1 + rounded_time_nanos
        } else {
            relative0 + rounded_time_nanos
        };

    let span =
        Span::from_invariant_nanoseconds(Unit::Hour, rounded_time_nanos)
            .with_context(|| {
                err!(
                    "failed to convert rounded nanoseconds \
                     {rounded_time_nanos} to span for largest unit as {unit}",
                    unit = Unit::Hour.plural(),
                )
            })?
            .years_ranged(balanced.get_years_ranged())
            .months_ranged(balanced.get_months_ranged())
            .weeks_ranged(balanced.get_weeks_ranged())
            .days_ranged(balanced.get_days_ranged() + day_delta);
    let grew_big_unit = day_delta != 0;
    Ok(Nudge { span, rounded_relative_end, grew_big_unit })
}

fn nudge_relative_day_time_span(
    balanced: &Span,
    relative_end: NoUnits128,
    smallest: Unit,
    largest: Unit,
    increment: NoUnits128,
    mode: RoundMode,
) -> Result<Nudge, Error> {
    assert!(smallest <= Unit::Day);

    let sign = balanced.get_sign_ranged();
    let balanced_nanos = balanced.to_invariant_nanoseconds();
    let rounded_nanos =
        mode.round_by_unit_in_nanoseconds(balanced_nanos, smallest, increment);
    let diff_nanos = rounded_nanos - balanced_nanos;
    let diff_days = rounded_nanos.div_ceil(t::NANOS_PER_CIVIL_DAY)
        - balanced_nanos.div_ceil(t::NANOS_PER_CIVIL_DAY);
    let grew_big_unit = diff_days.signum() == sign;
    let span = Span::from_invariant_nanoseconds(largest, rounded_nanos)
        .with_context(|| {
            err!(
                "failed to convert rounded nanoseconds {rounded_nanos} \
                 to span for largest unit as {unit}",
                unit = largest.plural(),
            )
        })?
        .years_ranged(balanced.get_years_ranged())
        .months_ranged(balanced.get_months_ranged())
        .weeks_ranged(balanced.get_weeks_ranged());
    let rounded_relative_end = relative_end + diff_nanos;
    Ok(Nudge { span, rounded_relative_end, grew_big_unit })
}

fn bubble(
    relative: &RelativeSpan,
    nudge: &Nudge,
    smallest: Unit,
    largest: Unit,
) -> Result<Span, Error> {
    let smallest = smallest.max(Unit::Day);
    let mut balanced = nudge.span;
    let sign = balanced.get_sign_ranged();
    let mut unit = smallest;
    while let Some(u) = unit.next() {
        unit = u;
        if unit > largest {
            break;
        }
        if unit == Unit::Week && largest != Unit::Week {
            continue;
        }

        let span_start = balanced.without_lower(unit);
        let new_units = span_start
            .get_units_ranged(unit)
            .try_checked_add("bubble-units", sign)
            .with_context(|| {
                err!(
                    "failed to add sign {sign} to {unit} value {value}",
                    unit = unit.plural(),
                    value = span_start.get_units_ranged(unit),
                )
            })?;
        let span_end = span_start
            .try_units_ranged(unit, new_units)
            .with_context(|| {
                err!(
                    "failed to set {unit} to value \
                     {new_units} on span {span_start}",
                    unit = unit.plural(),
                )
            })?;
        let threshold = match relative.range {
            RelativeRange::Civil { ref start, .. } => {
                start.checked_add(span_end)?.instant
            }
            RelativeRange::Zoned { ref start, .. } => {
                start.checked_add(span_end)?.zoned.to_instant()
            }
        };
        let beyond =
            nudge.rounded_relative_end - threshold.as_nanosecond_ranged();
        if beyond == 0 || beyond.signum() == sign {
            balanced = span_end;
        } else {
            break;
        }
    }
    Ok(balanced)
}

pub(crate) fn clamp_relative_span(
    span: &Span,
    relative: &RelativeCow<'_>,
    unit: Unit,
    amount: NoUnits,
) -> Result<(NoUnits128, NoUnits128), Error> {
    let amount = span
        .get_units_ranged(unit)
        .try_checked_add("clamp-units", amount)
        .with_context(|| {
            err!(
                "failed to add {amount} to {unit} \
                 value {value} on span {span}",
                unit = unit.plural(),
                value = span.get_units_ranged(unit),
            )
        })?;
    let span_amount =
        span.try_units_ranged(unit, amount).with_context(|| {
            err!(
                "failed to set {unit} unit to {amount} on span {span}",
                unit = unit.plural(),
            )
        })?;
    let relative0 = relative.checked_add(*span)?.to_nanosecond();
    let relative1 = relative.checked_add(span_amount)?.to_nanosecond();
    Ok((relative0, relative1))
}

#[cfg(test)]
mod tests {
    use super::*;

    // Some ad hoc tests I wrote while writing the rounding increment code.
    #[test]
    fn round_to_increment_half_expand_ad_hoc() {
        let round = |quantity: i64, increment: i64| -> i64 {
            let quantity = NoUnits::new(quantity).unwrap();
            let increment = NoUnits::new(increment).unwrap();
            i64::from(RoundMode::HalfExpand.round(quantity, increment))
        };
        assert_eq!(26, round(20, 13));

        assert_eq!(0, round(29, 60));
        assert_eq!(60, round(30, 60));
        assert_eq!(60, round(31, 60));

        assert_eq!(0, round(3, 7));
        assert_eq!(7, round(4, 7));
    }

    // The Temporal tests are inspired by the table from here:
    // https://tc39.es/proposal-temporal/#sec-temporal-roundnumbertoincrement
    //
    // The main difference is that our rounding function specifically does not
    // use floating point, so we tweak the values a bit.

    #[test]
    fn round_to_increment_temporal_table_ceil() {
        let round = |quantity: i64, increment: i64| -> i64 {
            let quantity = NoUnits::new(quantity).unwrap();
            let increment = NoUnits::new(increment).unwrap();
            RoundMode::Ceil.round(quantity, increment).into()
        };
        assert_eq!(-10, round(-15, 10));
        assert_eq!(0, round(-5, 10));
        assert_eq!(10, round(4, 10));
        assert_eq!(10, round(5, 10));
        assert_eq!(10, round(6, 10));
        assert_eq!(20, round(15, 10));
    }

    #[test]
    fn round_to_increment_temporal_table_floor() {
        let round = |quantity: i64, increment: i64| -> i64 {
            let quantity = NoUnits::new(quantity).unwrap();
            let increment = NoUnits::new(increment).unwrap();
            RoundMode::Floor.round(quantity, increment).into()
        };
        assert_eq!(-20, round(-15, 10));
        assert_eq!(-10, round(-5, 10));
        assert_eq!(0, round(4, 10));
        assert_eq!(0, round(5, 10));
        assert_eq!(0, round(6, 10));
        assert_eq!(10, round(15, 10));
    }

    #[test]
    fn round_to_increment_temporal_table_expand() {
        let round = |quantity: i64, increment: i64| -> i64 {
            let quantity = NoUnits::new(quantity).unwrap();
            let increment = NoUnits::new(increment).unwrap();
            RoundMode::Expand.round(quantity, increment).into()
        };
        assert_eq!(-20, round(-15, 10));
        assert_eq!(-10, round(-5, 10));
        assert_eq!(10, round(4, 10));
        assert_eq!(10, round(5, 10));
        assert_eq!(10, round(6, 10));
        assert_eq!(20, round(15, 10));
    }

    #[test]
    fn round_to_increment_temporal_table_trunc() {
        let round = |quantity: i64, increment: i64| -> i64 {
            let quantity = NoUnits::new(quantity).unwrap();
            let increment = NoUnits::new(increment).unwrap();
            RoundMode::Trunc.round(quantity, increment).into()
        };
        assert_eq!(-10, round(-15, 10));
        assert_eq!(0, round(-5, 10));
        assert_eq!(0, round(4, 10));
        assert_eq!(0, round(5, 10));
        assert_eq!(0, round(6, 10));
        assert_eq!(10, round(15, 10));
    }

    #[test]
    fn round_to_increment_temporal_table_half_ceil() {
        let round = |quantity: i64, increment: i64| -> i64 {
            let quantity = NoUnits::new(quantity).unwrap();
            let increment = NoUnits::new(increment).unwrap();
            RoundMode::HalfCeil.round(quantity, increment).into()
        };
        assert_eq!(-10, round(-15, 10));
        assert_eq!(0, round(-5, 10));
        assert_eq!(0, round(4, 10));
        assert_eq!(10, round(5, 10));
        assert_eq!(10, round(6, 10));
        assert_eq!(20, round(15, 10));
    }

    #[test]
    fn round_to_increment_temporal_table_half_floor() {
        let round = |quantity: i64, increment: i64| -> i64 {
            let quantity = NoUnits::new(quantity).unwrap();
            let increment = NoUnits::new(increment).unwrap();
            RoundMode::HalfFloor.round(quantity, increment).into()
        };
        assert_eq!(-20, round(-15, 10));
        assert_eq!(-10, round(-5, 10));
        assert_eq!(0, round(4, 10));
        assert_eq!(0, round(5, 10));
        assert_eq!(10, round(6, 10));
        assert_eq!(10, round(15, 10));
    }

    #[test]
    fn round_to_increment_temporal_table_half_expand() {
        let round = |quantity: i64, increment: i64| -> i64 {
            let quantity = NoUnits::new(quantity).unwrap();
            let increment = NoUnits::new(increment).unwrap();
            RoundMode::HalfExpand.round(quantity, increment).into()
        };
        assert_eq!(-20, round(-15, 10));
        assert_eq!(-10, round(-5, 10));
        assert_eq!(0, round(4, 10));
        assert_eq!(10, round(5, 10));
        assert_eq!(10, round(6, 10));
        assert_eq!(20, round(15, 10));
    }

    #[test]
    fn round_to_increment_temporal_table_half_trunc() {
        let round = |quantity: i64, increment: i64| -> i64 {
            let quantity = NoUnits::new(quantity).unwrap();
            let increment = NoUnits::new(increment).unwrap();
            RoundMode::HalfTrunc.round(quantity, increment).into()
        };
        assert_eq!(-10, round(-15, 10));
        assert_eq!(0, round(-5, 10));
        assert_eq!(0, round(4, 10));
        assert_eq!(0, round(5, 10));
        assert_eq!(10, round(6, 10));
        assert_eq!(10, round(15, 10));
    }

    #[test]
    fn round_to_increment_temporal_table_half_even() {
        let round = |quantity: i64, increment: i64| -> i64 {
            let quantity = NoUnits::new(quantity).unwrap();
            let increment = NoUnits::new(increment).unwrap();
            RoundMode::HalfEven.round(quantity, increment).into()
        };
        assert_eq!(-20, round(-15, 10));
        assert_eq!(0, round(-5, 10));
        assert_eq!(0, round(4, 10));
        assert_eq!(0, round(5, 10));
        assert_eq!(10, round(6, 10));
        assert_eq!(20, round(15, 10));
    }
}
