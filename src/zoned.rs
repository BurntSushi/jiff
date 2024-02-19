use crate::{
    civil::{DateTime, Time},
    error::{err, Error, ErrorContext},
    instant::{Instant, TimeScale, Unix},
    round::{Round, Unit},
    span::Span,
    tz::{Offset, TimeZone},
    util::{
        rangeint::{RFrom, RInto, TryRFrom},
        t::{self, NoUnits, NoUnits128, ZonedDayNanoseconds, C},
    },
};

// BREADCRUMBS: Filling out the rest of the methods on Zoned doesn't look like
// it's too tricky. The only interesting one beyond what we've already built
// is `Zoned::round`. And in particular, we need `Instant::round` too. I wonder
// if that's just going to be the same as `DateTime::round`?
//
// The real trickiness comes with rounding `Span` values relative to a `Zoned`
// instant.
//
// Do Instant::round next.

#[derive(Clone)]
pub struct Zoned<S: TimeScale = Unix> {
    instant: Instant<S>,
    tz: TimeZone,
}

impl Zoned {
    pub const UNIX_EPOCH: Zoned =
        Zoned::new(Instant::UNIX_EPOCH, TimeZone::UTC);

    #[cfg(feature = "std")]
    #[inline]
    pub fn now() -> Zoned {
        Zoned::now_with_scale().expect("system time reports valid value")
    }
}

impl<S: TimeScale> Zoned<S> {
    #[inline]
    pub const fn new(instant: Instant<S>, tz: TimeZone) -> Zoned<S> {
        Zoned { instant, tz }
    }

    #[inline]
    pub fn time_zone(&self) -> &TimeZone {
        &self.tz
    }

    #[inline]
    pub fn to_instant(&self) -> Instant<S> {
        self.instant
    }

    #[inline]
    pub fn to_datetime(&self) -> DateTime {
        self.time_zone().to_datetime(self.to_instant())
    }

    #[inline]
    pub fn with_instant(&self, instant: Instant<S>) -> Zoned<S> {
        Zoned::new(instant, self.time_zone().clone())
    }

    #[inline]
    pub fn with_time_zone(&self, time_zone: TimeZone) -> Zoned<S> {
        Zoned::new(self.to_instant(), time_zone)
    }

    #[inline]
    pub fn since(&self, other: &Zoned<S>) -> Span {
        self.until(other).negate()
    }

    #[inline]
    pub(crate) fn since_with_largest_unit(
        &self,
        largest: Unit,
        mut other: &Zoned<S>,
    ) -> Result<Span, Error> {
        Ok(-self.until_with_largest_unit(largest, other)?)
    }

    #[inline]
    pub fn until(&self, other: &Zoned<S>) -> Span {
        self.until_with_largest_unit(Unit::Hour, other).expect("always okay")
        // self.to_instant().until(other.to_instant())
    }

    #[inline]
    pub(crate) fn until_with_largest_unit(
        &self,
        largest: Unit,
        mut other: &Zoned<S>,
    ) -> Result<Span, Error> {
        use crate::instant::private::Nanoseconds;

        let (zdt1, zdt2) = (self, other);

        // FIXME: Turn this into an error. And iron out time zone equality
        // story.
        assert_eq!(zdt1.time_zone(), zdt2.time_zone());

        let sign = t::sign(zdt2, zdt1);
        if sign == 0 {
            return Ok(Span::new());
        }
        if largest < Unit::Day {
            return zdt1
                .to_instant()
                .until_with_largest_unit(largest, zdt2.to_instant());
        }

        let (dt1, mut dt2) = (zdt1.to_datetime(), zdt2.to_datetime());

        let mut day_correct: t::SpanDays = C(0).rinto();
        if -sign == dt1.time().until_nanoseconds(dt2.time()).signum() {
            day_correct += C(1);
        }

        let mut mid = dt2
            .date()
            .checked_add(Span::new().days_ranged(day_correct * -sign))
            .with_context(|| {
                err!(
                    "failed to add {days} days to date in {dt2}",
                    days = day_correct * -sign,
                )
            })?
            .to_datetime(dt1.time());
        let mut zmid: Zoned<S> = mid
            .to_zoned_with(self.time_zone().clone())
            .with_context(|| {
            err!(
                "failed to convert intermediate datetime {mid} \
                 to zoned instant in time zone {tz}",
                tz = self.time_zone().name(),
            )
        })?;
        if t::sign(zdt2, &zmid) == -sign {
            if sign == -1 {
                panic!("this should be an error");
            }
            day_correct += C(1);
            mid = dt2
                .date()
                .checked_add(Span::new().days_ranged(day_correct * -sign))
                .with_context(|| {
                    err!(
                        "failed to add {days} days to date in {dt2}",
                        days = day_correct * -sign,
                    )
                })?
                .to_datetime(dt1.time());
            zmid = mid.to_zoned_with(self.time_zone().clone()).with_context(
                || {
                    err!(
                        "failed to convert intermediate datetime {mid} \
                         to zoned instant in time zone {tz}",
                        tz = self.time_zone().name(),
                    )
                },
            )?;
            if t::sign(zdt2, &zmid) == -sign {
                panic!("this should be an error too");
            }
        }
        let remainder_nano =
            zdt2.to_instant().as_nanosecond_ranged().to_no_units()
                - zmid.to_instant().as_nanosecond_ranged().to_no_units();
        dt2 = mid;

        let date_span =
            dt1.date().until_with_largest_unit(largest, dt2.date());
        Ok(Span::from_invariant_nanoseconds(Unit::Hour, remainder_nano)
            .expect("difference between time always fits in span")
            .years_ranged(date_span.get_years_ranged())
            .months_ranged(date_span.get_months_ranged())
            .weeks_ranged(date_span.get_weeks_ranged())
            .days_ranged(date_span.get_days_ranged()))
    }

    /// # Example
    ///
    /// ```
    /// use jiff::{civil::DateTime, ToSpan, Zoned};
    ///
    /// let dt = DateTime::constant(2024, 3, 10, 0, 0, 0, 0);
    /// let inst: Zoned = dt.to_zoned("America/New_York")?;
    ///
    /// let later_day = inst.checked_add(1.day())?;
    /// assert_eq!(
    ///     later_day.to_datetime(),
    ///     DateTime::constant(2024, 3, 11, 0, 0, 0, 0),
    /// );
    ///
    /// let later_hours = inst.checked_add(24.hours())?;
    /// assert_eq!(
    ///     later_hours.to_datetime(),
    ///     DateTime::constant(2024, 3, 11, 1, 0, 0, 0),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn checked_add(&self, span: Span) -> Result<Zoned<S>, Error> {
        let span_calendar = span.without_lower(Unit::Day);
        // If our duration only consists of "time" (hours, minutes, etc), then
        // we can short-circuit and do timestamp math. This also avoids dealing
        // with ambiguity and time zone bullshit.
        if span_calendar.is_zero() {
            return Ok(self.with_instant(
                self.to_instant().checked_add(span).with_context(|| {
                    err!(
                        "failed to add span {span} to instant {instant} \
                         from zoned instant {zoned}",
                        instant = self.to_instant(),
                        zoned = self,
                    )
                })?,
            ));
        }
        let span_time = span.only_lower(Unit::Day);
        let dt = self.to_datetime().checked_add(span_calendar).with_context(
            || {
                err!(
                    "failed to add span {span_calendar} to datetime {dt} \
                     from zoned instant {zoned}",
                    dt = self.to_datetime(),
                    zoned = self,
                )
            },
        )?;
        let instant =
            self.time_zone().to_instant_with_scale(dt).with_context(|| {
                err!(
                    "failed to convert civil datetime {dt} to instant \
                     with time zone {tz}",
                    tz = self.time_zone().name(),
                )
            })?;
        let instant = instant.checked_add(span_time).with_context(|| {
            err!("failed to add span {span_time} to instant {instant}")
        })?;
        Ok(self.with_instant(instant))
    }

    #[inline]
    pub fn checked_sub(&self, span: Span) -> Result<Zoned<S>, Error> {
        self.checked_add(span.negate())
    }

    /// # Example
    ///
    /// ```
    /// use jiff::{civil::DateTime, Zoned};
    ///
    /// let dt = DateTime::constant(2015, 10, 18, 12, 0, 0, 0);
    /// let inst: Zoned = dt.to_zoned("America/Sao_Paulo")?;
    /// assert_eq!(
    ///     inst.start_of_day()?.to_datetime(),
    ///     DateTime::constant(2015, 10, 18, 1, 0, 0, 0),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// ```
    /// use jiff::{civil::DateTime, tz::{TimeZone, Offset}, Zoned};
    ///
    /// // While -9999-01-03T04:00:00+25:59:59 is representable as a Zoned
    /// // value, the start of the corresponding day is not!
    /// let dt = DateTime::constant(-9999, 1, 3, 4, 0, 0, 0);
    /// let inst: Zoned = dt.to_zoned_with(TimeZone::fixed(Offset::MAX))?;
    /// assert!(inst.start_of_day().is_err());
    /// // The next day works fine since -9999-01-04T00:00:00+25:59:59 is
    /// // representable.
    /// let dt = DateTime::constant(-9999, 1, 4, 15, 0, 0, 0);
    /// let inst: Zoned = dt.to_zoned_with(TimeZone::fixed(Offset::MAX))?;
    /// assert_eq!(
    ///     inst.start_of_day()?.to_datetime(),
    ///     DateTime::constant(-9999, 1, 4, 0, 0, 0, 0),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn start_of_day(&self) -> Result<Zoned<S>, Error> {
        let civil_start = self.to_datetime().map_time(|_| Time::midnight());
        let instant = self.time_zone().to_instant_with_scale(civil_start)?;
        Ok(self.with_instant(instant))
    }

    /// # Example
    ///
    /// ```
    /// use jiff::{civil::DateTime, round::{RoundMode, Unit}, Zoned};
    ///
    /// let dt = DateTime::constant(1995, 12, 7, 3, 24, 30, 3500);
    /// let inst: Zoned = dt.to_zoned("America/Los_Angeles")?;
    ///
    /// let rounded = inst.round(Unit::Hour);
    /// assert_eq!(
    ///     rounded.to_datetime(),
    ///     DateTime::constant(1995, 12, 7, 3, 0, 0, 0),
    /// );
    ///
    /// let rounded = inst.round(Unit::Minute.increment(30));
    /// assert_eq!(
    ///     rounded.to_datetime(),
    ///     DateTime::constant(1995, 12, 7, 3, 30, 0, 0),
    /// );
    ///
    /// let rounded = inst.round(
    ///     Unit::Minute.increment(30).mode(RoundMode::Floor),
    /// );
    /// assert_eq!(
    ///     rounded.to_datetime(),
    ///     DateTime::constant(1995, 12, 7, 3, 0, 0, 0),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn round(&self, options: impl Into<Round>) -> Zoned<S> {
        self.try_round(options).expect("invalid round options")
    }

    #[inline]
    pub fn try_round(
        &self,
        options: impl Into<Round>,
    ) -> Result<Zoned<S>, Error> {
        let options = options.into();
        let day_length = self.day_length_ranged()?;
        let start = self.to_datetime();
        let end = options.round_datetime(Some(day_length), start)?;
        end.to_zoned_with(self.time_zone().clone())
    }

    #[inline]
    pub(crate) fn day_length_ranged(
        &self,
    ) -> Result<ZonedDayNanoseconds, Error> {
        let start = self.start_of_day()?;
        let end = start.checked_add(Span::new().days_ranged(C(1)))?;
        let len = start.to_instant().until(end.to_instant());
        let seconds = t::ZonedDaySeconds::try_rfrom(
            "seconds-per-zoned-day",
            len.get_seconds_ranged(),
        )
        .with_context(|| {
            err!(
                "failed to convert span between {start} until {end} \
                 to seconds",
            )
        })?;
        let nanos = seconds * t::NANOS_PER_SECOND;
        ZonedDayNanoseconds::try_rfrom("nanoseconds-per-zoned-day", nanos)
            .with_context(|| {
                err!(
                    "failed to convert span between {start} until {end} \
                 to nanoseconds",
                )
            })
    }

    #[inline]
    pub fn to_unix_scale(&self) -> Zoned {
        let instant = self.to_instant().to_unix_scale();
        Zoned::new(instant, self.time_zone().clone())
    }
}

impl<S: TimeScale> Zoned<S> {
    #[cfg(feature = "std")]
    #[inline]
    pub fn now_with_scale() -> Result<Zoned<S>, Error> {
        // TODO: We should use the local time zone.
        Ok(Zoned::new(Instant::now_with_scale()?, TimeZone::UTC))
    }

    #[inline]
    pub(crate) fn from_offset_timezone(
        dt: DateTime,
        offset: Option<Offset>,
        time_zone: Option<TimeZone>,
    ) -> Result<Zoned<S>, Error> {
        todo!()
    }
}

impl<S: TimeScale> Default for Zoned<S> {
    #[inline]
    fn default() -> Zoned<S> {
        Zoned::new(Instant::default(), TimeZone::UTC)
    }
}

impl<S> core::fmt::Debug for Zoned<S>
where
    S: TimeScale + core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("Zoned")
            .field("instant", &self.to_instant())
            .field("time_zone", &self.time_zone().name())
            .finish()
    }
}

impl<S: TimeScale> core::fmt::Display for Zoned<S> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        use crate::format::{temporal::DateTimePrinter, FmtWrite};

        static P: DateTimePrinter = DateTimePrinter::new();
        // Printing to `f` should never fail.
        Ok(P.print_zoned(self, FmtWrite(f)).unwrap())
    }
}

impl<S: TimeScale> Eq for Zoned<S> {}

impl<S: TimeScale> PartialEq for Zoned<S> {
    #[inline]
    fn eq(&self, rhs: &Zoned<S>) -> bool {
        self.to_instant().eq(&rhs.to_instant())
    }
}

impl<S: TimeScale> Ord for Zoned<S> {
    #[inline]
    fn cmp(&self, rhs: &Zoned<S>) -> core::cmp::Ordering {
        self.to_instant().cmp(&rhs.to_instant())
    }
}

impl<S: TimeScale> PartialOrd for Zoned<S> {
    #[inline]
    fn partial_cmp(&self, rhs: &Zoned<S>) -> Option<core::cmp::Ordering> {
        Some(self.cmp(rhs))
    }
}

#[cfg(feature = "std")]
impl<S: TimeScale> TryFrom<std::time::SystemTime> for Zoned<S> {
    type Error = Error;

    #[inline]
    fn try_from(
        system_time: std::time::SystemTime,
    ) -> Result<Zoned<S>, Error> {
        let instant = Instant::try_from(system_time)?;
        Ok(Zoned::new(instant, TimeZone::UTC))
    }
}

#[cfg(feature = "std")]
impl<S: TimeScale> From<Zoned<S>> for std::time::SystemTime {
    #[inline]
    fn from(time: Zoned<S>) -> std::time::SystemTime {
        time.to_instant().into()
    }
}

#[cfg(test)]
impl<S: TimeScale + 'static> quickcheck::Arbitrary for Zoned<S> {
    fn arbitrary(g: &mut quickcheck::Gen) -> Zoned<S> {
        use quickcheck::Arbitrary;

        let instant = Instant::arbitrary(g);
        let tz = TimeZone::UTC; // TODO: do something better here?
        Zoned::new(instant, tz)
    }

    fn shrink(&self) -> alloc::boxed::Box<dyn Iterator<Item = Self>> {
        let instant = self.to_instant();
        alloc::boxed::Box::new(
            instant.shrink().map(|instant| Zoned::new(instant, TimeZone::UTC)),
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::ToSpan;

    use super::*;

    #[test]
    fn until_with_largest_unit() {
        let zdt1: Zoned = DateTime::constant(1995, 12, 7, 3, 24, 30, 3500)
            .to_zoned("Asia/Kolkata")
            .unwrap();
        let zdt2: Zoned = DateTime::constant(2019, 1, 31, 15, 30, 0, 0)
            .to_zoned("Asia/Kolkata")
            .unwrap();
        let span = zdt1.until(&zdt2);
        assert_eq!(
            span,
            202956
                .hours()
                .minutes(5)
                .seconds(29)
                .milliseconds(999)
                .microseconds(996)
                .nanoseconds(500)
        );
        let span = zdt1.until_with_largest_unit(Unit::Year, &zdt2).unwrap();
        assert_eq!(
            span,
            23.years()
                .months(1)
                .days(24)
                .hours(12)
                .minutes(5)
                .seconds(29)
                .milliseconds(999)
                .microseconds(996)
                .nanoseconds(500)
        );

        let span = zdt2.until_with_largest_unit(Unit::Year, &zdt1).unwrap();
        assert_eq!(
            span,
            -23.years()
                .months(1)
                .days(24)
                .hours(12)
                .minutes(5)
                .seconds(29)
                .milliseconds(999)
                .microseconds(996)
                .nanoseconds(500)
        );
        let span =
            zdt1.until_with_largest_unit(Unit::Nanosecond, &zdt2).unwrap();
        assert_eq!(span, 730641929999996500i64.nanoseconds(),);

        let zdt1: Zoned = DateTime::constant(2020, 1, 1, 0, 0, 0, 0)
            .to_zoned("America/New_York")
            .unwrap();
        let zdt2: Zoned = DateTime::constant(2020, 4, 24, 21, 0, 0, 0)
            .to_zoned("America/New_York")
            .unwrap();
        let span = zdt1.until(&zdt2);
        assert_eq!(span, 2756.hours());
        let span = zdt1.until_with_largest_unit(Unit::Year, &zdt2).unwrap();
        assert_eq!(span, 3.months().days(23).hours(21));

        let zdt1: Zoned = DateTime::constant(2000, 10, 29, 0, 0, 0, 0)
            .to_zoned("America/Vancouver")
            .unwrap();
        let zdt2: Zoned = DateTime::constant(2000, 10, 29, 23, 0, 0, 5)
            .to_zoned("America/Vancouver")
            .unwrap();
        let span = zdt1.until_with_largest_unit(Unit::Day, &zdt2).unwrap();
        assert_eq!(span, 24.hours().nanoseconds(5));
    }

    #[test]
    fn zoned_size() {
        #[cfg(debug_assertions)]
        {
            assert_eq!(48, core::mem::size_of::<Zoned>());
        }
        #[cfg(not(debug_assertions))]
        {
            assert_eq!(24, core::mem::size_of::<Zoned>());
        }
    }
}
