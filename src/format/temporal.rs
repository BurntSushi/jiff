/*!
A hybrid format derived from [RFC 3339], [RFC 9557] and [ISO 8601].

Specifically, this format comes from the [Temporal ISO 8601 grammar].

# Differences with Temporal

Jiff implements Temporal's grammar pretty closely, but there are a few
differences at the time of writing:

* The sign for a UTC offset or a datetime as a whole must be expressed with the
ASCII symbol `+` or `-`. Temporal also supports using a non-ASCII minute sign
`−` (`U+2212`). Support for this could be added to Jiff pretty easily. There is
no specific reason why Jiff doesn't support it, other than me not quite
understanding how useful it is. Please open an issue if you need it.
* The maximum UTC offset value expressible is `25:59:59` in Jiff, where as in
Temporal it's `23:59:59.999999999`. Jiff supports a slightly bigger maximum
to account for all valid values of POSIX time zone strings. Jiff also lacks
nanosecond precision for UTC offsets, as it's not clear how useful that is in
practice.

There is some more [background on Temporal's format] available.

[Temporal ISO 8601 grammar]: https://tc39.es/proposal-temporal/#sec-temporal-iso8601grammar
[RFC 3339]: https://www.rfc-editor.org/rfc/rfc3339
[RFC 9557]: https://www.rfc-editor.org/rfc/rfc9557.html
[ISO 8601]: https://www.iso.org/iso-8601-date-and-time-format.html
[background on Temporal's format]: https://github.com/tc39/proposal-temporal/issues/2843
*/

use crate::{
    civil::{Date, DateTime, Time},
    error::{err, Error, ErrorContext},
    format::{
        offset::{self, ParsedOffset},
        rfc9557::{self, ParsedAnnotations},
        util::DecimalFormatter,
        Parsed, Write, WriteExt,
    },
    tz::{
        AmbiguousInstant, AmbiguousInstantKind, Offset, TimeZone,
        TimeZoneDatabase,
    },
    util::{escape, parse, t},
    Instant, TimeScale, Zoned,
};

// BREADCRUMBS:
//
// * Audit how Temporal deals with conflicts between offsets and time zone
// names. I think we'll need an option on the datetime parser below. Although,
// it might actually be an input to a method on `ParsedDateTime`.
// * Implement duration printing and parsing. Probably just in this module,
// emulating Temporal.
// * Add `Display` and `Debug` impls for primary types.
// * Add `FromStr` impls.
// * Probably skip on exposing the `format` module. Delete the traits. Skip on
// `strftime` and `strptime` for now.
// * Clean up, tighten and document the `format` module. (For "internal" level
// quality docs.)
// * Straighten out the span/round/whatever stuff. We probably want some
// concrete target types as inputs to things like `since`/`until`. And this
// should include parsing. Do we want a separate sub-module for these types?
// Maybe `jiff::args`? Or can we squeeze them into `jiff::span`? Hmmmm.

/// The datetime components parsed from a string.
#[derive(Debug)]
pub(crate) struct ParsedDateTime<'i> {
    /// The original input that the datetime was parsed from.
    input: escape::Bytes<'i>,
    /// An optional civil date.
    date: ParsedDate<'i>,
    /// An optional civil time.
    time: Option<ParsedTime<'i>>,
    /// An optional UTC offset.
    offset: Option<ParsedOffset<'i>>,
    /// An optional RFC 9557 annotations parsed.
    ///
    /// An empty `ParsedAnnotations` is valid and possible, so this bakes
    /// optionality into the type and doesn't need to be an `Option` itself.
    annotations: ParsedAnnotations<'i>,
}

impl<'i> ParsedDateTime<'i> {
    pub(crate) fn to_zoned<S: TimeScale>(
        &self,
        db: &TimeZoneDatabase,
        resolve_offset_conflict: ResolveOffsetConflict,
        disambiguation: Disambiguation,
    ) -> Result<Zoned<S>, Error> {
        let amb = self.to_ambiguous_instant(db, resolve_offset_conflict)?;
        disambiguation.disambiguate(amb)
    }

    pub(crate) fn to_ambiguous_instant(
        &self,
        db: &TimeZoneDatabase,
        resolve_offset_conflict: ResolveOffsetConflict,
    ) -> Result<AmbiguousInstant, Error> {
        let time = self.time.as_ref().map(|p| p.time).ok_or_else(|| {
            err!(
                "failed to find time component in {:?}, \
                 which is required for parsing a zoned instant",
                self.input,
            )
        })?;
        let dt = DateTime::from_parts(self.date.date, time);

        // We always require a time zone when parsing a zoned instant.
        let tz = self.annotations.to_time_zone(db)?.ok_or_else(|| {
            err!(
                "failed to find time zone in square brackets \
                 in {:?}, which is required for parsing a zoned instant",
                self.input,
            )
        })?;

        // If there's no offset, then our only choice, regardless of conflict
        // resolution preference, is to use the time zone. That is, there is no
        // possible conflict.
        let Some(ref parsed_offset) = self.offset else {
            return Ok(tz.to_ambiguous_instant(dt));
        };
        let offset = parsed_offset.to_offset()?;
        resolve_offset_conflict.resolve(dt, offset, &tz).with_context(|| {
            err!("parsing {input:?} failed", input = self.input)
        })
    }

    pub(crate) fn to_instant<S: TimeScale>(
        &self,
    ) -> Result<Instant<S>, Error> {
        let time = self.time.as_ref().map(|p| p.time).ok_or_else(|| {
            err!(
                "failed to find time component in {:?}, \
                 which is required for parsing an instant",
                self.input,
            )
        })?;
        let parsed_offset = self.offset.as_ref().ok_or_else(|| {
            err!(
                "failed to find offset component in {:?}, \
                 which is required for parsing a zoned instant",
                self.input,
            )
        })?;
        let offset = parsed_offset.to_offset()?;
        let dt = DateTime::from_parts(self.date.date, time);
        let instant = offset.to_instant_with_scale(dt).with_context(|| {
            err!(
                "failed to convert civil datetime to instant \
                 with offset {offset}",
            )
        })?;
        Ok(instant)
    }

    pub(crate) fn to_datetime(&self) -> Result<DateTime, Error> {
        if self.offset.as_ref().map_or(false, |o| o.is_zulu()) {
            return Err(err!(
                "cannot parse civil date from string with a Zulu \
                 offset, parse as an instant and convert to a civil \
                 date instead",
            ));
        }
        Ok(DateTime::from_parts(self.date.date, self.time()))
    }

    pub(crate) fn to_date(&self) -> Result<Date, Error> {
        if self.offset.as_ref().map_or(false, |o| o.is_zulu()) {
            return Err(err!(
                "cannot parse civil date from string with a Zulu \
                 offset, parse as an instant and convert to a civil \
                 date instead",
            ));
        }
        Ok(self.date.date)
    }

    fn time(&self) -> Time {
        self.time.as_ref().map(|p| p.time).unwrap_or(Time::midnight())
    }
}

impl<'i> core::fmt::Display for ParsedDateTime<'i> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        core::fmt::Display::fmt(&self.input, f)
    }
}

/// The result of parsing a Gregorian calendar civil date.
#[derive(Debug)]
pub(crate) struct ParsedDate<'i> {
    /// The original input that the date was parsed from.
    input: escape::Bytes<'i>,
    /// The actual parsed date.
    date: Date,
}

/// The result of parsing a 24-hour civil time.
#[derive(Debug)]
pub(crate) struct ParsedTime<'i> {
    /// The original input that the time was parsed from.
    input: escape::Bytes<'i>,
    /// The actual parsed time.
    time: Time,
    /// Whether the time was parsed in extended format or not.
    extended: bool,
}

/// How to resolve conflicts between the offset and time zone.
#[derive(Clone, Copy, Debug)]
pub(crate) enum ResolveOffsetConflict {
    AlwaysOffset,
    AlwaysTimeZone,
    PreferOffset,
    Reject,
}

impl ResolveOffsetConflict {
    // TODO: We should figure out how to expose this in the public API so that
    // callers can make use of it without going through parsing. (Which would
    // also only limit it to IANA time zones.)
    //
    // I think this is just mostly a matter of figuring out where
    // `ResolveOffsetConflict` should live. Probably in the `tz` sub-module.
    fn resolve(
        self,
        dt: DateTime,
        offset: Offset,
        tz: &TimeZone,
    ) -> Result<AmbiguousInstant, Error> {
        match self {
            // In this case, we ignore any TZ annotation (although still
            // require that it exists) and always use the provided offset.
            ResolveOffsetConflict::AlwaysOffset => {
                // FIXME: This is non-ideal, because we're creating a
                // `TimeZone` here (which is an alloc), although it's likely
                // marginal, since we've already allocated to create a
                // `TimeZone` from an annotation above.
                let tz = TimeZone::fixed(offset);
                Ok(tz.to_ambiguous_instant(dt))
            }
            // In this case, we ignore any provided offset and always use the
            // time zone annotation.
            ResolveOffsetConflict::AlwaysTimeZone => {
                Ok(tz.to_ambiguous_instant(dt))
            }
            // In this case, we use the offset if it's correct, but otherwise
            // fall back to the time zone annotation if it's not.
            ResolveOffsetConflict::PreferOffset => {
                Ok(ResolveOffsetConflict::resolve_via_prefer(dt, offset, &tz))
            }
            // In this case, if the offset isn't possible for the provided time
            // zone annotation, then we return an error.
            ResolveOffsetConflict::Reject => {
                ResolveOffsetConflict::resolve_via_reject(dt, offset, &tz)
            }
        }
    }

    /// Given a parsed datetime, a parsed offset and a parsed time zone, this
    /// attempts to resolve the datetime to a particular instant based on the
    /// 'prefer' strategy.
    ///
    /// In the 'prefer' strategy, we prefer to use the parsed offset to resolve
    /// any ambiguity in the parsed datetime and time zone, but only if the
    /// parsed offset is valid for the parsed datetime and time zone. If the
    /// parsed offset isn't valid, then it is ignored. In the case where it is
    /// ignored, it is possible for an ambiguous instant to be returned.
    fn resolve_via_prefer(
        dt: DateTime,
        given: Offset,
        tz: &TimeZone,
    ) -> AmbiguousInstant {
        use AmbiguousInstantKind::*;

        let amb = tz.to_ambiguous_instant(dt);
        match *amb.kind() {
            // Basically, if the offset parsed matches one of our ambiguous
            // offsets, then the offset is used to resolve the ambiguity and
            // yields an unambiguous result. But in every other case, the
            // offset parsed is completely ignored. (And this may result in
            // returning an ambiguous instant.)
            Gap { before, after } | Fold { before, after }
                if given == before || given == after =>
            {
                let kind = AmbiguousInstantKind::Unambiguous { offset: given };
                AmbiguousInstant::new(tz.clone(), dt, kind)
            }
            _ => amb,
        }
    }

    /// Given a parsed datetime, a parsed offset and a parsed time zone, this
    /// attempts to resolve the datetime to a particular instant based on the
    /// 'reject' strategy.
    ///
    /// That is, if the offset is not possibly valid for the given datetime and
    /// time zone, then this returns an error.
    ///
    /// This guarantees that on success, an unambiguous instant is returned.
    /// This occurs because if the datetime is ambiguous for the given time
    /// zone, then the parsed offset either matches one of the possible offsets
    /// (and thus provides an unambiguous choice), or it doesn't and an error
    /// is returned.
    fn resolve_via_reject(
        dt: DateTime,
        given: Offset,
        tz: &TimeZone,
    ) -> Result<AmbiguousInstant, Error> {
        use AmbiguousInstantKind::*;

        let amb = tz.to_ambiguous_instant(dt);
        match *amb.kind() {
            Unambiguous { offset } if given != offset => Err(err!(
                "parsed datetime {dt} could not resolve to instant since \
                 'reject' conflict resolution was chosen, and because parsed \
                 datetime has offset {given}, but the time zone {tzname} for \
                 the given datetime unambiguously has offset {offset}",
                tzname = tz.name(),
            )),
            Unambiguous { offset } => Ok(amb),
            Gap { before, after } if given != before && given != after => {
                // Temporal actually seems to report an error whenever a gap
                // is found, even if the parsed offset matches one of the two
                // offsets in the gap. I think the reasoning is because the
                // parsed offset and offsets from the gap will flip-flop, thus
                // resulting in a datetime with an offset distinct from the one
                // given. Here's an example. Consider this datetime:
                //
                //     2024-03-10T02:30-04:00[America/New_York]
                //
                // This occurs in the EST->EDT transition gap, such that
                // `02:30` never actually appears on a clock for folks in
                // `America/New_York`. The `-04` offset means that the instant
                // this corresponds to is unambiguous. Namely, it is:
                //
                //     2024-03-10T06:30Z
                //
                // This instant, when converted to `America/New_York`, is in:
                //
                //     2024-03-10T01:30-05:00[America/New_York]
                //
                // As you can see, the offset flip-flopped. The same flip-flop
                // happens the other way if you use `02:30-05:00`. Presumably,
                // Temporal errors here because the offset changes. But the
                // instant in time is the same *and* it is unambiguous. So it's
                // not clear to me why we ought to error in this case.
                //
                // Ref: https://github.com/tc39/proposal-temporal/issues/2892
                Err(err!(
                    "parsed datetime {dt} could not resolve to instant since \
                     'reject' conflict resolution was chosen, and because \
                     parsed datetime has offset {given}, but the time zone \
                     {tzname} for the given datetime falls in a gap between \
                     offsets {before} and {after}, neither of which match \
                     the parsed offset",
                    tzname = tz.name(),
                ))
            }
            Fold { before, after } if given != before && given != after => {
                Err(err!(
                    "parsed datetime {dt} could not resolve to instant since \
                     'reject' conflict resolution was chosen, and because \
                     parsed datetime has offset {given}, but the time zone \
                     {tzname} for the given datetime falls in a fold between \
                     offsets {before} and {after}, neither of which match \
                     the parsed offset",
                    tzname = tz.name(),
                ))
            }
            Gap { .. } | Fold { .. } => {
                let kind = AmbiguousInstantKind::Unambiguous { offset: given };
                Ok(AmbiguousInstant::new(tz.clone(), dt, kind))
            }
        }
    }
}

/// How to resolve ambiguous datetimes for a particular time zone.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Disambiguation {
    Compatible,
    Earlier,
    Later,
    Reject,
}

impl Disambiguation {
    fn disambiguate<S: TimeScale>(
        self,
        amb: AmbiguousInstant,
    ) -> Result<Zoned<S>, Error> {
        match self {
            Disambiguation::Compatible => amb.compatible_with_scale(),
            Disambiguation::Earlier => amb.earlier_with_scale(),
            Disambiguation::Later => amb.later_with_scale(),
            Disambiguation::Reject => amb.unambiguous_with_scale(),
        }
    }
}

/// A parser for Temporal datetimes.
#[derive(Debug)]
pub(crate) struct DateTimeParser {
    /// There are currently no configuration options for this parser.
    _priv: (),
}

impl DateTimeParser {
    /// Create a new Temporal parser with the default configuration.
    pub(crate) const fn new() -> DateTimeParser {
        DateTimeParser { _priv: () }
    }

    // TemporalDateTimeString[Zoned] :::
    //   AnnotatedDateTime[?Zoned]
    //
    // AnnotatedDateTime[Zoned] :::
    //   [~Zoned] DateTime TimeZoneAnnotation[opt] Annotations[opt]
    //   [+Zoned] DateTime TimeZoneAnnotation Annotations[opt]
    //
    // DateTime :::
    //   Date
    //   Date DateTimeSeparator TimeSpec DateTimeUTCOffset[opt]
    pub(crate) fn parse_temporal_datetime<'i>(
        &self,
        input: &'i [u8],
    ) -> Result<Parsed<'i, ParsedDateTime<'i>>, Error> {
        let mkslice = parse::slicer(input);
        let Parsed { value: date, input } = self.parse_date_spec(input)?;
        if input.is_empty() {
            let value = ParsedDateTime {
                input: escape::Bytes(mkslice(input)),
                date,
                time: None,
                offset: None,
                annotations: ParsedAnnotations::none(),
            };
            return Ok(Parsed { value, input });
        }
        let (time, offset, input) = if !matches!(input[0], b' ' | b'T' | b't')
        {
            (None, None, input)
        } else {
            let input = &input[1..];
            // If there's a separator, then we must parse a time and we are
            // *allowed* to parse an offset. But without a separator, we don't
            // support offsets. Just annotations (which are parsed below).
            let Parsed { value: time, input } = self.parse_time_spec(input)?;
            let Parsed { value: offset, input } = self.parse_offset(input)?;
            (Some(time), offset, input)
        };
        let Parsed { value: annotations, input } =
            self.parse_annotations(input)?;
        let value = ParsedDateTime {
            input: escape::Bytes(mkslice(input)),
            date,
            time,
            offset,
            annotations,
        };
        Ok(Parsed { value, input })
    }

    // TemporalTimeString :::
    //   AnnotatedTime
    //   AnnotatedDateTimeTimeRequired
    //
    // AnnotatedTime :::
    //   TimeDesignator TimeSpec
    //                  DateTimeUTCOffset[opt]
    //                  TimeZoneAnnotation[opt]
    //                  Annotations[opt]
    //   TimeSpecWithOptionalOffsetNotAmbiguous TimeZoneAnnotation[opt]
    //                                          Annotations[opt]
    //
    // TimeSpecWithOptionalOffsetNotAmbiguous :::
    //   TimeSpec DateTimeUTCOffsetopt (but not one of ValidMonthDay or DateSpecYearMonth)
    //
    // TimeDesignator ::: one of
    //   T t
    pub(crate) fn parse_temporal_time<'i>(
        &self,
        mut input: &'i [u8],
    ) -> Result<Parsed<'i, ParsedTime<'i>>, Error> {
        let mkslice = parse::slicer(input);
        let original = escape::Bytes(input);

        if input.starts_with(b"T") || input.starts_with(b"t") {
            input = &input[1..];
            let Parsed { value: time, input } = self.parse_time_spec(input)?;
            let Parsed { value: offset, input } = self.parse_offset(input)?;
            if offset.map_or(false, |o| o.is_zulu()) {
                return Err(err!(
                    "cannot parse civil time from string with a Zulu \
                     offset, parse as an instant and convert to a civil \
                     time instead",
                ));
            }
            let Parsed { value: annotations, input } =
                self.parse_annotations(input)?;
            return Ok(Parsed { value: time, input });
        }
        // We now look for a full datetime and extract the time from that.
        // We do this before looking for a non-T time-only component because
        // otherwise things like `2024-06-01T01:02:03` end up having `2024-06`
        // parsed as a `HHMM-OFFSET` time, and then result in an "ambiguous"
        // error.
        //
        // This is largely a result of us trying to parse a time off of the
        // beginning of the input without assuming that the time must consume
        // the entire input.
        if let Ok(parsed) = self.parse_temporal_datetime(input) {
            let Parsed { value: dt, input } = parsed;
            if dt.offset.map_or(false, |o| o.is_zulu()) {
                return Err(err!(
                    "cannot parse plain time from full datetime string with a \
                     Zulu offset, parse as an instant and convert to a plain \
                     time instead",
                ));
            }
            let Some(time) = dt.time else {
                return Err(err!(
                    "successfully parsed date from {parsed:?}, but \
                     no time component was found",
                    parsed = dt.input,
                ));
            };
            return Ok(Parsed { value: time, input });
        }

        // At this point, we look for something that is a time that doesn't
        // start with a `T`. We need to check that it isn't ambiguous with a
        // possible date.
        let time = self.parse_time_spec(input)?;
        let Parsed { value: time, input } = self.parse_time_spec(input)?;
        let Parsed { value: offset, input } = self.parse_offset(input)?;
        if offset.map_or(false, |o| o.is_zulu()) {
            return Err(err!(
                "cannot parse plain time from string with a Zulu \
                         offset, parse as an instant and convert to a plain \
                         time instead",
            ));
        }
        // The possible ambiguities occur with the time AND the
        // optional offset, so try to parse what we have so far as
        // either a "month-day" or a "year-month." If either succeeds,
        // then the time is ambiguous and we can report an error.
        //
        // ... but this can only happen when the time was parsed in
        // "basic" mode. i.e., without the `:` separators.
        if !time.extended {
            let possibly_ambiguous = mkslice(input);
            if self.parse_month_day(possibly_ambiguous).is_ok() {
                return Err(err!(
                    "parsed time from {parsed:?} is ambiguous \
                             with a month-day date",
                    parsed = escape::Bytes(possibly_ambiguous),
                ));
            }
            if self.parse_year_month(possibly_ambiguous).is_ok() {
                return Err(err!(
                    "parsed time from {parsed:?} is ambiguous \
                             with a year-month date",
                    parsed = escape::Bytes(possibly_ambiguous),
                ));
            }
        }
        // OK... carry on.
        let Parsed { value: annotations, input } =
            self.parse_annotations(input)?;
        Ok(Parsed { value: time, input })
    }

    // Date :::
    //   DateYear - DateMonth - DateDay
    //   DateYear DateMonth DateDay
    fn parse_date_spec<'i>(
        &self,
        input: &'i [u8],
    ) -> Result<Parsed<'i, ParsedDate<'i>>, Error> {
        let mkslice = parse::slicer(input);
        let original = escape::Bytes(input);

        // Parse year component.
        let Parsed { value: year, input } =
            self.parse_year(input).map_err(|err| {
                err.context(err!("failed to parse year in date {original:?}"))
            })?;
        let extended = input.starts_with(b"-");

        // Parse optional separator.
        let Parsed { input, .. } =
            self.parse_date_separator(input, extended).map_err(|err| {
                err.context("failed to parse separator after year")
            })?;

        // Parse month component.
        let Parsed { value: month, input } =
            self.parse_month(input).map_err(|err| {
                err.context(err!("failed to parse month in date {original:?}"))
            })?;

        // Parse optional separator.
        let Parsed { input, .. } =
            self.parse_date_separator(input, extended).map_err(|err| {
                err.context("failed to parse separator after month")
            })?;

        // Parse day component.
        let Parsed { value: day, input } =
            self.parse_day(input).map_err(|err| {
                err.context(err!("failed to parse day in date {original:?}"))
            })?;

        let date = Date::new_ranged(year, month, day).map_err(|err| {
            err!("date parsed from {original:?} is not valid: {err}")
        })?;
        let value = ParsedDate { input: escape::Bytes(mkslice(input)), date };
        Ok(Parsed { value, input })
    }

    // TimeSpec :::
    //   TimeHour
    //   TimeHour : TimeMinute
    //   TimeHour TimeMinute
    //   TimeHour : TimeMinute : TimeSecond TimeFraction[opt]
    //   TimeHour TimeMinute TimeSecond TimeFraction[opt]
    fn parse_time_spec<'i>(
        &self,
        mut input: &'i [u8],
    ) -> Result<Parsed<'i, ParsedTime<'i>>, Error> {
        let mkslice = parse::slicer(input);
        let original = escape::Bytes(input);

        // Parse hour component.
        let Parsed { value: hour, input } =
            self.parse_hour(input).map_err(|err| {
                err.context(err!("failed to parse hour in time {original:?}"))
            })?;
        let extended = input.starts_with(b":");

        // Start building up our time value.
        let mut time = Time::midnight().with_hour_ranged(hour);

        // Parse optional minute component.
        let Parsed { value: has_minute, input } =
            self.parse_time_separator(input, extended);
        if !has_minute {
            let value = ParsedTime {
                input: escape::Bytes(mkslice(input)),
                time,
                extended,
            };
            return Ok(Parsed { value, input });
        }
        let Parsed { value: minute, input } =
            self.parse_minute(input).map_err(|err| {
                err.context(err!(
                    "failed to parse minute in time {original:?}"
                ))
            })?;
        time = time.with_minute_ranged(minute);

        // Parse optional second component.
        let Parsed { value: has_second, input } =
            self.parse_time_separator(input, extended);
        if !has_second {
            let value = ParsedTime {
                input: escape::Bytes(mkslice(input)),
                time,
                extended,
            };
            return Ok(Parsed { value, input });
        }
        let Parsed { value: second, input } =
            self.parse_second(input).map_err(|err| {
                err.context(err!(
                    "failed to parse second in time {original:?}"
                ))
            })?;
        time = time.with_second_ranged(second);

        // Parse an optional fractional component.
        let Parsed { value: nanosecond, input } =
            parse_fractional_nanosecond(input).map_err(|err| {
                err.context(err!(
                    "failed to parse fractional nanoseconds \
                     in time {original:?}",
                ))
            })?;
        if let Some(nanosecond) = nanosecond {
            time = time.with_subsec_nanosecond_ranged(nanosecond);
        }

        let value = ParsedTime {
            input: escape::Bytes(mkslice(input)),
            time,
            extended,
        };
        Ok(Parsed { value, input })
    }

    // ValidMonthDay :::
    //   DateMonth -[opt] 0 NonZeroDigit
    //   DateMonth -[opt] 1 DecimalDigit
    //   DateMonth -[opt] 2 DecimalDigit
    //   DateMonth -[opt] 30 but not one of 0230 or 02-30
    //   DateMonthWithThirtyOneDays -opt 31
    //
    // DateMonthWithThirtyOneDays ::: one of
    //   01 03 05 07 08 10 12
    //
    // NOTE: Jiff doesn't have a "month-day" type, but we still have a parsing
    // function for it so that we can detect ambiguous time strings.
    fn parse_month_day<'i>(
        &self,
        input: &'i [u8],
    ) -> Result<Parsed<'i, ()>, Error> {
        let original = escape::Bytes(input);

        // Parse month component.
        let Parsed { value: month, mut input } =
            self.parse_month(input).map_err(|err| {
                err.context(err!(
                    "failed to parse month in month-day {original:?}"
                ))
            })?;

        // Skip over optional separator.
        if input.starts_with(b"-") {
            input = &input[1..];
        }

        // Parse day component.
        let Parsed { value: day, input } =
            self.parse_day(input).map_err(|err| {
                err.context(err!(
                    "failed to parse day in month-day {original:?}"
                ))
            })?;

        // Check that the month-day is valid. Since Temporal's month-day
        // permits 02-29, we use a leap year. The error message here is
        // probably confusing, but these errors should never be exposed to the
        // user.
        let year = t::Year::N::<2024>();
        let date = Date::new_ranged(year, month, day).map_err(|err| {
            err!("month-day parsed from {original:?} is not valid: {err}")
        })?;

        // We have a valid year-month. But we don't return it because we just
        // need to check validity.
        Ok(Parsed { value: (), input })
    }

    // DateSpecYearMonth :::
    //   DateYear -[opt] DateMonth
    //
    // NOTE: Jiff doesn't have a "year-month" type, but we still have a parsing
    // function for it so that we can detect ambiguous time strings.
    fn parse_year_month<'i>(
        &self,
        input: &'i [u8],
    ) -> Result<Parsed<'i, ()>, Error> {
        let original = escape::Bytes(input);

        // Parse year component.
        let Parsed { value: year, mut input } =
            self.parse_year(input).map_err(|err| {
                err.context(err!("failed to parse year in date {original:?}"))
            })?;
        let extended = input.starts_with(b"-");

        // Skip over optional separator.
        if input.starts_with(b"-") {
            input = &input[1..];
        }

        // Parse month component.
        let Parsed { value: month, mut input } =
            self.parse_month(input).map_err(|err| {
                err.context(err!(
                    "failed to parse month in month-day {original:?}"
                ))
            })?;

        // Check that the year-month is valid. We just use a day of 1, since
        // every month in every year must have a day 1.
        let day = t::Day::N::<1>();
        let date = Date::new_ranged(year, month, day).map_err(|err| {
            err!("year-month parsed from {original:?} is not valid: {err}")
        })?;

        // We have a valid year-month. But we don't return it because we just
        // need to check validity.
        Ok(Parsed { value: (), input })
    }

    // DateYear :::
    //   DecimalDigit DecimalDigit DecimalDigit DecimalDigit
    //   TemporalSign DecimalDigit DecimalDigit DecimalDigit DecimalDigit DecimalDigit DecimalDigit
    //
    // NOTE: I don't really like the fact that in order to write a negative
    // year, you need to use the six digit variant. Like, why not allow
    // `-0001`? I'm not sure why, so for Chesterton's fence reasons, I'm
    // sticking with the Temporal spec. But I may loosen this in the future. We
    // should be careful not to introduce any possible ambiguities, though, I
    // don't think there are any?
    fn parse_year<'i>(
        &self,
        input: &'i [u8],
    ) -> Result<Parsed<'i, t::Year>, Error> {
        let Parsed { value: sign, input } = self.parse_year_sign(input);
        if let Some(sign) = sign {
            let (year, input) = parse::split(input, 6).ok_or_else(|| {
                err!(
                    "expected six digit year (because of a leading sign), \
                     but found end of input",
                )
            })?;
            let year = parse::i64(year).map_err(|err| {
                err!(
                    "failed to parse {year:?} as year \
                     (a six digit integer): {err}",
                    year = escape::Bytes(year),
                )
            })?;
            let year = t::Year::try_new("year", year)
                .map_err(|err| err!("year is not valid: {err}"))?;
            Ok(Parsed { value: year * sign, input })
        } else {
            let (year, input) = parse::split(input, 4).ok_or_else(|| {
                err!(
                    "expected four digit year (or leading sign for \
                     six digit year), but found end of input",
                )
            })?;
            let year = parse::i64(year).map_err(|err| {
                err!(
                    "failed to parse {year:?} as year \
                     (a four digit integer): {err}",
                    year = escape::Bytes(year),
                )
            })?;
            let year = t::Year::try_new("year", year)
                .map_err(|err| err!("year is not valid: {err}"))?;
            Ok(Parsed { value: year, input })
        }
    }

    // DateMonth :::
    //   0 NonZeroDigit
    //   10
    //   11
    //   12
    fn parse_month<'i>(
        &self,
        input: &'i [u8],
    ) -> Result<Parsed<'i, t::Month>, Error> {
        let (month, input) = parse::split(input, 2).ok_or_else(|| {
            err!("expected two digit month, but found end of input",)
        })?;
        let month = parse::i64(month).map_err(|err| {
            err!(
                "failed to parse {month:?} as month (a two digit integer): \
                 {err}",
                month = escape::Bytes(month),
            )
        })?;
        let month = t::Month::try_new("month", month)
            .map_err(|err| err!("month is not valid: {err}"))?;
        Ok(Parsed { value: month, input })
    }

    // DateDay :::
    //   0 NonZeroDigit
    //   1 DecimalDigit
    //   2 DecimalDigit
    //   30
    //   31
    fn parse_day<'i>(
        &self,
        input: &'i [u8],
    ) -> Result<Parsed<'i, t::Day>, Error> {
        let (day, input) = parse::split(input, 2).ok_or_else(|| {
            err!("expected two digit day, but found end of input",)
        })?;
        let day = parse::i64(day).map_err(|err| {
            err!(
                "failed to parse {day:?} as day (a two digit integer): \
                 {err}",
                day = escape::Bytes(day),
            )
        })?;
        let day = t::Day::try_new("day", day)
            .map_err(|err| err!("day is not valid: {err}"))?;
        Ok(Parsed { value: day, input })
    }

    // TimeHour :::
    //   Hour
    //
    // Hour :::
    //   0 DecimalDigit
    //   1 DecimalDigit
    //   20
    //   21
    //   22
    //   23
    fn parse_hour<'i>(
        &self,
        input: &'i [u8],
    ) -> Result<Parsed<'i, t::Hour>, Error> {
        let (hour, input) = parse::split(input, 2).ok_or_else(|| {
            err!("expected two digit hour, but found end of input",)
        })?;
        let hour = parse::i64(hour).map_err(|err| {
            err!(
                "failed to parse {hour:?} as hour (a two digit integer): \
                 {err}",
                hour = escape::Bytes(hour),
            )
        })?;
        let hour = t::Hour::try_new("hour", hour)
            .map_err(|err| err!("hour is not valid: {err}"))?;
        Ok(Parsed { value: hour, input })
    }

    // TimeMinute :::
    //   MinuteSecond
    //
    // MinuteSecond :::
    //   0 DecimalDigit
    //   1 DecimalDigit
    //   2 DecimalDigit
    //   3 DecimalDigit
    //   4 DecimalDigit
    //   5 DecimalDigit
    fn parse_minute<'i>(
        &self,
        input: &'i [u8],
    ) -> Result<Parsed<'i, t::Minute>, Error> {
        let (minute, input) = parse::split(input, 2).ok_or_else(|| {
            err!("expected two digit minute, but found end of input",)
        })?;
        let minute = parse::i64(minute).map_err(|err| {
            err!(
                "failed to parse {minute:?} as minute (a two digit integer): \
                 {err}",
                minute = escape::Bytes(minute),
            )
        })?;
        let minute = t::Minute::try_new("minute", minute)
            .map_err(|err| err!("minute is not valid: {err}"))?;
        Ok(Parsed { value: minute, input })
    }

    // TimeSecond :::
    //   MinuteSecond
    //   60
    //
    // MinuteSecond :::
    //   0 DecimalDigit
    //   1 DecimalDigit
    //   2 DecimalDigit
    //   3 DecimalDigit
    //   4 DecimalDigit
    //   5 DecimalDigit
    fn parse_second<'i>(
        &self,
        input: &'i [u8],
    ) -> Result<Parsed<'i, t::UtcSecond>, Error> {
        let (second, input) = parse::split(input, 2).ok_or_else(|| {
            err!("expected two digit second, but found end of input",)
        })?;
        let second = parse::i64(second).map_err(|err| {
            err!(
                "failed to parse {second:?} as second (a two digit integer): \
                 {err}",
                second = escape::Bytes(second),
            )
        })?;
        let second = t::UtcSecond::try_new("second", second)
            .map_err(|err| err!("second is not valid: {err}"))?;
        Ok(Parsed { value: second, input })
    }

    fn parse_offset<'i>(
        &self,
        input: &'i [u8],
    ) -> Result<Parsed<'i, Option<ParsedOffset<'i>>>, Error> {
        const P: offset::Parser =
            offset::Parser::new().zulu(true).subminute(true);
        P.parse_optional(input)
    }

    fn parse_annotations<'i>(
        &self,
        input: &'i [u8],
    ) -> Result<Parsed<'i, ParsedAnnotations<'i>>, Error> {
        const P: rfc9557::Parser = rfc9557::Parser::new();
        P.parse(input)
    }

    /// Parses the separator that is expected to appear between
    /// date components.
    ///
    /// When in extended mode, a `-` is expected. When not in extended mode,
    /// no input is consumed and this routine never fails.
    fn parse_date_separator<'i>(
        &self,
        mut input: &'i [u8],
        extended: bool,
    ) -> Result<Parsed<'i, ()>, Error> {
        if !extended {
            // If we see a '-' when not in extended mode, then we can report
            // a better error message than, e.g., "-3 isn't a valid day."
            if input.starts_with(b"-") {
                return Err(err!(
                    "expected no separator after month since none was \
                     found after the year, but found a '-' separator",
                ));
            }
            return Ok(Parsed { value: (), input });
        }
        if input.is_empty() {
            return Err(err!(
                "expected '-' separator, but found end of input"
            ));
        }
        if input[0] != b'-' {
            return Err(err!(
                "expected '-' separator, but found {found:?} instead",
                found = escape::Byte(input[0]),
            ));
        }
        input = &input[1..];
        Ok(Parsed { value: (), input })
    }

    /// Parses the separator that is expected to appear between time
    /// components. When `true` is returned, we expect to parse the next
    /// component. When `false` is returned, then no separator was found and
    /// there is no expectation of finding another component.
    ///
    /// When in extended mode, true is returned if and only if a separator is
    /// found.
    ///
    /// When in basic mode (not extended), then a subsequent component is only
    /// expected when `input` begins with two ASCII digits.
    fn parse_time_separator<'i>(
        &self,
        mut input: &'i [u8],
        extended: bool,
    ) -> Parsed<'i, bool> {
        if !extended {
            let expected =
                input.len() >= 2 && input[..2].iter().all(u8::is_ascii_digit);
            return Parsed { value: expected, input };
        }
        let is_separator = input.get(0).map_or(false, |&b| b == b':');
        if is_separator {
            input = &input[1..];
        }
        Parsed { value: is_separator, input }
    }

    // TemporalSign :::
    //   ASCIISign
    //   <MINUS>
    //
    // ASCIISign ::: one of
    //   + -
    //
    // NOTE: We specifically only support ASCII signs. I think Temporal needs
    // to support `<MINUS>` because of other things in ECMA script that
    // require it?[1]
    //
    // [1]: https://github.com/tc39/proposal-temporal/issues/2843
    fn parse_year_sign<'i>(
        &self,
        mut input: &'i [u8],
    ) -> Parsed<'i, Option<t::Sign>> {
        let Some(sign) = input.get(0).copied() else {
            return Parsed { value: None, input };
        };
        let sign = if sign == b'+' {
            t::Sign::N::<1>()
        } else if sign == b'-' {
            t::Sign::N::<-1>()
        } else {
            return Parsed { value: None, input };
        };
        input = &input[1..];
        Parsed { value: Some(sign), input }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct DateTimePrinter {
    lowercase: bool,
    separator: u8,
    rfc9557: bool,
}

impl DateTimePrinter {
    pub(crate) const fn new() -> DateTimePrinter {
        DateTimePrinter { lowercase: false, separator: b'T', rfc9557: true }
    }

    pub(crate) const fn lowercase(self, yes: bool) -> DateTimePrinter {
        DateTimePrinter { lowercase: yes, ..self }
    }

    pub(crate) const fn separator(self, ascii_char: u8) -> DateTimePrinter {
        assert!(ascii_char.is_ascii(), "RFC3339 separator must be ASCII");
        DateTimePrinter { separator: ascii_char, ..self }
    }

    pub(crate) const fn rfc9557(self, yes: bool) -> DateTimePrinter {
        DateTimePrinter { rfc9557: yes, ..self }
    }

    pub(crate) fn print_zoned<S: TimeScale, W: Write>(
        &self,
        zoned: &Zoned<S>,
        mut wtr: W,
    ) -> Result<(), Error> {
        let instant = zoned.to_instant();
        let tz = zoned.time_zone();
        let (offset, _, _) = tz.to_offset(instant);
        let dt = offset.to_datetime(instant);
        self.print_datetime(&dt, &mut wtr)?;
        self.print_offset(&offset, &mut wtr)?;
        self.print_time_zone(&tz, &offset, &mut wtr)?;
        Ok(())
    }

    pub(crate) fn print_instant<S: TimeScale, W: Write>(
        &self,
        instant: &Instant<S>,
        mut wtr: W,
    ) -> Result<(), Error> {
        let dt = TimeZone::UTC.to_datetime(*instant);
        self.print_datetime(&dt, &mut wtr)?;
        self.print_zulu(&mut wtr)?;
        Ok(())
    }

    /// Formats the given datetime into the writer given.
    pub(crate) fn print_datetime<W: Write>(
        &self,
        dt: &DateTime,
        mut wtr: W,
    ) -> Result<(), Error> {
        self.print_date(&dt.date(), &mut wtr)?;
        self.print_time(&dt.time(), &mut wtr)?;
        Ok(())
    }

    /// Formats the given date into the writer given.
    pub(crate) fn print_date<W: Write>(
        &self,
        date: &Date,
        mut wtr: W,
    ) -> Result<(), Error> {
        static FMT_YEAR: DecimalFormatter =
            DecimalFormatter::new().minimum_digits(4);
        static FMT_TWO: DecimalFormatter =
            DecimalFormatter::new().minimum_digits(2);

        wtr.write_int(&FMT_YEAR, date.year())?;
        wtr.write_str("-");
        wtr.write_int(&FMT_TWO, date.month())?;
        wtr.write_str("-")?;
        wtr.write_int(&FMT_TWO, date.day())?;
        Ok(())
    }

    /// Formats the given time into the writer given.
    pub(crate) fn print_time<W: Write>(
        &self,
        time: &Time,
        mut wtr: W,
    ) -> Result<(), Error> {
        static FMT_TWO: DecimalFormatter =
            DecimalFormatter::new().minimum_digits(2);
        static FMT_FRACTION: DecimalFormatter =
            DecimalFormatter::new().minimum_digits(9);

        wtr.write_char(char::from(if self.lowercase {
            self.separator.to_ascii_lowercase()
        } else {
            self.separator
        }))?;
        wtr.write_int(&FMT_TWO, time.hour())?;
        wtr.write_str(":")?;
        wtr.write_int(&FMT_TWO, time.minute())?;
        wtr.write_str(":")?;
        wtr.write_int(&FMT_TWO, time.second())?;
        let fractional_nanosecond = time.subsec_nanosecond();
        if fractional_nanosecond != 0 {
            wtr.write_str(".")?;
            wtr.write_int(&FMT_FRACTION, fractional_nanosecond)?;
        }
        Ok(())
    }

    /// Formats the given offset into the writer given.
    fn print_offset<W: Write>(
        &self,
        offset: &Offset,
        mut wtr: W,
    ) -> Result<(), Error> {
        static FMT_TWO: DecimalFormatter =
            DecimalFormatter::new().minimum_digits(2);

        wtr.write_str(if offset.is_negative() { "-" } else { "+" })?;
        let mut hours = offset.part_hours_ranged().abs().get();
        let mut minutes = offset.part_minutes_ranged().abs().get();
        // RFC 3339 requires that time zone offsets are an integral number
        // of minutes. While rounding based on seconds doesn't seem clearly
        // indicated, the `1937-01-01T12:00:27.87+00:20` example seems
        // to suggest that the number of minutes should be "as close as
        // possible" to the actual offset. So we just do basic rounding
        // here.
        if offset.part_seconds_ranged().abs() >= 30 {
            if minutes == 59 {
                hours = hours.saturating_add(1);
                minutes = 0;
            } else {
                minutes = minutes.saturating_add(1);
            }
        }
        wtr.write_int(&FMT_TWO, hours)?;
        wtr.write_str(":")?;
        wtr.write_int(&FMT_TWO, minutes)?;
        Ok(())
    }

    /// Prints the "zulu" indicator.
    ///
    /// This should only be used when the local offset is not known. For
    /// example, when printing an `Instant`.
    fn print_zulu<W: Write>(&self, mut wtr: W) -> Result<(), Error> {
        wtr.write_str(if self.lowercase { "z" } else { "Z" })
    }

    /// Formats the given time zone name into the writer given.
    ///
    /// This is a no-op when RFC 9557 support isn't enabled. And when the given
    /// time zone is not an IANA time zone name, then the offset is printed
    /// instead. (This means the offset will be printed twice, which is indeed
    /// an intended behavior of RFC 9557 for cases where a time zone name is
    /// not used or unavailable.)
    fn print_time_zone<W: Write>(
        &self,
        time_zone: &TimeZone,
        offset: &Offset,
        mut wtr: W,
    ) -> Result<(), Error> {
        if !self.rfc9557 {
            return Ok(());
        }
        wtr.write_str("[")?;
        if let Some(iana_name) = time_zone.iana_name() {
            wtr.write_str(iana_name)?;
        } else {
            self.print_offset(offset, &mut wtr)?;
        }
        wtr.write_str("]")?;
        Ok(())
    }
}

impl Default for DateTimePrinter {
    fn default() -> DateTimePrinter {
        DateTimePrinter::new()
    }
}

/// Parses an optional fractional nanosecond from the start of `input`.
///
/// If `input` does not begin with a `.` (or a `,`), then this returns `None`
/// and no input is consumed. Otherwise, up to 9 ASCII digits are parsed after
/// the decimal separator.
pub(crate) fn parse_fractional_nanosecond<'i>(
    mut input: &'i [u8],
) -> Result<Parsed<'i, Option<t::FractionalNanosecond>>, Error> {
    // TimeFraction :::
    //   TemporalDecimalFraction
    //
    // TemporalDecimalFraction :::
    //   TemporalDecimalSeparator DecimalDigit
    //   TemporalDecimalSeparator DecimalDigit DecimalDigit
    //   TemporalDecimalSeparator DecimalDigit DecimalDigit DecimalDigit
    //   TemporalDecimalSeparator DecimalDigit DecimalDigit DecimalDigit
    //                            DecimalDigit
    //   TemporalDecimalSeparator DecimalDigit DecimalDigit DecimalDigit
    //                            DecimalDigit DecimalDigit
    //   TemporalDecimalSeparator DecimalDigit DecimalDigit DecimalDigit
    //                            DecimalDigit DecimalDigit DecimalDigit
    //   TemporalDecimalSeparator DecimalDigit DecimalDigit DecimalDigit
    //                            DecimalDigit DecimalDigit DecimalDigit
    //                            DecimalDigit
    //   TemporalDecimalSeparator DecimalDigit DecimalDigit DecimalDigit
    //                            DecimalDigit DecimalDigit DecimalDigit
    //                            DecimalDigit DecimalDigit
    //   TemporalDecimalSeparator DecimalDigit DecimalDigit DecimalDigit
    //                            DecimalDigit DecimalDigit DecimalDigit
    //                            DecimalDigit DecimalDigit DecimalDigit
    //
    // TemporalDecimalSeparator ::: one of
    //   . ,
    //
    // DecimalDigit :: one of
    //   0 1 2 3 4 5 6 7 8 9

    if input.is_empty() || (input[0] != b'.' && input[0] != b',') {
        return Ok(Parsed { value: None, input });
    }
    input = &input[1..];

    let mkdigits = parse::slicer(input);
    while mkdigits(input).len() <= 8
        && input.first().map_or(false, u8::is_ascii_digit)
    {
        input = &input[1..];
    }
    let digits = mkdigits(input);
    if digits.is_empty() {
        return Err(err!(
            "found decimal after seconds component, \
             but did not find any decimal digits after decimal",
        ));
    }
    // I believe this error can never happen, since we know we have no more
    // than 9 ASCII digits. Any sequence of 9 ASCII digits can be parsed
    // into an `i64`.
    let nanoseconds = parse::fraction(digits, 9).map_err(|err| {
        err!(
            "failed to parse {digits:?} as fractional component \
             (up to 9 digits, nanosecond precision): {err}",
            digits = escape::Bytes(digits),
        )
    })?;
    // I believe this is also impossible to fail, since the maximal
    // fractional nanosecond is 999_999_999, and which also corresponds
    // to the maximal expressible number with 9 ASCII digits. So every
    // possible expressible value here is in range.
    let nanoseconds =
        t::FractionalNanosecond::try_new("nanoseconds", nanoseconds).map_err(
            |err| err!("fractional nanoseconds are not valid: {err}"),
        )?;
    Ok(Parsed { value: Some(nanoseconds), input })
}

#[cfg(test)]
mod tests {
    use alloc::string::String;

    use super::*;

    #[test]
    fn ok_temporal_datetime_basic() {
        let p = |input| {
            DateTimeParser::new().parse_temporal_datetime(input).unwrap()
        };

        insta::assert_debug_snapshot!(p(b"2024-06-01"), @r###"
        Parsed {
            value: ParsedDateTime {
                input: "2024-06-01",
                date: ParsedDate {
                    input: "2024-06-01",
                    date: 2024-06-01,
                },
                time: None,
                offset: None,
                annotations: ParsedAnnotations {
                    input: "",
                    time_zone: None,
                },
            },
            input: "",
        }
        "###);
        insta::assert_debug_snapshot!(p(b"2024-06-01[America/New_York]"), @r###"
        Parsed {
            value: ParsedDateTime {
                input: "2024-06-01[America/New_York]",
                date: ParsedDate {
                    input: "2024-06-01",
                    date: 2024-06-01,
                },
                time: None,
                offset: None,
                annotations: ParsedAnnotations {
                    input: "[America/New_York]",
                    time_zone: Some(
                        Named {
                            critical: false,
                            name: "America/New_York",
                        },
                    ),
                },
            },
            input: "",
        }
        "###);
        insta::assert_debug_snapshot!(p(b"2024-06-01T01:02:03"), @r###"
        Parsed {
            value: ParsedDateTime {
                input: "2024-06-01T01:02:03",
                date: ParsedDate {
                    input: "2024-06-01",
                    date: 2024-06-01,
                },
                time: Some(
                    ParsedTime {
                        input: "01:02:03",
                        time: 01:02:03,
                        extended: true,
                    },
                ),
                offset: None,
                annotations: ParsedAnnotations {
                    input: "",
                    time_zone: None,
                },
            },
            input: "",
        }
        "###);
        insta::assert_debug_snapshot!(p(b"2024-06-01T01:02:03-05"), @r###"
        Parsed {
            value: ParsedDateTime {
                input: "2024-06-01T01:02:03-05",
                date: ParsedDate {
                    input: "2024-06-01",
                    date: 2024-06-01,
                },
                time: Some(
                    ParsedTime {
                        input: "01:02:03",
                        time: 01:02:03,
                        extended: true,
                    },
                ),
                offset: Some(
                    ParsedOffset {
                        input: "-05",
                        kind: Numeric(
                            -05,
                        ),
                    },
                ),
                annotations: ParsedAnnotations {
                    input: "",
                    time_zone: None,
                },
            },
            input: "",
        }
        "###);
        insta::assert_debug_snapshot!(p(b"2024-06-01T01:02:03-05[America/New_York]"), @r###"
        Parsed {
            value: ParsedDateTime {
                input: "2024-06-01T01:02:03-05[America/New_York]",
                date: ParsedDate {
                    input: "2024-06-01",
                    date: 2024-06-01,
                },
                time: Some(
                    ParsedTime {
                        input: "01:02:03",
                        time: 01:02:03,
                        extended: true,
                    },
                ),
                offset: Some(
                    ParsedOffset {
                        input: "-05",
                        kind: Numeric(
                            -05,
                        ),
                    },
                ),
                annotations: ParsedAnnotations {
                    input: "[America/New_York]",
                    time_zone: Some(
                        Named {
                            critical: false,
                            name: "America/New_York",
                        },
                    ),
                },
            },
            input: "",
        }
        "###);
        insta::assert_debug_snapshot!(p(b"2024-06-01T01:02:03Z[America/New_York]"), @r###"
        Parsed {
            value: ParsedDateTime {
                input: "2024-06-01T01:02:03Z[America/New_York]",
                date: ParsedDate {
                    input: "2024-06-01",
                    date: 2024-06-01,
                },
                time: Some(
                    ParsedTime {
                        input: "01:02:03",
                        time: 01:02:03,
                        extended: true,
                    },
                ),
                offset: Some(
                    ParsedOffset {
                        input: "Z",
                        kind: Zulu,
                    },
                ),
                annotations: ParsedAnnotations {
                    input: "[America/New_York]",
                    time_zone: Some(
                        Named {
                            critical: false,
                            name: "America/New_York",
                        },
                    ),
                },
            },
            input: "",
        }
        "###);
        insta::assert_debug_snapshot!(p(b"2024-06-01T01:02:03-01[America/New_York]"), @r###"
        Parsed {
            value: ParsedDateTime {
                input: "2024-06-01T01:02:03-01[America/New_York]",
                date: ParsedDate {
                    input: "2024-06-01",
                    date: 2024-06-01,
                },
                time: Some(
                    ParsedTime {
                        input: "01:02:03",
                        time: 01:02:03,
                        extended: true,
                    },
                ),
                offset: Some(
                    ParsedOffset {
                        input: "-01",
                        kind: Numeric(
                            -01,
                        ),
                    },
                ),
                annotations: ParsedAnnotations {
                    input: "[America/New_York]",
                    time_zone: Some(
                        Named {
                            critical: false,
                            name: "America/New_York",
                        },
                    ),
                },
            },
            input: "",
        }
        "###);
    }

    #[test]
    fn ok_temporal_datetime_incomplete() {
        let p = |input| {
            DateTimeParser::new().parse_temporal_datetime(input).unwrap()
        };

        insta::assert_debug_snapshot!(p(b"2024-06-01T01"), @r###"
        Parsed {
            value: ParsedDateTime {
                input: "2024-06-01T01",
                date: ParsedDate {
                    input: "2024-06-01",
                    date: 2024-06-01,
                },
                time: Some(
                    ParsedTime {
                        input: "01",
                        time: 01:00:00,
                        extended: false,
                    },
                ),
                offset: None,
                annotations: ParsedAnnotations {
                    input: "",
                    time_zone: None,
                },
            },
            input: "",
        }
        "###);
        insta::assert_debug_snapshot!(p(b"2024-06-01T0102"), @r###"
        Parsed {
            value: ParsedDateTime {
                input: "2024-06-01T0102",
                date: ParsedDate {
                    input: "2024-06-01",
                    date: 2024-06-01,
                },
                time: Some(
                    ParsedTime {
                        input: "0102",
                        time: 01:02:00,
                        extended: false,
                    },
                ),
                offset: None,
                annotations: ParsedAnnotations {
                    input: "",
                    time_zone: None,
                },
            },
            input: "",
        }
        "###);
        insta::assert_debug_snapshot!(p(b"2024-06-01T01:02"), @r###"
        Parsed {
            value: ParsedDateTime {
                input: "2024-06-01T01:02",
                date: ParsedDate {
                    input: "2024-06-01",
                    date: 2024-06-01,
                },
                time: Some(
                    ParsedTime {
                        input: "01:02",
                        time: 01:02:00,
                        extended: true,
                    },
                ),
                offset: None,
                annotations: ParsedAnnotations {
                    input: "",
                    time_zone: None,
                },
            },
            input: "",
        }
        "###);
    }

    #[test]
    fn ok_temporal_datetime_separator() {
        let p = |input| {
            DateTimeParser::new().parse_temporal_datetime(input).unwrap()
        };

        insta::assert_debug_snapshot!(p(b"2024-06-01t01:02:03"), @r###"
        Parsed {
            value: ParsedDateTime {
                input: "2024-06-01t01:02:03",
                date: ParsedDate {
                    input: "2024-06-01",
                    date: 2024-06-01,
                },
                time: Some(
                    ParsedTime {
                        input: "01:02:03",
                        time: 01:02:03,
                        extended: true,
                    },
                ),
                offset: None,
                annotations: ParsedAnnotations {
                    input: "",
                    time_zone: None,
                },
            },
            input: "",
        }
        "###);
        insta::assert_debug_snapshot!(p(b"2024-06-01 01:02:03"), @r###"
        Parsed {
            value: ParsedDateTime {
                input: "2024-06-01 01:02:03",
                date: ParsedDate {
                    input: "2024-06-01",
                    date: 2024-06-01,
                },
                time: Some(
                    ParsedTime {
                        input: "01:02:03",
                        time: 01:02:03,
                        extended: true,
                    },
                ),
                offset: None,
                annotations: ParsedAnnotations {
                    input: "",
                    time_zone: None,
                },
            },
            input: "",
        }
        "###);
    }

    #[test]
    fn ok_temporal_time_basic() {
        let p =
            |input| DateTimeParser::new().parse_temporal_time(input).unwrap();

        insta::assert_debug_snapshot!(p(b"01:02:03"), @r###"
        Parsed {
            value: ParsedTime {
                input: "01:02:03",
                time: 01:02:03,
                extended: true,
            },
            input: "",
        }
        "###);
        insta::assert_debug_snapshot!(p(b"130113"), @r###"
        Parsed {
            value: ParsedTime {
                input: "130113",
                time: 13:01:13,
                extended: false,
            },
            input: "",
        }
        "###);
        insta::assert_debug_snapshot!(p(b"T01:02:03"), @r###"
        Parsed {
            value: ParsedTime {
                input: "01:02:03",
                time: 01:02:03,
                extended: true,
            },
            input: "",
        }
        "###);
        insta::assert_debug_snapshot!(p(b"T010203"), @r###"
        Parsed {
            value: ParsedTime {
                input: "010203",
                time: 01:02:03,
                extended: false,
            },
            input: "",
        }
        "###);
    }

    #[test]
    fn ok_temporal_time_from_full_datetime() {
        let p =
            |input| DateTimeParser::new().parse_temporal_time(input).unwrap();

        insta::assert_debug_snapshot!(p(b"2024-06-01T01:02:03"), @r###"
        Parsed {
            value: ParsedTime {
                input: "01:02:03",
                time: 01:02:03,
                extended: true,
            },
            input: "",
        }
        "###);
        insta::assert_debug_snapshot!(p(b"2024-06-01T01:02:03.123"), @r###"
        Parsed {
            value: ParsedTime {
                input: "01:02:03.123",
                time: 01:02:03.123000000,
                extended: true,
            },
            input: "",
        }
        "###);
        insta::assert_debug_snapshot!(p(b"2024-06-01T01"), @r###"
        Parsed {
            value: ParsedTime {
                input: "01",
                time: 01:00:00,
                extended: false,
            },
            input: "",
        }
        "###);
        insta::assert_debug_snapshot!(p(b"2024-06-01T0102"), @r###"
        Parsed {
            value: ParsedTime {
                input: "0102",
                time: 01:02:00,
                extended: false,
            },
            input: "",
        }
        "###);
        insta::assert_debug_snapshot!(p(b"2024-06-01T010203"), @r###"
        Parsed {
            value: ParsedTime {
                input: "010203",
                time: 01:02:03,
                extended: false,
            },
            input: "",
        }
        "###);
        insta::assert_debug_snapshot!(p(b"2024-06-01T010203-05"), @r###"
        Parsed {
            value: ParsedTime {
                input: "010203",
                time: 01:02:03,
                extended: false,
            },
            input: "",
        }
        "###);
        insta::assert_debug_snapshot!(
            p(b"2024-06-01T010203-05[America/New_York]"), @r###"
        Parsed {
            value: ParsedTime {
                input: "010203",
                time: 01:02:03,
                extended: false,
            },
            input: "",
        }
        "###);
        insta::assert_debug_snapshot!(
            p(b"2024-06-01T010203[America/New_York]"), @r###"
        Parsed {
            value: ParsedTime {
                input: "010203",
                time: 01:02:03,
                extended: false,
            },
            input: "",
        }
        "###);
    }

    #[test]
    fn err_temporal_time_ambiguous() {
        let p = |input| {
            DateTimeParser::new().parse_temporal_time(input).unwrap_err()
        };

        insta::assert_snapshot!(
            p(b"010203"),
            @r###"parsed time from "010203" is ambiguous with a month-day date"###,
        );
        insta::assert_snapshot!(
            p(b"130112"),
            @r###"parsed time from "130112" is ambiguous with a year-month date"###,
        );
    }

    #[test]
    fn err_temporal_time_missing_time() {
        let p = |input| {
            DateTimeParser::new().parse_temporal_time(input).unwrap_err()
        };

        insta::assert_snapshot!(
            p(b"2024-06-01[America/New_York]"),
            @r###"successfully parsed date from "2024-06-01[America/New_York]", but no time component was found"###,
        );
        // 2099 is not a valid time, but 2099-12-01 is a valid date, so this
        // carves a path where a full datetime parse is OK, but a basic
        // time-only parse is not.
        insta::assert_snapshot!(
            p(b"2099-12-01[America/New_York]"),
            @r###"successfully parsed date from "2099-12-01[America/New_York]", but no time component was found"###,
        );
        // Like above, but this time we use an invalid date. As a result, we
        // get an error reported not on the invalid date, but on how it is an
        // invalid time. (Because we're asking for a time here.)
        insta::assert_snapshot!(
            p(b"2099-13-01[America/New_York]"),
            @r###"failed to parse minute in time "2099-13-01[America/New_York]": minute is not valid: parameter 'minute' with value 99 is not in the required range of 0..=59"###,
        );
    }

    #[test]
    fn err_temporal_time_zulu() {
        let p = |input| {
            DateTimeParser::new().parse_temporal_time(input).unwrap_err()
        };

        insta::assert_snapshot!(
            p(b"T00:00:00Z"),
            @"cannot parse civil time from string with a Zulu offset, parse as an instant and convert to a civil time instead",
        );
        insta::assert_snapshot!(
            p(b"00:00:00Z"),
            @"cannot parse plain time from string with a Zulu offset, parse as an instant and convert to a plain time instead",
        );
        insta::assert_snapshot!(
            p(b"000000Z"),
            @"cannot parse plain time from string with a Zulu offset, parse as an instant and convert to a plain time instead",
        );
        insta::assert_snapshot!(
            p(b"2099-12-01T00:00:00Z"),
            @"cannot parse plain time from full datetime string with a Zulu offset, parse as an instant and convert to a plain time instead",
        );
    }

    #[test]
    fn ok_date_basic() {
        let p = |input| DateTimeParser::new().parse_date_spec(input).unwrap();

        insta::assert_debug_snapshot!(p(b"2010-03-14"), @r###"
        Parsed {
            value: ParsedDate {
                input: "2010-03-14",
                date: 2010-03-14,
            },
            input: "",
        }
        "###);
        insta::assert_debug_snapshot!(p(b"20100314"), @r###"
        Parsed {
            value: ParsedDate {
                input: "20100314",
                date: 2010-03-14,
            },
            input: "",
        }
        "###);
        insta::assert_debug_snapshot!(p(b"2010-03-14T01:02:03"), @r###"
        Parsed {
            value: ParsedDate {
                input: "2010-03-14",
                date: 2010-03-14,
            },
            input: "T01:02:03",
        }
        "###);
        insta::assert_debug_snapshot!(p(b"-009999-03-14"), @r###"
        Parsed {
            value: ParsedDate {
                input: "-009999-03-14",
                date: -9999-03-14,
            },
            input: "",
        }
        "###);
        insta::assert_debug_snapshot!(p(b"+009999-03-14"), @r###"
        Parsed {
            value: ParsedDate {
                input: "+009999-03-14",
                date: 9999-03-14,
            },
            input: "",
        }
        "###);
    }

    #[test]
    fn err_date_empty() {
        insta::assert_snapshot!(
            DateTimeParser::new().parse_date_spec(b"").unwrap_err(),
            @r###"failed to parse year in date "": expected four digit year (or leading sign for six digit year), but found end of input"###,
        );
    }

    #[test]
    fn err_date_year() {
        insta::assert_snapshot!(
            DateTimeParser::new().parse_date_spec(b"123").unwrap_err(),
            @r###"failed to parse year in date "123": expected four digit year (or leading sign for six digit year), but found end of input"###,
        );
        insta::assert_snapshot!(
            DateTimeParser::new().parse_date_spec(b"123a").unwrap_err(),
            @r###"failed to parse year in date "123a": failed to parse "123a" as year (a four digit integer): invalid digit, expected 0-9 but got a"###,
        );

        insta::assert_snapshot!(
            DateTimeParser::new().parse_date_spec(b"-9999").unwrap_err(),
            @r###"failed to parse year in date "-9999": expected six digit year (because of a leading sign), but found end of input"###,
        );
        insta::assert_snapshot!(
            DateTimeParser::new().parse_date_spec(b"+9999").unwrap_err(),
            @r###"failed to parse year in date "+9999": expected six digit year (because of a leading sign), but found end of input"###,
        );
        insta::assert_snapshot!(
            DateTimeParser::new().parse_date_spec(b"-99999").unwrap_err(),
            @r###"failed to parse year in date "-99999": expected six digit year (because of a leading sign), but found end of input"###,
        );
        insta::assert_snapshot!(
            DateTimeParser::new().parse_date_spec(b"+99999").unwrap_err(),
            @r###"failed to parse year in date "+99999": expected six digit year (because of a leading sign), but found end of input"###,
        );
        insta::assert_snapshot!(
            DateTimeParser::new().parse_date_spec(b"-99999a").unwrap_err(),
            @r###"failed to parse year in date "-99999a": failed to parse "99999a" as year (a six digit integer): invalid digit, expected 0-9 but got a"###,
        );
        insta::assert_snapshot!(
            DateTimeParser::new().parse_date_spec(b"+999999").unwrap_err(),
            @r###"failed to parse year in date "+999999": year is not valid: parameter 'year' with value 999999 is not in the required range of -9999..=9999"###,
        );
        insta::assert_snapshot!(
            DateTimeParser::new().parse_date_spec(b"-010000").unwrap_err(),
            @r###"failed to parse year in date "-010000": year is not valid: parameter 'year' with value 10000 is not in the required range of -9999..=9999"###,
        );
    }

    #[test]
    fn err_date_month() {
        insta::assert_snapshot!(
            DateTimeParser::new().parse_date_spec(b"2024-").unwrap_err(),
            @r###"failed to parse month in date "2024-": expected two digit month, but found end of input"###,
        );
        insta::assert_snapshot!(
            DateTimeParser::new().parse_date_spec(b"2024").unwrap_err(),
            @r###"failed to parse month in date "2024": expected two digit month, but found end of input"###,
        );
        insta::assert_snapshot!(
            DateTimeParser::new().parse_date_spec(b"2024-13-01").unwrap_err(),
            @r###"failed to parse month in date "2024-13-01": month is not valid: parameter 'month' with value 13 is not in the required range of 1..=12"###,
        );
        insta::assert_snapshot!(
            DateTimeParser::new().parse_date_spec(b"20241301").unwrap_err(),
            @r###"failed to parse month in date "20241301": month is not valid: parameter 'month' with value 13 is not in the required range of 1..=12"###,
        );
    }

    #[test]
    fn err_date_day() {
        insta::assert_snapshot!(
            DateTimeParser::new().parse_date_spec(b"2024-12-").unwrap_err(),
            @r###"failed to parse day in date "2024-12-": expected two digit day, but found end of input"###,
        );
        insta::assert_snapshot!(
            DateTimeParser::new().parse_date_spec(b"202412").unwrap_err(),
            @r###"failed to parse day in date "202412": expected two digit day, but found end of input"###,
        );
        insta::assert_snapshot!(
            DateTimeParser::new().parse_date_spec(b"2024-12-40").unwrap_err(),
            @r###"failed to parse day in date "2024-12-40": day is not valid: parameter 'day' with value 40 is not in the required range of 1..=31"###,
        );
        insta::assert_snapshot!(
            DateTimeParser::new().parse_date_spec(b"2024-11-31").unwrap_err(),
            @r###"date parsed from "2024-11-31" is not valid: parameter 'day' with value 31 is not in the required range of 1..=30"###,
        );
        insta::assert_snapshot!(
            DateTimeParser::new().parse_date_spec(b"2024-02-30").unwrap_err(),
            @r###"date parsed from "2024-02-30" is not valid: parameter 'day' with value 30 is not in the required range of 1..=29"###,
        );
        insta::assert_snapshot!(
            DateTimeParser::new().parse_date_spec(b"2023-02-29").unwrap_err(),
            @r###"date parsed from "2023-02-29" is not valid: parameter 'day' with value 29 is not in the required range of 1..=28"###,
        );
    }

    #[test]
    fn err_date_separator() {
        insta::assert_snapshot!(
            DateTimeParser::new().parse_date_spec(b"2024-1231").unwrap_err(),
            @"failed to parse separator after month: expected '-' separator, but found 3 instead",
        );
        insta::assert_snapshot!(
            DateTimeParser::new().parse_date_spec(b"202412-31").unwrap_err(),
            @"failed to parse separator after month: expected no separator after month since none was found after the year, but found a '-' separator",
        );
    }

    #[test]
    fn ok_time_basic() {
        let p = |input| DateTimeParser::new().parse_time_spec(input).unwrap();

        insta::assert_debug_snapshot!(p(b"01:02:03"), @r###"
        Parsed {
            value: ParsedTime {
                input: "01:02:03",
                time: 01:02:03,
                extended: true,
            },
            input: "",
        }
        "###);
        insta::assert_debug_snapshot!(p(b"010203"), @r###"
        Parsed {
            value: ParsedTime {
                input: "010203",
                time: 01:02:03,
                extended: false,
            },
            input: "",
        }
        "###);
    }

    #[test]
    fn ok_time_fractional() {
        let p = |input| DateTimeParser::new().parse_time_spec(input).unwrap();

        insta::assert_debug_snapshot!(p(b"01:02:03.123456789"), @r###"
        Parsed {
            value: ParsedTime {
                input: "01:02:03.123456789",
                time: 01:02:03.123456789,
                extended: true,
            },
            input: "",
        }
        "###);
        insta::assert_debug_snapshot!(p(b"010203.123456789"), @r###"
        Parsed {
            value: ParsedTime {
                input: "010203.123456789",
                time: 01:02:03.123456789,
                extended: false,
            },
            input: "",
        }
        "###);

        insta::assert_debug_snapshot!(p(b"01:02:03.9"), @r###"
        Parsed {
            value: ParsedTime {
                input: "01:02:03.9",
                time: 01:02:03.900000000,
                extended: true,
            },
            input: "",
        }
        "###);
    }

    #[test]
    fn ok_time_no_fractional() {
        let p = |input| DateTimeParser::new().parse_time_spec(input).unwrap();

        insta::assert_debug_snapshot!(p(b"01:02.123456789"), @r###"
        Parsed {
            value: ParsedTime {
                input: "01:02",
                time: 01:02:00,
                extended: true,
            },
            input: ".123456789",
        }
        "###);
    }

    #[test]
    fn ok_time_leap() {
        let p = |input| DateTimeParser::new().parse_time_spec(input).unwrap();

        insta::assert_debug_snapshot!(p(b"01:02:60"), @r###"
        Parsed {
            value: ParsedTime {
                input: "01:02:60",
                time: 01:02:60,
                extended: true,
            },
            input: "",
        }
        "###);
    }

    #[test]
    fn ok_time_mixed_format() {
        let p = |input| DateTimeParser::new().parse_time_spec(input).unwrap();

        insta::assert_debug_snapshot!(p(b"01:0203"), @r###"
        Parsed {
            value: ParsedTime {
                input: "01:02",
                time: 01:02:00,
                extended: true,
            },
            input: "03",
        }
        "###);
        insta::assert_debug_snapshot!(p(b"0102:03"), @r###"
        Parsed {
            value: ParsedTime {
                input: "0102",
                time: 01:02:00,
                extended: false,
            },
            input: ":03",
        }
        "###);
    }

    #[test]
    fn err_time_empty() {
        insta::assert_snapshot!(
            DateTimeParser::new().parse_time_spec(b"").unwrap_err(),
            @r###"failed to parse hour in time "": expected two digit hour, but found end of input"###,
        );
    }

    #[test]
    fn err_time_hour() {
        insta::assert_snapshot!(
            DateTimeParser::new().parse_time_spec(b"a").unwrap_err(),
            @r###"failed to parse hour in time "a": expected two digit hour, but found end of input"###,
        );
        insta::assert_snapshot!(
            DateTimeParser::new().parse_time_spec(b"1a").unwrap_err(),
            @r###"failed to parse hour in time "1a": failed to parse "1a" as hour (a two digit integer): invalid digit, expected 0-9 but got a"###,
        );
        insta::assert_snapshot!(
            DateTimeParser::new().parse_time_spec(b"24").unwrap_err(),
            @r###"failed to parse hour in time "24": hour is not valid: parameter 'hour' with value 24 is not in the required range of 0..=23"###,
        );
    }

    #[test]
    fn err_time_minute() {
        insta::assert_snapshot!(
            DateTimeParser::new().parse_time_spec(b"01:").unwrap_err(),
            @r###"failed to parse minute in time "01:": expected two digit minute, but found end of input"###,
        );
        insta::assert_snapshot!(
            DateTimeParser::new().parse_time_spec(b"01:a").unwrap_err(),
            @r###"failed to parse minute in time "01:a": expected two digit minute, but found end of input"###,
        );
        insta::assert_snapshot!(
            DateTimeParser::new().parse_time_spec(b"01:1a").unwrap_err(),
            @r###"failed to parse minute in time "01:1a": failed to parse "1a" as minute (a two digit integer): invalid digit, expected 0-9 but got a"###,
        );
        insta::assert_snapshot!(
            DateTimeParser::new().parse_time_spec(b"01:60").unwrap_err(),
            @r###"failed to parse minute in time "01:60": minute is not valid: parameter 'minute' with value 60 is not in the required range of 0..=59"###,
        );
    }

    #[test]
    fn err_time_second() {
        insta::assert_snapshot!(
            DateTimeParser::new().parse_time_spec(b"01:02:").unwrap_err(),
            @r###"failed to parse second in time "01:02:": expected two digit second, but found end of input"###,
        );
        insta::assert_snapshot!(
            DateTimeParser::new().parse_time_spec(b"01:02:a").unwrap_err(),
            @r###"failed to parse second in time "01:02:a": expected two digit second, but found end of input"###,
        );
        insta::assert_snapshot!(
            DateTimeParser::new().parse_time_spec(b"01:02:1a").unwrap_err(),
            @r###"failed to parse second in time "01:02:1a": failed to parse "1a" as second (a two digit integer): invalid digit, expected 0-9 but got a"###,
        );
        insta::assert_snapshot!(
            DateTimeParser::new().parse_time_spec(b"01:02:61").unwrap_err(),
            @r###"failed to parse second in time "01:02:61": second is not valid: parameter 'second' with value 61 is not in the required range of 0..=60"###,
        );
    }

    #[test]
    fn err_time_fractional() {
        insta::assert_snapshot!(
            DateTimeParser::new().parse_time_spec(b"01:02:03.").unwrap_err(),
            @r###"failed to parse fractional nanoseconds in time "01:02:03.": found decimal after seconds component, but did not find any decimal digits after decimal"###,
        );
        insta::assert_snapshot!(
            DateTimeParser::new().parse_time_spec(b"01:02:03.a").unwrap_err(),
            @r###"failed to parse fractional nanoseconds in time "01:02:03.a": found decimal after seconds component, but did not find any decimal digits after decimal"###,
        );
    }

    #[test]
    fn print_zoned() {
        let dt = DateTime::constant(2024, 3, 10, 5, 34, 45, 0);
        let zoned: Zoned = dt.to_zoned("America/New_York").unwrap();
        let mut buf = String::new();
        DateTimePrinter::new().print_zoned(&zoned, &mut buf).unwrap();
        assert_eq!(buf, "2024-03-10T05:34:45-04:00[America/New_York]");

        let dt = DateTime::constant(2024, 3, 10, 5, 34, 45, 0);
        let zoned: Zoned = dt.to_zoned("America/New_York").unwrap();
        let zoned = zoned.with_time_zone(TimeZone::UTC);
        let mut buf = String::new();
        DateTimePrinter::new().print_zoned(&zoned, &mut buf).unwrap();
        assert_eq!(buf, "2024-03-10T09:34:45+00:00[UTC]");
    }

    #[test]
    fn print_instant() {
        let dt = DateTime::constant(2024, 3, 10, 5, 34, 45, 0);
        let zoned: Zoned = dt.to_zoned("America/New_York").unwrap();
        let mut buf = String::new();
        DateTimePrinter::new()
            .print_instant(&zoned.to_instant(), &mut buf)
            .unwrap();
        assert_eq!(buf, "2024-03-10T09:34:45Z");
    }
}
