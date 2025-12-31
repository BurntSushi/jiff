use core::time::Duration;

use crate::{
    civil::{Date, DateTime, ISOWeekDate, Time},
    error::{fmt::temporal::Error as E, Error},
    fmt::{
        buffer::{ArrayBuffer, BorrowedBuffer},
        temporal::{Pieces, PiecesOffset, TimeZoneAnnotationKind},
        Write,
    },
    span::{Span, UnitSet},
    tz::{Offset, TimeZone},
    SignedDuration, Timestamp, Unit, Zoned,
};

/// Defines the maximum possible length (in bytes) of an RFC 9557 zoned
/// datetime.
///
/// The actual maximal string possible is I believe
/// `-009999-03-14T17:30:00.999999999-04:23[America/Argentina/ComodRivadavia]`,
/// which is 72 bytes. Obviously, the length of the IANA tzdb identifier
/// matters and can be highly variable.
///
/// So why is this bigger than 72? Well, as far as I can tell, there is no
/// guaranteed maximum length for identifiers. Although, it does appear that
/// there is some loose goal to keep them as succinct as possible.
///
/// So... the current longest identifier is 32 bytes. Surely there will never
/// be one longer than 50 bytes, right? Well, that's what we assume here.
/// I don't feel great about this, because if there ever is a longer
/// identifier, the printer will panic. We can't return an error (here)
/// because the printer has to be infallible. There are two possible
/// alternatives here:
///
/// 1. We refuse to create any `TimeZone` with an IANA tzdb identifier longer
/// than the limit we impose here. We can return an error at `TimeZone`
/// construction (since Jiff already knows how to deal with that) and thus
/// everyone downstream of `TimeZone`---including this printer---can make
/// assumptions about the maximum length of identifiers.
///
/// 2. Introduce a buffering mechanism that allows us to define a smaller
/// buffer on the stack that is "flushed" to the caller's `Write` implementation
/// whenever it fills up. We don't have this abstraction yet (as of 2025-12-31),
/// but we'll need it for `strftime`.
///
/// Perhaps even more pernicious is that this error category will only occur
/// when writing to a `Write` that doesn't expose an underlying `Vec<u8>`
/// or `String`. When we have a `String`, and since we can compute a reasonably
/// tight upper bound on the total length cheaply, we'll always reserve a
/// sufficient large capacity to write to.
///
/// FIXME: So I think we really do need to do either (1) or (2) above. I'm
/// inclined to do (2) so that we'll handle all possible reasonable inputs.
/// Although it might be a good idea to impose a maximum limit too. It's very
/// useful to be able to assume maximum lengths of inputs.
const MAX_ZONED_LEN: usize = 90;

/// Defines the maximum possible length (in bytes) of an RFC 3339 timestamp
/// that is always in Zulu time.
///
/// The longest possible string is `-009999-03-14T21:53:08.999999999Z`.
const MAX_TIMESTAMP_ZULU_LEN: usize = 33;

/// Defines the maximum possible length (in bytes) of an RFC 3339 timestamp
/// with an offset (up to minute precision).
///
/// The longest possible string is `-009999-03-15T23:53:07.999999999+25:59`.
const MAX_TIMESTAMP_OFFSET_LEN: usize = 38;

/// Defines the maximum possible length (in bytes) of an ISO 8601 datetime.
///
/// The longest possible string is `-009999-03-14T17:30:00.999999999`.
const MAX_DATETIME_LEN: usize = 32;

/// Defines the maximum possible length (in bytes) of an ISO 8601 date.
///
/// The longest possible string is `-009999-03-14`.
const MAX_DATE_LEN: usize = 13;

/// Defines the maximum possible length (in bytes) of an ISO 8601 time.
///
/// The longest possible string is `17:30:00.999999999`.
const MAX_TIME_LEN: usize = 18;

/// Defines the maximum possible length (in bytes) of an offset.
///
/// The longest possible string is `-25:59:59`.
const MAX_OFFSET_LEN: usize = 9;

/// Defines the maximum possible length (in bytes) of an ISO 8601 week date.
///
/// The longest possible string is `-009999-W11-3`.
const MAX_ISO_WEEK_DATE_LEN: usize = 13;

/// Defines the maximum possible length (in bytes) of a `Span` printed in the
/// Temporal ISO 8601 format.
///
/// The way I computed this length was by using the default printer (since
/// there's only one knob and it doesn't impact the length of the string)
/// and using a negative `Span` with each unit set to
/// its minimum value.
const MAX_SPAN_LEN: usize = 78;

/// Defines the maximum possible length (in bytes) of a duration printed in the
/// Temporal ISO 8601 format.
///
/// This applies to both signed and unsigned durations. Unsigned durations have
/// one more digit, but signed durations can have a negative sign.
const MAX_DURATION_LEN: usize = 35;

#[derive(Clone, Debug)]
pub(super) struct DateTimePrinter {
    lowercase: bool,
    separator: u8,
    precision: Option<u8>,
}

impl DateTimePrinter {
    pub(super) const fn new() -> DateTimePrinter {
        DateTimePrinter { lowercase: false, separator: b'T', precision: None }
    }

    pub(super) const fn lowercase(self, yes: bool) -> DateTimePrinter {
        DateTimePrinter { lowercase: yes, ..self }
    }

    pub(super) const fn separator(self, ascii_char: u8) -> DateTimePrinter {
        assert!(ascii_char.is_ascii(), "RFC3339 separator must be ASCII");
        DateTimePrinter { separator: ascii_char, ..self }
    }

    pub(super) const fn precision(
        self,
        precision: Option<u8>,
    ) -> DateTimePrinter {
        DateTimePrinter { precision, ..self }
    }

    pub(super) fn print_zoned(
        &self,
        zdt: &Zoned,
        wtr: &mut dyn Write,
    ) -> Result<(), Error> {
        /// The base size of an RFC 9557 zoned datetime string.
        ///
        /// 19 comes from the datetime component, e.g., `2025-01-01T00:00:00`
        /// 6 comes from the offset, e.g., `+05:30`
        /// 2 comes from the `[` and `]` for the time zone annotation
        ///
        /// Basically, we always need space for *at least* the above stuff.
        /// The actual time zone annotation name, negative year and fractional
        /// second component are all optional and can vary quite a bit in
        /// length.
        const BASE: usize = 19 + 6 + 2;

        let mut runtime_allocation = BASE
            + zdt.time_zone().iana_name().map(|name| name.len()).unwrap_or(11);
        if zdt.year() < 0 {
            runtime_allocation += 3;
        }
        if zdt.subsec_nanosecond() != 0 {
            runtime_allocation += 10;
        }

        BorrowedBuffer::with_writer::<MAX_ZONED_LEN>(
            wtr,
            runtime_allocation,
            |bbuf| Ok(self.print_zoned_impl(zdt, bbuf)),
        )
    }

    fn print_zoned_impl(&self, zdt: &Zoned, bbuf: &mut BorrowedBuffer<'_>) {
        self.print_datetime_impl(&zdt.datetime(), bbuf);
        let tz = zdt.time_zone();
        if tz.is_unknown() {
            bbuf.write_str("Z[Etc/Unknown]");
        } else {
            self.print_offset_rounded(&zdt.offset(), bbuf);
            self.print_time_zone_annotation(&tz, &zdt.offset(), bbuf);
        }
    }

    pub(super) fn print_timestamp(
        &self,
        timestamp: &Timestamp,
        wtr: &mut dyn Write,
    ) -> Result<(), Error> {
        let mut runtime_allocation = MAX_TIMESTAMP_ZULU_LEN;
        if timestamp.subsec_nanosecond() == 0 {
            runtime_allocation -= 10;
        }
        BorrowedBuffer::with_writer::<MAX_TIMESTAMP_ZULU_LEN>(
            wtr,
            runtime_allocation,
            |bbuf| Ok(self.print_timestamp_impl(timestamp, bbuf)),
        )
    }

    fn print_timestamp_impl(
        &self,
        timestamp: &Timestamp,
        bbuf: &mut BorrowedBuffer<'_>,
    ) {
        let dt = Offset::UTC.to_datetime(*timestamp);
        self.print_datetime_impl(&dt, bbuf);
        self.print_zulu(bbuf);
    }

    pub(super) fn print_timestamp_with_offset(
        &self,
        timestamp: &Timestamp,
        offset: Offset,
        wtr: &mut dyn Write,
    ) -> Result<(), Error> {
        let mut runtime_allocation = MAX_TIMESTAMP_OFFSET_LEN;
        if timestamp.subsec_nanosecond() == 0 {
            runtime_allocation -= 10;
        }
        BorrowedBuffer::with_writer::<MAX_TIMESTAMP_OFFSET_LEN>(
            wtr,
            runtime_allocation,
            |bbuf| {
                Ok(self
                    .print_timestamp_with_offset_impl(timestamp, offset, bbuf))
            },
        )
    }

    fn print_timestamp_with_offset_impl(
        &self,
        timestamp: &Timestamp,
        offset: Offset,
        bbuf: &mut BorrowedBuffer<'_>,
    ) {
        let dt = offset.to_datetime(*timestamp);
        self.print_datetime_impl(&dt, bbuf);
        self.print_offset_rounded(&offset, bbuf);
    }

    pub(super) fn print_datetime(
        &self,
        dt: &DateTime,
        wtr: &mut dyn Write,
    ) -> Result<(), Error> {
        let mut runtime_allocation = MAX_DATETIME_LEN;
        if dt.subsec_nanosecond() == 0 {
            runtime_allocation -= 10;
        }
        BorrowedBuffer::with_writer::<MAX_DATETIME_LEN>(
            wtr,
            runtime_allocation,
            |bbuf| Ok(self.print_datetime_impl(dt, bbuf)),
        )
    }

    /// Formats the given datetime into the writer given.
    fn print_datetime_impl(
        &self,
        dt: &DateTime,
        bbuf: &mut BorrowedBuffer<'_>,
    ) {
        self.print_date_impl(&dt.date(), bbuf);
        bbuf.write_ascii_char(if self.lowercase {
            self.separator.to_ascii_lowercase()
        } else {
            self.separator
        });
        self.print_time_impl(&dt.time(), bbuf);
    }

    pub(super) fn print_date(
        &self,
        date: &Date,
        wtr: &mut dyn Write,
    ) -> Result<(), Error> {
        BorrowedBuffer::with_writer::<MAX_DATE_LEN>(
            wtr,
            MAX_DATE_LEN,
            |bbuf| Ok(self.print_date_impl(date, bbuf)),
        )
    }

    /// Formats the given date into the writer given.
    fn print_date_impl(&self, date: &Date, bbuf: &mut BorrowedBuffer<'_>) {
        let year = date.year();
        if year >= 0 {
            bbuf.write_int_pad4(year.unsigned_abs().into());
        } else {
            bbuf.write_ascii_char(b'-');
            bbuf.write_int_pad6(year.unsigned_abs().into());
        }
        bbuf.write_ascii_char(b'-');
        bbuf.write_int_pad2(date.month().unsigned_abs().into());
        bbuf.write_ascii_char(b'-');
        bbuf.write_int_pad2(date.day().unsigned_abs().into());
    }

    /// Formats the given time into the writer given.
    pub(super) fn print_time(
        &self,
        time: &Time,
        wtr: &mut dyn Write,
    ) -> Result<(), Error> {
        let mut runtime_allocation = MAX_TIME_LEN;
        if time.subsec_nanosecond() == 0 {
            runtime_allocation -= 10;
        }
        BorrowedBuffer::with_writer::<MAX_TIME_LEN>(
            wtr,
            runtime_allocation,
            |bbuf| Ok(self.print_time_impl(time, bbuf)),
        )
    }

    fn print_time_impl(&self, time: &Time, bbuf: &mut BorrowedBuffer<'_>) {
        bbuf.write_int_pad2(time.hour().unsigned_abs().into());
        bbuf.write_ascii_char(b':');
        bbuf.write_int_pad2(time.minute().unsigned_abs().into());
        bbuf.write_ascii_char(b':');
        bbuf.write_int_pad2(time.second().unsigned_abs().into());
        let fractional_nanosecond = time.subsec_nanosecond();
        if self.precision.map_or(fractional_nanosecond != 0, |p| p > 0) {
            bbuf.write_ascii_char(b'.');
            bbuf.write_fraction(
                self.precision,
                fractional_nanosecond.unsigned_abs(),
            );
        }
    }

    /// Formats the given time zone into the writer given.
    pub(super) fn print_time_zone<W: Write>(
        &self,
        tz: &TimeZone,
        mut wtr: W,
    ) -> Result<(), Error> {
        // N.B. We use a `&mut dyn Write` here instead of a
        // `&mut BorrowedBuffer` (as in the other routines for this printer)
        // because this can emit a POSIX time zone string. We don't really have
        // strong guarantees about how long this string can be (although all
        // sensible values are pretty short). Since this API is not expected to
        // be used much, we don't spend the time to try and optimize this.
        //
        // If and when we get a borrowed buffer writer abstraction (for truly
        // variable length output), then we might consider using that here.
        self.print_time_zone_impl(tz, &mut wtr)
    }

    fn print_time_zone_impl(
        &self,
        tz: &TimeZone,
        wtr: &mut dyn Write,
    ) -> Result<(), Error> {
        if let Some(iana_name) = tz.iana_name() {
            return wtr.write_str(iana_name);
        }
        if tz.is_unknown() {
            return wtr.write_str("Etc/Unknown");
        }
        if let Ok(offset) = tz.to_fixed_offset() {
            // Kind of unfortunate, but it's probably better than
            // making `print_offset_full_precision` accept a `dyn Write`.
            let mut buf = ArrayBuffer::<MAX_OFFSET_LEN>::default();
            let mut bbuf = buf.as_borrowed();
            self.print_offset_full_precision(&offset, &mut bbuf);
            return wtr.write_str(bbuf.filled());
        }
        // We get this on `alloc` because we format the POSIX time zone into a
        // `String` first. See the note below.
        //
        // This is generally okay because there is no current (2025-02-28) way
        // to create a `TimeZone` that is *only* a POSIX time zone in core-only
        // environments. (All you can do is create a TZif time zone, which may
        // contain a POSIX time zone, but `tz.posix_tz()` would still return
        // `None` in that case.)
        #[cfg(feature = "alloc")]
        {
            if let Some(posix_tz) = tz.posix_tz() {
                // This is pretty unfortunate, but at time of writing, I
                // didn't see an easy way to make the `Display` impl for
                // `PosixTimeZone` automatically work with
                // `jiff::fmt::Write` without allocating a new string. As
                // far as I can see, I either have to duplicate the code or
                // make it generic in some way. I judged neither to be worth
                // doing for such a rare case. ---AG
                let s = alloc::string::ToString::to_string(posix_tz);
                return wtr.write_str(&s);
            }
        }
        // Ideally this never actually happens, but it can, and there
        // are likely system configurations out there in which it does.
        // I can imagine "lightweight" installations that just have a
        // `/etc/localtime` as a TZif file that doesn't point to any IANA time
        // zone. In which case, serializing a time zone probably doesn't make
        // much sense.
        //
        // Anyway, if you're seeing this error and think there should be a
        // different behavior, please file an issue.
        Err(Error::from(E::PrintTimeZoneFailure))
    }

    pub(super) fn print_pieces<W: Write>(
        &self,
        pieces: &Pieces,
        mut wtr: W,
    ) -> Result<(), Error> {
        // N.B. We don't bother with writing into the spare capacity of a
        // `&mut String` here because with `Pieces` it's a little more
        // complicated to find a more precise upper bound on the length.
        // Plus, I don't think this API is commonly used, so it's not clear
        // that it's worth optimizing. But I'm open to a PR with benchmarks
        // if there's a good use case. ---AG
        let mut buf = ArrayBuffer::<MAX_ZONED_LEN>::default();
        let mut bbuf = buf.as_borrowed();
        // FIXME: This should really use a buffer abstraction. Namely,
        // the `Pieces` API specifically permits arbitrary length strings
        // as time zone name annotations. But as written here, this will
        // panic on overly long strings. Sigh.
        self.print_pieces_impl(pieces, &mut bbuf);
        wtr.write_str(bbuf.filled())
    }

    fn print_pieces_impl(
        &self,
        pieces: &Pieces,
        bbuf: &mut BorrowedBuffer<'_>,
    ) {
        if let Some(time) = pieces.time() {
            let dt = DateTime::from_parts(pieces.date(), time);
            self.print_datetime_impl(&dt, bbuf);
            if let Some(poffset) = pieces.offset() {
                self.print_pieces_offset(&poffset, bbuf);
            }
        } else if let Some(poffset) = pieces.offset() {
            // In this case, we have an offset but no time component. Since
            // `2025-01-02-05:00` isn't valid, we forcefully write out the
            // default time (which is what would be assumed anyway).
            let dt = DateTime::from_parts(pieces.date(), Time::midnight());
            self.print_datetime_impl(&dt, bbuf);
            self.print_pieces_offset(&poffset, bbuf);
        } else {
            // We have no time and no offset, so we can just write the date.
            // It's okay to write this followed by an annotation, e.g.,
            // `2025-01-02[America/New_York]` or even `2025-01-02[-05:00]`.
            self.print_date_impl(&pieces.date(), bbuf);
        }
        // For the time zone annotation, a `Pieces` gives us the annotation
        // name or offset directly, where as with `Zoned`, we have a
        // `TimeZone`. So we hand-roll our own formatter directly from the
        // annotation.
        if let Some(ann) = pieces.time_zone_annotation() {
            bbuf.write_ascii_char(b'[');
            if ann.is_critical() {
                bbuf.write_ascii_char(b'!');
            }
            match *ann.kind() {
                TimeZoneAnnotationKind::Named(ref name) => {
                    bbuf.write_str(name.as_str());
                }
                TimeZoneAnnotationKind::Offset(offset) => {
                    self.print_offset_rounded(&offset, bbuf);
                }
            }
            bbuf.write_ascii_char(b']');
        }
    }

    pub(super) fn print_iso_week_date(
        &self,
        iso_week_date: &ISOWeekDate,
        wtr: &mut dyn Write,
    ) -> Result<(), Error> {
        BorrowedBuffer::with_writer::<MAX_ISO_WEEK_DATE_LEN>(
            wtr,
            MAX_ISO_WEEK_DATE_LEN,
            |bbuf| Ok(self.print_iso_week_date_impl(iso_week_date, bbuf)),
        )
    }

    fn print_iso_week_date_impl(
        &self,
        iso_week_date: &ISOWeekDate,
        bbuf: &mut BorrowedBuffer<'_>,
    ) {
        let year = iso_week_date.year();
        if year >= 0 {
            bbuf.write_int_pad4(year.unsigned_abs().into());
        } else {
            bbuf.write_ascii_char(b'-');
            bbuf.write_int_pad6(year.unsigned_abs().into());
        }
        bbuf.write_ascii_char(b'-');
        bbuf.write_ascii_char(if self.lowercase { b'w' } else { b'W' });
        bbuf.write_int_pad2(iso_week_date.week().unsigned_abs().into());
        bbuf.write_ascii_char(b'-');
        bbuf.write_int1(
            iso_week_date
                .weekday()
                .to_monday_one_offset()
                .unsigned_abs()
                .into(),
        );
    }

    /// Formats the given "pieces" offset into the writer given.
    fn print_pieces_offset(
        &self,
        poffset: &PiecesOffset,
        bbuf: &mut BorrowedBuffer<'_>,
    ) {
        match *poffset {
            PiecesOffset::Zulu => self.print_zulu(bbuf),
            PiecesOffset::Numeric(ref noffset) => {
                if noffset.offset().is_zero() && noffset.is_negative() {
                    bbuf.write_str("-00:00");
                } else {
                    self.print_offset_rounded(&noffset.offset(), bbuf);
                }
            }
        }
    }

    /// Formats the given offset into the writer given.
    ///
    /// If the given offset has non-zero seconds, then they are rounded to
    /// the nearest minute.
    fn print_offset_rounded(
        &self,
        offset: &Offset,
        bbuf: &mut BorrowedBuffer<'_>,
    ) {
        bbuf.write_ascii_char(if offset.is_negative() { b'-' } else { b'+' });
        let (offset_hours, offset_minutes) = offset.round_to_nearest_minute();
        bbuf.write_int_pad2(offset_hours.into());
        bbuf.write_ascii_char(b':');
        bbuf.write_int_pad2(offset_minutes.into());
    }

    /// Formats the given offset into the writer given.
    ///
    /// If the given offset has non-zero seconds, then they are emitted as a
    /// third `:`-delimited component of the offset. If seconds are zero, then
    /// only the hours and minute components are emitted.
    fn print_offset_full_precision(
        &self,
        offset: &Offset,
        bbuf: &mut BorrowedBuffer<'_>,
    ) {
        bbuf.write_ascii_char(if offset.is_negative() { b'-' } else { b'+' });
        let hours = offset.part_hours_ranged().get().unsigned_abs();
        let minutes = offset.part_minutes_ranged().get().unsigned_abs();
        let seconds = offset.part_seconds_ranged().get().unsigned_abs();
        bbuf.write_int_pad2(hours.into());
        bbuf.write_ascii_char(b':');
        bbuf.write_int_pad2(minutes.into());
        if seconds > 0 {
            bbuf.write_ascii_char(b':');
            bbuf.write_int_pad2(seconds.into());
        }
    }

    /// Prints the "zulu" indicator.
    ///
    /// This should only be used when the offset is not known. For example,
    /// when printing a `Timestamp`.
    fn print_zulu(&self, bbuf: &mut BorrowedBuffer<'_>) {
        bbuf.write_ascii_char(if self.lowercase { b'z' } else { b'Z' });
    }

    /// Formats the given time zone name into the writer given as an RFC 9557
    /// time zone annotation.
    ///
    /// When the given time zone is not an IANA time zone name, then the offset
    /// is printed instead. (This means the offset will be printed twice, which
    /// is indeed an intended behavior of RFC 9557 for cases where a time zone
    /// name is not used or unavailable.)
    fn print_time_zone_annotation(
        &self,
        time_zone: &TimeZone,
        offset: &Offset,
        bbuf: &mut BorrowedBuffer<'_>,
    ) {
        bbuf.write_ascii_char(b'[');
        if let Some(iana_name) = time_zone.iana_name() {
            bbuf.write_str(iana_name);
        } else {
            self.print_offset_rounded(offset, bbuf);
        }
        bbuf.write_ascii_char(b']');
    }
}

impl Default for DateTimePrinter {
    fn default() -> DateTimePrinter {
        DateTimePrinter::new()
    }
}

/// A printer for Temporal spans.
///
/// Note that in Temporal, a "span" is called a "duration."
#[derive(Debug)]
pub(super) struct SpanPrinter {
    /// The designators to use.
    designators: &'static Designators,
}

impl SpanPrinter {
    /// Create a new Temporal span printer with the default configuration.
    pub(super) const fn new() -> SpanPrinter {
        SpanPrinter { designators: DESIGNATORS_UPPERCASE }
    }

    /// Use lowercase for unit designator labels.
    ///
    /// By default, unit designator labels are written in uppercase.
    pub(super) const fn lowercase(self, yes: bool) -> SpanPrinter {
        SpanPrinter {
            designators: if yes {
                DESIGNATORS_LOWERCASE
            } else {
                DESIGNATORS_UPPERCASE
            },
        }
    }

    /// Print the given span to the writer given.
    ///
    /// This only returns an error when the given writer returns an error.
    pub(super) fn print_span<W: Write>(
        &self,
        span: &Span,
        mut wtr: W,
    ) -> Result<(), Error> {
        let mut buf = ArrayBuffer::<MAX_SPAN_LEN>::default();
        let mut bbuf = buf.as_borrowed();
        self.print_span_impl(span, &mut bbuf);
        wtr.write_str(bbuf.filled())
    }

    fn print_span_impl(&self, span: &Span, bbuf: &mut BorrowedBuffer<'_>) {
        static SUBSECOND: UnitSet = UnitSet::from_slice(&[
            Unit::Millisecond,
            Unit::Microsecond,
            Unit::Nanosecond,
        ]);

        if span.is_negative() {
            bbuf.write_ascii_char(b'-');
        }
        bbuf.write_ascii_char(b'P');

        let units = span.units();
        if units.contains(Unit::Year) {
            bbuf.write_int(
                span.get_years_unsigned().get().unsigned_abs().into(),
            );
            bbuf.write_ascii_char(self.label(Unit::Year));
        }
        if units.contains(Unit::Month) {
            bbuf.write_int(
                span.get_months_unsigned().get().unsigned_abs().into(),
            );
            bbuf.write_ascii_char(self.label(Unit::Month));
        }
        if units.contains(Unit::Week) {
            bbuf.write_int(
                span.get_weeks_unsigned().get().unsigned_abs().into(),
            );
            bbuf.write_ascii_char(self.label(Unit::Week));
        }
        if units.contains(Unit::Day) {
            bbuf.write_int(
                span.get_days_unsigned().get().unsigned_abs().into(),
            );
            bbuf.write_ascii_char(self.label(Unit::Day));
        }

        if units.only_time().is_empty() {
            if units.only_calendar().is_empty() {
                bbuf.write_ascii_char(b'T');
                bbuf.write_ascii_char(b'0');
                bbuf.write_ascii_char(self.label(Unit::Second));
            }
            return;
        }

        bbuf.write_ascii_char(b'T');

        if units.contains(Unit::Hour) {
            bbuf.write_int(
                span.get_hours_unsigned().get().unsigned_abs().into(),
            );
            bbuf.write_ascii_char(self.label(Unit::Hour));
        }
        if units.contains(Unit::Minute) {
            bbuf.write_int(
                span.get_minutes_unsigned().get().unsigned_abs().into(),
            );
            bbuf.write_ascii_char(self.label(Unit::Minute));
        }

        // ISO 8601 (and Temporal) don't support writing out milliseconds,
        // microseconds or nanoseconds as separate components like for all
        // the other units. Instead, they must be incorporated as fractional
        // seconds. But we only want to do that work if we need to.
        let has_subsecond = !units.intersection(SUBSECOND).is_empty();
        if units.contains(Unit::Second) && !has_subsecond {
            bbuf.write_int(
                span.get_seconds_unsigned().get().unsigned_abs().into(),
            );
            bbuf.write_ascii_char(self.label(Unit::Second));
        } else if has_subsecond {
            // We want to combine our seconds, milliseconds, microseconds and
            // nanoseconds into one single value in terms of nanoseconds. Then
            // we can "balance" that out so that we have a number of seconds
            // and a number of nanoseconds not greater than 1 second. (Which is
            // our fraction.)
            let (seconds, millis, micros, nanos) = (
                Duration::from_secs(
                    span.get_seconds_unsigned().get().unsigned_abs(),
                ),
                Duration::from_millis(
                    span.get_milliseconds_unsigned().get().unsigned_abs(),
                ),
                Duration::from_micros(
                    span.get_microseconds_unsigned().get().unsigned_abs(),
                ),
                Duration::from_nanos(
                    span.get_nanoseconds_unsigned().get().unsigned_abs(),
                ),
            );
            // OK because the maximums for a span's seconds, millis, micros
            // and nanos combined all fit into a 96-bit integer. (This is
            // guaranteed by `Span::to_duration_invariant`.)
            let total = seconds + millis + micros + nanos;
            let (secs, subsecs) = (total.as_secs(), total.subsec_nanos());
            bbuf.write_int(secs);
            if subsecs != 0 {
                bbuf.write_ascii_char(b'.');
                bbuf.write_fraction(None, subsecs);
            }
            bbuf.write_ascii_char(self.label(Unit::Second));
        }
    }

    /// Print the given signed duration to the writer given.
    ///
    /// This only returns an error when the given writer returns an error.
    pub(super) fn print_signed_duration<W: Write>(
        &self,
        dur: &SignedDuration,
        mut wtr: W,
    ) -> Result<(), Error> {
        let mut buf = ArrayBuffer::<MAX_DURATION_LEN>::default();
        let mut bbuf = buf.as_borrowed();
        if dur.is_negative() {
            bbuf.write_ascii_char(b'-');
        }
        self.print_unsigned_duration_impl(&dur.unsigned_abs(), &mut bbuf);
        wtr.write_str(bbuf.filled())
    }

    /// Print the given unsigned duration to the writer given.
    ///
    /// This only returns an error when the given writer returns an error.
    pub(super) fn print_unsigned_duration<W: Write>(
        &self,
        dur: &Duration,
        mut wtr: W,
    ) -> Result<(), Error> {
        let mut buf = ArrayBuffer::<MAX_DURATION_LEN>::default();
        let mut bbuf = buf.as_borrowed();
        self.print_unsigned_duration_impl(dur, &mut bbuf);
        wtr.write_str(bbuf.filled())
    }

    fn print_unsigned_duration_impl(
        &self,
        dur: &Duration,
        bbuf: &mut BorrowedBuffer<'_>,
    ) {
        bbuf.write_ascii_char(b'P');
        bbuf.write_ascii_char(b'T');

        let (mut secs, nanos) = (dur.as_secs(), dur.subsec_nanos());
        let non_zero_greater_than_second = secs >= 60;
        if non_zero_greater_than_second {
            let hours = secs / (60 * 60);
            secs %= 60 * 60;
            let minutes = secs / 60;
            secs = secs % 60;
            if hours != 0 {
                bbuf.write_int(hours);
                bbuf.write_ascii_char(self.label(Unit::Hour));
            }
            if minutes != 0 {
                bbuf.write_int(minutes);
                bbuf.write_ascii_char(self.label(Unit::Minute));
            }
        }
        if !non_zero_greater_than_second || secs != 0 || nanos != 0 {
            bbuf.write_int(secs);
            if nanos != 0 {
                bbuf.write_ascii_char(b'.');
                bbuf.write_fraction(None, nanos);
            }
            bbuf.write_ascii_char(self.label(Unit::Second));
        }
    }

    /// Converts the ASCII uppercase unit designator label to lowercase if this
    /// printer is configured to use lowercase. Otherwise the label is returned
    /// unchanged.
    fn label(&self, unit: Unit) -> u8 {
        self.designators.designator(unit)
    }
}

#[derive(Clone, Debug)]
struct Designators {
    // Indexed by `Unit as usize`
    map: [u8; 10],
}

const DESIGNATORS_UPPERCASE: &'static Designators = &Designators {
    // N.B. ISO 8601 duration format doesn't have unit
    // designators for sub-second units.
    map: [0, 0, 0, b'S', b'M', b'H', b'D', b'W', b'M', b'Y'],
};

const DESIGNATORS_LOWERCASE: &'static Designators = &Designators {
    // N.B. ISO 8601 duration format doesn't have unit
    // designators for sub-second units.
    map: [0, 0, 0, b's', b'm', b'h', b'd', b'w', b'm', b'y'],
};

impl Designators {
    /// Returns the designator for the given unit.
    fn designator(&self, unit: Unit) -> u8 {
        self.map[unit as usize]
    }
}

#[cfg(feature = "alloc")]
#[cfg(test)]
mod tests {
    use alloc::string::String;

    use crate::{
        civil::{date, Weekday},
        span::ToSpan,
        util::t,
    };

    use super::*;

    #[test]
    fn print_zoned() {
        if crate::tz::db().is_definitively_empty() {
            return;
        }

        let dt = date(2024, 3, 10).at(5, 34, 45, 0);
        let zoned: Zoned = dt.in_tz("America/New_York").unwrap();
        let mut buf = String::new();
        DateTimePrinter::new().print_zoned(&zoned, &mut buf).unwrap();
        assert_eq!(buf, "2024-03-10T05:34:45-04:00[America/New_York]");

        let dt = date(2024, 3, 10).at(5, 34, 45, 0);
        let zoned: Zoned = dt.in_tz("America/New_York").unwrap();
        let zoned = zoned.with_time_zone(TimeZone::UTC);
        let mut buf = String::new();
        DateTimePrinter::new().print_zoned(&zoned, &mut buf).unwrap();
        assert_eq!(buf, "2024-03-10T09:34:45+00:00[UTC]");

        let dt = date(2024, 3, 10).at(5, 34, 45, 0);
        let zoned: Zoned = dt.to_zoned(TimeZone::fixed(Offset::MIN)).unwrap();
        let mut buf = String::new();
        DateTimePrinter::new().print_zoned(&zoned, &mut buf).unwrap();
        assert_eq!(buf, "2024-03-10T05:34:45-25:59[-25:59]");

        let dt = date(2024, 3, 10).at(5, 34, 45, 0);
        let zoned: Zoned = dt.to_zoned(TimeZone::fixed(Offset::MAX)).unwrap();
        let mut buf = String::new();
        DateTimePrinter::new().print_zoned(&zoned, &mut buf).unwrap();
        assert_eq!(buf, "2024-03-10T05:34:45+25:59[+25:59]");
    }

    #[test]
    fn print_timestamp() {
        if crate::tz::db().is_definitively_empty() {
            return;
        }

        let dt = date(2024, 3, 10).at(5, 34, 45, 0);
        let zoned: Zoned = dt.in_tz("America/New_York").unwrap();
        let mut buf = String::new();
        DateTimePrinter::new()
            .print_timestamp(&zoned.timestamp(), &mut buf)
            .unwrap();
        assert_eq!(buf, "2024-03-10T09:34:45Z");

        let dt = date(-2024, 3, 10).at(5, 34, 45, 0);
        let zoned: Zoned = dt.in_tz("America/New_York").unwrap();
        let mut buf = String::new();
        DateTimePrinter::new()
            .print_timestamp(&zoned.timestamp(), &mut buf)
            .unwrap();
        assert_eq!(buf, "-002024-03-10T10:30:47Z");
    }

    #[test]
    fn print_timestamp_with_offset() {
        if crate::tz::db().is_definitively_empty() {
            return;
        }

        let dt = date(2024, 3, 10).at(5, 34, 45, 0);
        let zoned: Zoned = dt.in_tz("America/New_York").unwrap();
        let mut buf = String::new();
        DateTimePrinter::new()
            .print_timestamp_with_offset(
                &zoned.timestamp(),
                zoned.offset(),
                &mut buf,
            )
            .unwrap();
        assert_eq!(buf, "2024-03-10T05:34:45-04:00");

        let dt = date(-2024, 3, 10).at(5, 34, 45, 0);
        let zoned: Zoned = dt.in_tz("America/New_York").unwrap();
        let mut buf = String::new();
        DateTimePrinter::new()
            .print_timestamp_with_offset(
                &zoned.timestamp(),
                zoned.offset(),
                &mut buf,
            )
            .unwrap();
        assert_eq!(buf, "-002024-03-10T05:34:45-04:56");
    }

    #[test]
    fn print_span_basic() {
        let p = |span: Span| -> String {
            let mut buf = String::new();
            SpanPrinter::new().print_span(&span, &mut buf).unwrap();
            buf
        };

        insta::assert_snapshot!(p(Span::new()), @"PT0S");
        insta::assert_snapshot!(p(1.second()), @"PT1S");
        insta::assert_snapshot!(p(-1.second()), @"-PT1S");
        insta::assert_snapshot!(p(
            1.second().milliseconds(1).microseconds(1).nanoseconds(1),
        ), @"PT1.001001001S");
        insta::assert_snapshot!(p(
            0.second().milliseconds(999).microseconds(999).nanoseconds(999),
        ), @"PT0.999999999S");
        insta::assert_snapshot!(p(
            1.year().months(1).weeks(1).days(1)
            .hours(1).minutes(1).seconds(1)
            .milliseconds(1).microseconds(1).nanoseconds(1),
        ), @"P1Y1M1W1DT1H1M1.001001001S");
        insta::assert_snapshot!(p(
            -1.year().months(1).weeks(1).days(1)
            .hours(1).minutes(1).seconds(1)
            .milliseconds(1).microseconds(1).nanoseconds(1),
        ), @"-P1Y1M1W1DT1H1M1.001001001S");
    }

    #[test]
    fn print_span_subsecond_positive() {
        let p = |span: Span| -> String {
            let mut buf = String::new();
            SpanPrinter::new().print_span(&span, &mut buf).unwrap();
            buf
        };

        // These are all sub-second trickery tests.
        insta::assert_snapshot!(p(
            0.second().milliseconds(1000).microseconds(1000).nanoseconds(1000),
        ), @"PT1.001001S");
        insta::assert_snapshot!(p(
            1.second().milliseconds(1000).microseconds(1000).nanoseconds(1000),
        ), @"PT2.001001S");
        insta::assert_snapshot!(p(
            0.second()
            .milliseconds(t::SpanMilliseconds::MAX_REPR),
        ), @"PT631107417600S");
        insta::assert_snapshot!(p(
            0.second()
            .microseconds(t::SpanMicroseconds::MAX_REPR),
        ), @"PT631107417600S");
        insta::assert_snapshot!(p(
            0.second()
            .nanoseconds(t::SpanNanoseconds::MAX_REPR),
        ), @"PT9223372036.854775807S");

        insta::assert_snapshot!(p(
            0.second()
            .milliseconds(t::SpanMilliseconds::MAX_REPR)
            .microseconds(999_999),
        ), @"PT631107417600.999999S");
        // This is 1 microsecond more than the maximum number of seconds
        // representable in a span.
        insta::assert_snapshot!(p(
            0.second()
            .milliseconds(t::SpanMilliseconds::MAX_REPR)
            .microseconds(1_000_000),
        ), @"PT631107417601S");
        insta::assert_snapshot!(p(
            0.second()
            .milliseconds(t::SpanMilliseconds::MAX_REPR)
            .microseconds(1_000_001),
        ), @"PT631107417601.000001S");
        // This is 1 nanosecond more than the maximum number of seconds
        // representable in a span.
        insta::assert_snapshot!(p(
            0.second()
            .milliseconds(t::SpanMilliseconds::MAX_REPR)
            .nanoseconds(1_000_000_000),
        ), @"PT631107417601S");
        insta::assert_snapshot!(p(
            0.second()
            .milliseconds(t::SpanMilliseconds::MAX_REPR)
            .nanoseconds(1_000_000_001),
        ), @"PT631107417601.000000001S");

        // The max millis, micros and nanos, combined.
        insta::assert_snapshot!(p(
            0.second()
            .milliseconds(t::SpanMilliseconds::MAX_REPR)
            .microseconds(t::SpanMicroseconds::MAX_REPR)
            .nanoseconds(t::SpanNanoseconds::MAX_REPR),
        ), @"PT1271438207236.854775807S");
        // The max seconds, millis, micros and nanos, combined.
        insta::assert_snapshot!(p(
            Span::new()
            .seconds(t::SpanSeconds::MAX_REPR)
            .milliseconds(t::SpanMilliseconds::MAX_REPR)
            .microseconds(t::SpanMicroseconds::MAX_REPR)
            .nanoseconds(t::SpanNanoseconds::MAX_REPR),
        ), @"PT1902545624836.854775807S");
    }

    #[test]
    fn print_span_subsecond_negative() {
        let p = |span: Span| -> String {
            let mut buf = String::new();
            SpanPrinter::new().print_span(&span, &mut buf).unwrap();
            buf
        };

        // These are all sub-second trickery tests.
        insta::assert_snapshot!(p(
            -0.second().milliseconds(1000).microseconds(1000).nanoseconds(1000),
        ), @"-PT1.001001S");
        insta::assert_snapshot!(p(
            -1.second().milliseconds(1000).microseconds(1000).nanoseconds(1000),
        ), @"-PT2.001001S");
        insta::assert_snapshot!(p(
            0.second()
            .milliseconds(t::SpanMilliseconds::MIN_REPR),
        ), @"-PT631107417600S");
        insta::assert_snapshot!(p(
            0.second()
            .microseconds(t::SpanMicroseconds::MIN_REPR),
        ), @"-PT631107417600S");
        insta::assert_snapshot!(p(
            0.second()
            .nanoseconds(t::SpanNanoseconds::MIN_REPR),
        ), @"-PT9223372036.854775807S");

        insta::assert_snapshot!(p(
            0.second()
            .milliseconds(t::SpanMilliseconds::MIN_REPR)
            .microseconds(999_999),
        ), @"-PT631107417600.999999S");
        // This is 1 microsecond more than the maximum number of seconds
        // representable in a span.
        insta::assert_snapshot!(p(
            0.second()
            .milliseconds(t::SpanMilliseconds::MIN_REPR)
            .microseconds(1_000_000),
        ), @"-PT631107417601S");
        insta::assert_snapshot!(p(
            0.second()
            .milliseconds(t::SpanMilliseconds::MIN_REPR)
            .microseconds(1_000_001),
        ), @"-PT631107417601.000001S");
        // This is 1 nanosecond more than the maximum number of seconds
        // representable in a span.
        insta::assert_snapshot!(p(
            0.second()
            .milliseconds(t::SpanMilliseconds::MIN_REPR)
            .nanoseconds(1_000_000_000),
        ), @"-PT631107417601S");
        insta::assert_snapshot!(p(
            0.second()
            .milliseconds(t::SpanMilliseconds::MIN_REPR)
            .nanoseconds(1_000_000_001),
        ), @"-PT631107417601.000000001S");

        // The max millis, micros and nanos, combined.
        insta::assert_snapshot!(p(
            0.second()
            .milliseconds(t::SpanMilliseconds::MIN_REPR)
            .microseconds(t::SpanMicroseconds::MIN_REPR)
            .nanoseconds(t::SpanNanoseconds::MIN_REPR),
        ), @"-PT1271438207236.854775807S");
        // The max seconds, millis, micros and nanos, combined.
        insta::assert_snapshot!(p(
            Span::new()
            .seconds(t::SpanSeconds::MIN_REPR)
            .milliseconds(t::SpanMilliseconds::MIN_REPR)
            .microseconds(t::SpanMicroseconds::MIN_REPR)
            .nanoseconds(t::SpanNanoseconds::MIN_REPR),
        ), @"-PT1902545624836.854775807S");
    }

    #[test]
    fn print_signed_duration() {
        let p = |secs, nanos| -> String {
            let dur = SignedDuration::new(secs, nanos);
            let mut buf = String::new();
            SpanPrinter::new().print_signed_duration(&dur, &mut buf).unwrap();
            buf
        };

        insta::assert_snapshot!(p(0, 0), @"PT0S");
        insta::assert_snapshot!(p(0, 1), @"PT0.000000001S");
        insta::assert_snapshot!(p(1, 0), @"PT1S");
        insta::assert_snapshot!(p(59, 0), @"PT59S");
        insta::assert_snapshot!(p(60, 0), @"PT1M");
        insta::assert_snapshot!(p(60, 1), @"PT1M0.000000001S");
        insta::assert_snapshot!(p(61, 1), @"PT1M1.000000001S");
        insta::assert_snapshot!(p(3_600, 0), @"PT1H");
        insta::assert_snapshot!(p(3_600, 1), @"PT1H0.000000001S");
        insta::assert_snapshot!(p(3_660, 0), @"PT1H1M");
        insta::assert_snapshot!(p(3_660, 1), @"PT1H1M0.000000001S");
        insta::assert_snapshot!(p(3_661, 0), @"PT1H1M1S");
        insta::assert_snapshot!(p(3_661, 1), @"PT1H1M1.000000001S");

        insta::assert_snapshot!(p(0, -1), @"-PT0.000000001S");
        insta::assert_snapshot!(p(-1, 0), @"-PT1S");
        insta::assert_snapshot!(p(-59, 0), @"-PT59S");
        insta::assert_snapshot!(p(-60, 0), @"-PT1M");
        insta::assert_snapshot!(p(-60, -1), @"-PT1M0.000000001S");
        insta::assert_snapshot!(p(-61, -1), @"-PT1M1.000000001S");
        insta::assert_snapshot!(p(-3_600, 0), @"-PT1H");
        insta::assert_snapshot!(p(-3_600, -1), @"-PT1H0.000000001S");
        insta::assert_snapshot!(p(-3_660, 0), @"-PT1H1M");
        insta::assert_snapshot!(p(-3_660, -1), @"-PT1H1M0.000000001S");
        insta::assert_snapshot!(p(-3_661, 0), @"-PT1H1M1S");
        insta::assert_snapshot!(p(-3_661, -1), @"-PT1H1M1.000000001S");

        insta::assert_snapshot!(
            p(i64::MIN, -999_999_999),
            @"-PT2562047788015215H30M8.999999999S",
        );
        insta::assert_snapshot!(
            p(i64::MAX, 999_999_999),
            @"PT2562047788015215H30M7.999999999S",
        );
    }

    #[test]
    fn print_unsigned_duration() {
        let p = |secs, nanos| -> String {
            let dur = Duration::new(secs, nanos);
            let mut buf = String::new();
            SpanPrinter::new()
                .print_unsigned_duration(&dur, &mut buf)
                .unwrap();
            buf
        };

        insta::assert_snapshot!(p(0, 0), @"PT0S");
        insta::assert_snapshot!(p(0, 1), @"PT0.000000001S");
        insta::assert_snapshot!(p(1, 0), @"PT1S");
        insta::assert_snapshot!(p(59, 0), @"PT59S");
        insta::assert_snapshot!(p(60, 0), @"PT1M");
        insta::assert_snapshot!(p(60, 1), @"PT1M0.000000001S");
        insta::assert_snapshot!(p(61, 1), @"PT1M1.000000001S");
        insta::assert_snapshot!(p(3_600, 0), @"PT1H");
        insta::assert_snapshot!(p(3_600, 1), @"PT1H0.000000001S");
        insta::assert_snapshot!(p(3_660, 0), @"PT1H1M");
        insta::assert_snapshot!(p(3_660, 1), @"PT1H1M0.000000001S");
        insta::assert_snapshot!(p(3_661, 0), @"PT1H1M1S");
        insta::assert_snapshot!(p(3_661, 1), @"PT1H1M1.000000001S");

        insta::assert_snapshot!(
            p(u64::MAX, 999_999_999),
            @"PT5124095576030431H15.999999999S",
        );
    }

    #[test]
    fn print_iso_week_date() {
        let p = |d: ISOWeekDate| -> String {
            let mut buf = String::new();
            DateTimePrinter::new().print_iso_week_date(&d, &mut buf).unwrap();
            buf
        };

        insta::assert_snapshot!(
            p(ISOWeekDate::new(2024, 52, Weekday::Monday).unwrap()),
            @"2024-W52-1",
        );
        insta::assert_snapshot!(
            p(ISOWeekDate::new(2004, 1, Weekday::Sunday).unwrap()),
            @"2004-W01-7",
        );
    }
}
