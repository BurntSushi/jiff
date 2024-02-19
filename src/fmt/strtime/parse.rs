use core::fmt::Write;

use crate::{
    civil::Weekday,
    error::{err, ErrorContext},
    fmt::strtime::{BrokenDownTime, Meridiem},
    tz::Offset,
    util::{
        escape, parse,
        rangeint::{ri8, RFrom},
        t::{self, C},
    },
    Error,
};

// Custom offset value ranges. They're the same as what we use for `Offset`,
// but always positive since parsing proceeds by getting the absolute value
// and then applying the sign.
type ParsedOffsetHours = ri8<0, { t::SpanZoneOffsetHours::MAX }>;
type ParsedOffsetMinutes = ri8<0, { t::SpanZoneOffsetMinutes::MAX }>;
type ParsedOffsetSeconds = ri8<0, { t::SpanZoneOffsetSeconds::MAX }>;

pub(super) struct Parser<'f, 'i, 't> {
    pub(super) fmt: &'f [u8],
    pub(super) inp: &'i [u8],
    pub(super) tm: &'t mut BrokenDownTime,
}

impl<'f, 'i, 't> Parser<'f, 'i, 't> {
    pub(super) fn parse(&mut self) -> Result<(), Error> {
        while !self.fmt.is_empty() {
            if self.f() != b'%' {
                self.parse_literal()?;
                continue;
            }
            if !self.bump_fmt() {
                return Err(err!(
                    "invalid format string, expected byte after '%', \
                     but found end of format string",
                ));
            }
            if self.inp.is_empty() {
                return Err(err!(
                    "expected non-empty input for directive %{directive}, \
                     but found end of input",
                    directive = escape::Byte(self.f()),
                ));
            }
            // Skip over flags and width settings. We only use these when
            // formatting. The parser is "flexible" enough to absorb all of
            // this automatically in all cases.
            if matches!(self.f(), b'_' | b'0' | b'-' | b'^' | b'#') {
                let flag = escape::Byte(self.f());
                if !self.bump_fmt() {
                    return Err(err!(
                        "found flag {flag:?} after '%', and expected \
                         a directive after it, but found end of input",
                    ));
                }
            }
            // Same deal with the width setting.
            while self.f().is_ascii_digit() {
                let digit = escape::Byte(self.f());
                if !self.bump_fmt() {
                    return Err(err!(
                        "found last width digit {digit:?}, and expected \
                         another width digit or a directive after it, \
                         but found end of input",
                    ));
                }
            }
            match self.f() {
                b'%' => self.parse_percent().context("%% failed")?,
                b'A' => self.parse_weekday_full().context("%A failed")?,
                b'a' => self.parse_weekday_abbrev().context("%a failed")?,
                b'B' => self.parse_month_name_full().context("%B failed")?,
                b'b' => self.parse_month_name_abbrev().context("%b failed")?,
                b'D' => self.parse_american_date().context("%D failed")?,
                b'd' => self.parse_day().context("%d failed")?,
                b'e' => self.parse_day().context("%e failed")?,
                b'F' => self.parse_iso_date().context("%F failed")?,
                b'H' => self.parse_hour().context("%H failed")?,
                b'h' => self.parse_month_name_abbrev().context("%h failed")?,
                b'I' => self.parse_hour12().context("%I failed")?,
                b'M' => self.parse_minute().context("%M failed")?,
                b'm' => self.parse_month().context("%m failed")?,
                b'P' => self.parse_ampm().context("%P failed")?,
                b'p' => self.parse_ampm().context("%p failed")?,
                b'S' => self.parse_second().context("%S failed")?,
                b'T' => self.parse_clock().context("%T failed")?,
                b'Y' => self.parse_year().context("%Y failed")?,
                b'y' => self.parse_year_2digit().context("%y failed")?,
                b'z' => self.parse_offset_nocolon().context("%z failed")?,
                b':' => {
                    if !self.bump_fmt() {
                        return Err(err!(
                            "invalid format string, expected directive \
                             after '%:'",
                        ));
                    }
                    match self.f() {
                        b'z' => {
                            self.parse_offset_colon().context("%:z failed")?
                        }
                        unk => {
                            return Err(err!(
                                "found unrecognized directive %{unk} \
                                 following %:",
                                unk = escape::Byte(unk),
                            ));
                        }
                    }
                }
                b'Z' => {
                    return Err(err!("cannot parse time zone abbreviations"));
                }
                unk => {
                    return Err(err!(
                        "found unrecognized directive %{unk}",
                        unk = escape::Byte(unk),
                    ));
                }
            }
        }
        Ok(())
    }

    /// Returns the byte at the current position of the format string.
    ///
    /// # Panics
    ///
    /// This panics when the entire format string has been consumed.
    fn f(&self) -> u8 {
        self.fmt[0]
    }

    /// Returns the byte at the current position of the input string.
    ///
    /// # Panics
    ///
    /// This panics when the entire input string has been consumed.
    fn i(&self) -> u8 {
        self.inp[0]
    }

    /// Bumps the position of the format string.
    ///
    /// This returns true in precisely the cases where `self.f()` will not
    /// panic. i.e., When the end of the format string hasn't been reached yet.
    fn bump_fmt(&mut self) -> bool {
        self.fmt = &self.fmt[1..];
        !self.fmt.is_empty()
    }

    /// Bumps the position of the input string.
    ///
    /// This returns true in precisely the cases where `self.i()` will not
    /// panic. i.e., When the end of the input string hasn't been reached yet.
    fn bump_input(&mut self) -> bool {
        self.inp = &self.inp[1..];
        !self.inp.is_empty()
    }

    // We write out a parsing routine for each directive below. Each parsing
    // routine assumes that the parser is positioned immediately after the
    // `%` for the current directive, and that there is at least one unconsumed
    // byte in the input.

    /// Parses a literal from the input that matches the current byte in the
    /// format string.
    ///
    /// This may consume multiple bytes from the input, for example, a single
    /// whitespace byte in the format string can match zero or more whitespace
    /// in the input.
    fn parse_literal(&mut self) -> Result<(), Error> {
        if self.f().is_ascii_whitespace() {
            if !self.inp.is_empty() {
                while self.i().is_ascii_whitespace() && self.bump_input() {}
            }
        } else if self.inp.is_empty() {
            return Err(err!(
                "expected to match literal byte {byte:?} from \
                 format string, but found end of input",
                byte = escape::Byte(self.fmt[0]),
            ));
        } else if self.f() != self.i() {
            return Err(err!(
                "expected to match literal byte {expect:?} from \
                 format string, but found byte {found:?} in input",
                expect = escape::Byte(self.f()),
                found = escape::Byte(self.i()),
            ));
        } else {
            self.bump_input();
        }
        self.bump_fmt();
        Ok(())
    }

    /// Parses a literal '%' from the input.
    fn parse_percent(&mut self) -> Result<(), Error> {
        if self.i() != b'%' {
            return Err(err!(
                "expected '%' due to '%%' in format string, \
                 but found {byte:?} in input",
                byte = escape::Byte(self.inp[0]),
            ));
        }
        self.bump_fmt();
        self.bump_input();
        Ok(())
    }

    /// Parses `%D`, which is equivalent to `%m/%d/%y`.
    fn parse_american_date(&mut self) -> Result<(), Error> {
        let mut p = Parser { fmt: b"%m/%d/%y", inp: self.inp, tm: self.tm };
        p.parse()?;
        self.inp = p.inp;
        self.bump_fmt();
        Ok(())
    }

    /// Parse `%p`, which indicates whether the time is AM or PM.
    ///
    /// This is generally only useful with `%I`. If, say, `%H` is used, then
    /// the AM/PM moniker will be validated, but it doesn't actually influence
    /// the clock time.
    fn parse_ampm(&mut self) -> Result<(), Error> {
        let (index, inp) = parse_ampm(self.inp)?;
        self.inp = inp;

        self.tm.meridiem = Some(match index {
            0 => Meridiem::AM,
            1 => Meridiem::PM,
            // OK because 0 <= index <= 1.
            index => unreachable!("unknown AM/PM index {index}"),
        });
        self.bump_fmt();
        Ok(())
    }

    /// Parses `%T`, which is equivalent to `%H:%M:%S`.
    fn parse_clock(&mut self) -> Result<(), Error> {
        let mut p = Parser { fmt: b"%H:%M:%S", inp: self.inp, tm: self.tm };
        p.parse()?;
        self.inp = p.inp;
        self.bump_fmt();
        Ok(())
    }

    /// Parses `%d` and `%e`, which is equivalent to the day of the month.
    ///
    /// We merely require that it is in the range 1-31 here. It isn't
    /// validated as an actual date until `Pieces` is used.
    fn parse_day(&mut self) -> Result<(), Error> {
        let (day, inp) =
            parse_number(self.inp).context("failed to parse day")?;
        self.inp = inp;

        let day =
            t::Day::try_new("day", day).context("day number is invalid")?;
        self.tm.day = Some(day);
        self.bump_fmt();
        Ok(())
    }

    /// Parses `%H`, which is equivalent to the hour.
    fn parse_hour(&mut self) -> Result<(), Error> {
        let (hour, inp) =
            parse_number(self.inp).context("failed to parse hour")?;
        self.inp = inp;

        let hour = t::Hour::try_new("hour", hour)
            .context("hour number is invalid")?;
        self.tm.hour = Some(hour);
        self.bump_fmt();
        Ok(())
    }

    /// Parses `%I`, which is equivalent to the hour on a 12-hour clock.
    fn parse_hour12(&mut self) -> Result<(), Error> {
        type Hour12 = ri8<1, 12>;

        let (hour, inp) =
            parse_number(self.inp).context("failed to parse hour")?;
        self.inp = inp;

        let hour =
            Hour12::try_new("hour", hour).context("hour number is invalid")?;
        self.tm.hour = Some(t::Hour::rfrom(hour));
        self.bump_fmt();
        Ok(())
    }

    /// Parses `%F`, which is equivalent to `%Y-%m-%d`.
    fn parse_iso_date(&mut self) -> Result<(), Error> {
        let mut p = Parser { fmt: b"%Y-%m-%d", inp: self.inp, tm: self.tm };
        p.parse()?;
        self.inp = p.inp;
        self.bump_fmt();
        Ok(())
    }

    /// Parses `%M`, which is equivalent to the minute.
    fn parse_minute(&mut self) -> Result<(), Error> {
        let (minute, inp) =
            parse_number(self.inp).context("failed to parse minute")?;
        self.inp = inp;

        let minute = t::Minute::try_new("minute", minute)
            .context("minute number is invalid")?;
        self.tm.minute = Some(minute);
        self.bump_fmt();
        Ok(())
    }

    /// Parse `%z`, which is a time zone offset without colons.
    fn parse_offset_nocolon(&mut self) -> Result<(), Error> {
        let (sign, inp) = parse_required_sign(self.inp)
            .context("sign is required for time zone offset")?;
        let (hhmm, inp) = parse::split(inp, 4).ok_or_else(|| {
            err!(
                "expected at least 4 digits for time zone offset \
                 after sign, but found only {len} bytes remaining",
                len = inp.len(),
            )
        })?;

        let hh = parse::i64(&hhmm[0..2]).with_context(|| {
            err!(
                "failed to parse hours from time zone offset {hhmm}",
                hhmm = escape::Bytes(hhmm)
            )
        })?;
        let hh = ParsedOffsetHours::try_new("zone-offset-hours", hh)
            .context("time zone offset hours are not valid")?;
        let hh = t::SpanZoneOffset::rfrom(hh);

        let mm = parse::i64(&hhmm[2..4]).with_context(|| {
            err!(
                "failed to parse minutes from time zone offset {hhmm}",
                hhmm = escape::Bytes(hhmm)
            )
        })?;
        let mm = ParsedOffsetMinutes::try_new("zone-offset-minutes", mm)
            .context("time zone offset minutes are not valid")?;
        let mm = t::SpanZoneOffset::rfrom(mm);

        let (ss, inp) = if inp.len() < 2
            || !inp[..2].iter().all(u8::is_ascii_digit)
        {
            (t::SpanZoneOffset::N::<0>(), inp)
        } else {
            let (ss, inp) = parse::split(inp, 2).unwrap();
            let ss = parse::i64(ss).with_context(|| {
                err!(
                    "failed to parse seconds from time zone offset {ss}",
                    ss = escape::Bytes(ss)
                )
            })?;
            let ss = ParsedOffsetSeconds::try_new("zone-offset-seconds", ss)
                .context("time zone offset seconds are not valid")?;
            if inp.starts_with(b".") {
                // I suppose we could parse them and then round, but meh...
                // (At time of writing, the precision of tz::Offset is
                // seconds. If that improves to nanoseconds, then yes, let's
                // parse fractional seconds here.)
                return Err(err!(
                    "parsing fractional seconds in time zone offset \
                     is not supported",
                ));
            }
            (t::SpanZoneOffset::rfrom(ss), inp)
        };

        let seconds = hh * C(3_600) + mm * C(60) + ss;
        let offset = Offset::from_seconds_ranged(seconds * sign);
        self.tm.offset = Some(offset);
        self.inp = inp;
        self.bump_fmt();

        Ok(())
    }

    /// Parse `%:z`, which is a time zone offset with colons.
    fn parse_offset_colon(&mut self) -> Result<(), Error> {
        let (sign, inp) = parse_required_sign(self.inp)
            .context("sign is required for time zone offset")?;
        let (hhmm, inp) = parse::split(inp, 5).ok_or_else(|| {
            err!(
                "expected at least HH:MM digits for time zone offset \
                 after sign, but found only {len} bytes remaining",
                len = inp.len(),
            )
        })?;
        if hhmm[2] != b':' {
            return Err(err!(
                "expected colon after between HH and MM in time zone \
                 offset, but found {found:?} instead",
                found = escape::Byte(hhmm[2]),
            ));
        }

        let hh = parse::i64(&hhmm[0..2]).with_context(|| {
            err!(
                "failed to parse hours from time zone offset {hhmm}",
                hhmm = escape::Bytes(hhmm)
            )
        })?;
        let hh = ParsedOffsetHours::try_new("zone-offset-hours", hh)
            .context("time zone offset hours are not valid")?;
        let hh = t::SpanZoneOffset::rfrom(hh);

        let mm = parse::i64(&hhmm[3..5]).with_context(|| {
            err!(
                "failed to parse minutes from time zone offset {hhmm}",
                hhmm = escape::Bytes(hhmm)
            )
        })?;
        let mm = ParsedOffsetMinutes::try_new("zone-offset-minutes", mm)
            .context("time zone offset minutes are not valid")?;
        let mm = t::SpanZoneOffset::rfrom(mm);

        let (ss, inp) = if inp.len() < 3
            || inp[0] != b':'
            || !inp[1..3].iter().all(u8::is_ascii_digit)
        {
            (t::SpanZoneOffset::N::<0>(), inp)
        } else {
            let (ss, inp) = parse::split(&inp[1..], 2).unwrap();
            let ss = parse::i64(ss).with_context(|| {
                err!(
                    "failed to parse seconds from time zone offset {ss}",
                    ss = escape::Bytes(ss)
                )
            })?;
            let ss = ParsedOffsetSeconds::try_new("zone-offset-seconds", ss)
                .context("time zone offset seconds are not valid")?;
            if inp.starts_with(b".") {
                // I suppose we could parse them and then round, but meh...
                // (At time of writing, the precision of tz::Offset is
                // seconds. If that improves to nanoseconds, then yes, let's
                // parse fractional seconds here.)
                return Err(err!(
                    "parsing fractional seconds in time zone offset \
                     is not supported",
                ));
            }
            (t::SpanZoneOffset::rfrom(ss), inp)
        };

        let seconds = hh * C(3_600) + mm * C(60) + ss;
        let offset = Offset::from_seconds_ranged(seconds * sign);
        self.tm.offset = Some(offset);
        self.inp = inp;
        self.bump_fmt();

        Ok(())
    }

    /// Parses `%S`, which is equivalent to the second.
    fn parse_second(&mut self) -> Result<(), Error> {
        let (mut second, inp) =
            parse_number(self.inp).context("failed to parse second")?;
        self.inp = inp;

        // As with other parses in Jiff, and like Temporal,
        // we constrain `60` seconds to `59` because we don't
        // support leap seconds.
        if second == 60 {
            second = 59;
        }
        let second = t::Second::try_new("second", second)
            .context("second number is invalid")?;
        self.tm.second = Some(second);
        self.bump_fmt();
        Ok(())
    }

    /// Parses `%m`, which is equivalent to the month.
    fn parse_month(&mut self) -> Result<(), Error> {
        let (month, inp) =
            parse_number(self.inp).context("failed to parse month")?;
        self.inp = inp;

        let month = t::Month::try_new("month", month)
            .context("month number is invalid")?;
        self.tm.month = Some(month);
        self.bump_fmt();
        Ok(())
    }

    /// Parse `%b` or `%h`, which is an abbreviated month name.
    fn parse_month_name_abbrev(&mut self) -> Result<(), Error> {
        let (index, inp) = parse_month_name_abbrev(self.inp)?;
        self.inp = inp;

        // Both are OK because 0 <= index <= 11.
        let index = i8::try_from(index).unwrap();
        self.tm.month = Some(t::Month::new(index + 1).unwrap());
        self.bump_fmt();
        Ok(())
    }

    /// Parse `%B`, which is a full month name.
    fn parse_month_name_full(&mut self) -> Result<(), Error> {
        static CHOICES: &'static [&'static [u8]] = &[
            b"January",
            b"February",
            b"March",
            b"April",
            b"May",
            b"June",
            b"July",
            b"August",
            b"September",
            b"October",
            b"November",
            b"December",
        ];

        let (index, inp) = parse_choice(self.inp, CHOICES)
            .context("unrecognized month name")?;
        self.inp = inp;

        // Both are OK because 0 <= index <= 11.
        let index = i8::try_from(index).unwrap();
        self.tm.month = Some(t::Month::new(index + 1).unwrap());
        self.bump_fmt();
        Ok(())
    }

    /// Parse `%a`, which is an abbreviated weekday.
    fn parse_weekday_abbrev(&mut self) -> Result<(), Error> {
        let (index, inp) = parse_weekday_abbrev(self.inp)?;
        self.inp = inp;

        // Both are OK because 0 <= index <= 6.
        let index = i8::try_from(index).unwrap();
        self.tm.weekday =
            Some(Weekday::from_sunday_zero_offset(index).unwrap());
        self.bump_fmt();
        Ok(())
    }

    /// Parse `%A`, which is a full weekday name.
    fn parse_weekday_full(&mut self) -> Result<(), Error> {
        static CHOICES: &'static [&'static [u8]] = &[
            b"Sunday",
            b"Monday",
            b"Tueday",
            b"Wednesday",
            b"Thursday",
            b"Friday",
            b"Saturday",
        ];

        let (index, inp) = parse_choice(self.inp, CHOICES)
            .context("unrecognized weekday abbreviation")?;
        self.inp = inp;

        // Both are OK because 0 <= index <= 6.
        let index = i8::try_from(index).unwrap();
        self.tm.weekday =
            Some(Weekday::from_sunday_zero_offset(index).unwrap());
        self.bump_fmt();
        Ok(())
    }

    /// Parses `%Y`, which we permit to be any year, including a negative year.
    fn parse_year(&mut self) -> Result<(), Error> {
        let (year, inp) = parse_optional_signed_number(self.inp)
            .context("failed to parse year")?;
        self.inp = inp;

        let year = t::Year::try_new("year", year)
            .context("year number is invalid")?;
        self.tm.year = Some(year);
        self.bump_fmt();
        Ok(())
    }

    /// Parses `%y`, which is equivalent to a 2-digit year.
    ///
    /// The numbers 69-99 refer to 1969-1999, while 00-68 refer to 2000-2068.
    fn parse_year_2digit(&mut self) -> Result<(), Error> {
        type Year2Digit = ri8<0, 99>;

        let (year, inp) =
            parse_number(self.inp).context("failed to parse year")?;
        self.inp = inp;

        let year = Year2Digit::try_new("year (2 digits)", year)
            .context("year number is invalid")?;
        let mut year = t::Year::rfrom(year);
        if year <= 68 {
            year += C(2000);
        } else {
            year += C(1900);
        }
        self.tm.year = Some(year);
        self.bump_fmt();
        Ok(())
    }
}

/// A function that looks for an optional sign (assumed positive if one
/// does not exist) following by a run of one or more ASCII digits and parses
/// it into a signed integer.
///
/// This also returns the remaining unparsed input.
///
/// It is legal to pass an empty input to this routine. In that case, an error
/// is returned.
#[inline(always)]
fn parse_optional_signed_number<'i>(
    input: &'i [u8],
) -> Result<(i64, &'i [u8]), Error> {
    let (sign, input) = parse_optional_sign(input);
    let (number, input) = parse_number(input)?;
    let number = number
        .checked_mul(sign)
        .ok_or_else(|| err!("failed to negate parsed number {number}"))?;
    Ok((number, input))
}

/// A function that looks for a run of ASCII digits and parses it into a
/// number. This returns an error if no ASCII digits could be found or if the
/// number parsed is out of bounds.
///
/// This also returns the remaining unparsed input.
///
/// It is legal to pass an empty input to this routine. In that case, an error
/// is returned.
#[inline(always)]
fn parse_number<'i>(input: &'i [u8]) -> Result<(i64, &'i [u8]), Error> {
    let mut digits = 0;
    while digits < input.len() && input[digits].is_ascii_digit() {
        digits += 1;
    }
    let (digits, input) = input.split_at(digits);
    parse::i64(digits).map(|number| (number, input))
}

/// Parses an optional sign from the beginning of the input. If one isn't
/// found, then the sign returned is positive.
///
/// This also returns the remaining unparsed input.
#[inline(always)]
fn parse_optional_sign<'i>(input: &'i [u8]) -> (i64, &'i [u8]) {
    if input.is_empty() {
        (1, input)
    } else if input[0] == b'-' {
        (-1, &input[1..])
    } else if input[0] == b'+' {
        (1, &input[1..])
    } else {
        (1, input)
    }
}

/// Parses an optional sign from the beginning of the input. If one isn't
/// found, then the sign returned is positive.
///
/// This also returns the remaining unparsed input.
#[inline(always)]
fn parse_required_sign<'i>(
    input: &'i [u8],
) -> Result<(t::Sign, &'i [u8]), Error> {
    if input.is_empty() {
        Err(err!("expected +/- sign, but found end of input"))
    } else if input[0] == b'-' {
        Ok((t::Sign::N::<-1>(), &input[1..]))
    } else if input[0] == b'+' {
        Ok((t::Sign::N::<1>(), &input[1..]))
    } else {
        Err(err!(
            "expected +/- sign, but found {found:?} instead",
            found = escape::Byte(input[0])
        ))
    }
}

/// Parses the input such that, on success, the index of the first matching
/// choice (via ASCII case insensitive comparisons) is returned, along with
/// any remaining unparsed input.
///
/// If no choice given is a prefix of the input, then an error is returned.
/// The error includes the possible allowed choices.
fn parse_choice<'i>(
    input: &'i [u8],
    choices: &[&'static [u8]],
) -> Result<(usize, &'i [u8]), Error> {
    for (i, choice) in choices.into_iter().enumerate() {
        if input.len() < choice.len() {
            continue;
        }
        let (candidate, input) = input.split_at(choice.len());
        if candidate.eq_ignore_ascii_case(choice) {
            return Ok((i, input));
        }
    }
    let mut err = alloc::format!(
        "failed to find expected choice at beginning of {input:?}, \
         available choices are: ",
        input = escape::Bytes(input),
    );
    for (i, choice) in choices.iter().enumerate() {
        if i > 0 {
            write!(err, ", ").unwrap();
        }
        write!(err, "{}", escape::Bytes(choice)).unwrap();
    }
    Err(Error::adhoc(err))
}

/// Like `parse_choice`, but specialized for AM/PM.
///
/// This exists because AM/PM is common and we can take advantage of the fact
/// that they are both exactly two bytes.
#[inline(always)]
fn parse_ampm<'i>(input: &'i [u8]) -> Result<(usize, &'i [u8]), Error> {
    if input.len() < 2 {
        return Err(err!(
            "expected to find AM or PM, \
             but the remaining input, {input:?}, is too short \
             to contain one",
            input = escape::Bytes(input),
        ));
    }
    let (x, input) = input.split_at(2);
    let candidate = &[x[0].to_ascii_lowercase(), x[1].to_ascii_lowercase()];
    let index = match candidate {
        b"am" => 0,
        b"pm" => 1,
        _ => {
            return Err(err!(
                "expected to find AM or PM, but found \
                {candidate:?} instead",
                candidate = escape::Bytes(x),
            ))
        }
    };
    Ok((index, input))
}

/// Like `parse_choice`, but specialized for weekday abbreviation.
///
/// This exists because weekday abbreviations are common and we can take
/// advantage of the fact that they are all exactly three bytes.
#[inline(always)]
fn parse_weekday_abbrev<'i>(
    input: &'i [u8],
) -> Result<(usize, &'i [u8]), Error> {
    if input.len() < 3 {
        return Err(err!(
            "expected to find a weekday abbreviation, \
             but the remaining input, {input:?}, is too short \
             to contain one",
            input = escape::Bytes(input),
        ));
    }
    let (x, input) = input.split_at(3);
    let candidate = &[
        x[0].to_ascii_lowercase(),
        x[1].to_ascii_lowercase(),
        x[2].to_ascii_lowercase(),
    ];
    let index = match candidate {
        b"sun" => 0,
        b"mon" => 1,
        b"tue" => 2,
        b"wed" => 3,
        b"thu" => 4,
        b"fri" => 5,
        b"sat" => 6,
        _ => {
            return Err(err!(
                "expected to find weekday abbreviation, but found \
                {candidate:?} instead",
                candidate = escape::Bytes(x),
            ))
        }
    };
    Ok((index, input))
}

/// Like `parse_choice`, but specialized for month name abbreviation.
///
/// This exists because month name abbreviations are common and we can take
/// advantage of the fact that they are all exactly three bytes.
#[inline(always)]
fn parse_month_name_abbrev<'i>(
    input: &'i [u8],
) -> Result<(usize, &'i [u8]), Error> {
    if input.len() < 3 {
        return Err(err!(
            "expected to find a month name abbreviation, \
             but the remaining input, {input:?}, is too short \
             to contain one",
            input = escape::Bytes(input),
        ));
    }
    let (x, input) = input.split_at(3);
    let candidate = &[
        x[0].to_ascii_lowercase(),
        x[1].to_ascii_lowercase(),
        x[2].to_ascii_lowercase(),
    ];
    let index = match candidate {
        b"jan" => 0,
        b"feb" => 1,
        b"mar" => 2,
        b"apr" => 3,
        b"may" => 4,
        b"jun" => 5,
        b"jul" => 6,
        b"aug" => 7,
        b"sep" => 8,
        b"oct" => 9,
        b"nov" => 10,
        b"dec" => 11,
        _ => {
            return Err(err!(
                "expected to find month name abbreviation, but found \
                 {candidate:?} instead",
                candidate = escape::Bytes(x),
            ))
        }
    };
    Ok((index, input))
}

#[cfg(test)]
mod tests {
    use alloc::string::ToString;

    use super::*;

    #[test]
    fn ok_parse_timestamp() {
        let p = |fmt: &str, input: &str| {
            BrokenDownTime::parse_mono(fmt.as_bytes(), input.as_bytes())
                .unwrap()
                .to_timestamp()
                .unwrap()
        };

        insta::assert_debug_snapshot!(
            p("%h %d, %Y %H:%M:%S %z", "Apr 1, 2022 20:46:15 -0400"),
            @"2022-04-02T00:46:15Z",
        );
        insta::assert_debug_snapshot!(
            p("%h %d, %Y %H:%M:%S %z", "Apr 1, 2022 20:46:15 +0400"),
            @"2022-04-01T16:46:15Z",
        );
        insta::assert_debug_snapshot!(
            p("%h %d, %Y %H:%M:%S %z", "Apr 1, 2022 20:46:15 -040059"),
            @"2022-04-02T00:47:14Z",
        );

        insta::assert_debug_snapshot!(
            p("%h %d, %Y %H:%M:%S %:z", "Apr 1, 2022 20:46:15 -04:00"),
            @"2022-04-02T00:46:15Z",
        );
        insta::assert_debug_snapshot!(
            p("%h %d, %Y %H:%M:%S %:z", "Apr 1, 2022 20:46:15 +04:00"),
            @"2022-04-01T16:46:15Z",
        );
        insta::assert_debug_snapshot!(
            p("%h %d, %Y %H:%M:%S %:z", "Apr 1, 2022 20:46:15 -04:00:59"),
            @"2022-04-02T00:47:14Z",
        );
    }

    #[test]
    fn ok_parse_datetime() {
        let p = |fmt: &str, input: &str| {
            BrokenDownTime::parse_mono(fmt.as_bytes(), input.as_bytes())
                .unwrap()
                .to_datetime()
                .unwrap()
        };

        insta::assert_debug_snapshot!(
            p("%h %d, %Y %H:%M:%S", "Apr 1, 2022 20:46:15"),
            @"2022-04-01T20:46:15",
        );
        insta::assert_debug_snapshot!(
            p("%h %05d, %Y %H:%M:%S", "Apr 1, 2022 20:46:15"),
            @"2022-04-01T20:46:15",
        );
    }

    #[test]
    fn ok_parse_date() {
        let p = |fmt: &str, input: &str| {
            BrokenDownTime::parse_mono(fmt.as_bytes(), input.as_bytes())
                .unwrap()
                .to_date()
                .unwrap()
        };

        insta::assert_debug_snapshot!(
            p("%m/%d/%y", "1/1/0000099"),
            @"1999-01-01",
        );
        insta::assert_debug_snapshot!(
            p("%D", "1/1/0000099"),
            @"1999-01-01",
        );
        insta::assert_debug_snapshot!(
            p("%m/%d/%Y", "1/1/0000099"),
            @"0099-01-01",
        );
        insta::assert_debug_snapshot!(
            p("%m/%d/%Y", "1/1/1999"),
            @"1999-01-01",
        );
        insta::assert_debug_snapshot!(
            p("%m/%d/%Y", "12/31/9999"),
            @"9999-12-31",
        );
        insta::assert_debug_snapshot!(
            p("%m/%d/%Y", "01/01/-9999"),
            @"-009999-01-01",
        );
        insta::assert_snapshot!(
            p("%a %m/%d/%Y", "sun 7/14/2024"),
            @"2024-07-14",
        );
        insta::assert_snapshot!(
            p("%A %m/%d/%Y", "sUnDaY 7/14/2024"),
            @"2024-07-14",
        );
        insta::assert_snapshot!(
            p("%b %d %Y", "Jul 14 2024"),
            @"2024-07-14",
        );
        insta::assert_snapshot!(
            p("%B %d, %Y", "July 14, 2024"),
            @"2024-07-14",
        );
        insta::assert_snapshot!(
            p("%A, %B %d, %Y", "Wednesday, dEcEmBeR 25, 2024"),
            @"2024-12-25",
        );
    }

    #[test]
    fn ok_parse_time() {
        let p = |fmt: &str, input: &str| {
            BrokenDownTime::parse_mono(fmt.as_bytes(), input.as_bytes())
                .unwrap()
                .to_time()
                .unwrap()
        };

        insta::assert_debug_snapshot!(
            p("%H", "15"),
            @"15:00:00",
        );
        insta::assert_debug_snapshot!(
            p("%H:%M", "15:48"),
            @"15:48:00",
        );
        insta::assert_debug_snapshot!(
            p("%H:%M:%S", "15:48:59"),
            @"15:48:59",
        );
        insta::assert_debug_snapshot!(
            p("%H:%M:%S", "15:48:60"),
            @"15:48:59",
        );
        insta::assert_debug_snapshot!(
            p("%T", "15:48:59"),
            @"15:48:59",
        );

        insta::assert_debug_snapshot!(
            p("%H %p", "5 am"),
            @"05:00:00",
        );
        insta::assert_debug_snapshot!(
            p("%H%p", "5am"),
            @"05:00:00",
        );
        insta::assert_debug_snapshot!(
            p("%H%p", "11pm"),
            @"23:00:00",
        );
        insta::assert_debug_snapshot!(
            p("%I%p", "11pm"),
            @"23:00:00",
        );
        insta::assert_debug_snapshot!(
            p("%I%p", "12am"),
            @"00:00:00",
        );
        insta::assert_debug_snapshot!(
            p("%H%p", "23pm"),
            @"23:00:00",
        );
        insta::assert_debug_snapshot!(
            p("%H%p", "23am"),
            @"11:00:00",
        );
    }

    #[test]
    fn err_parse() {
        let p = |fmt: &str, input: &str| {
            BrokenDownTime::parse_mono(fmt.as_bytes(), input.as_bytes())
                .unwrap_err()
                .to_string()
        };

        insta::assert_snapshot!(
            p("%y", "999"),
            @"strptime parsing failed: %y failed: year number is invalid: parameter 'year (2 digits)' with value 999 is not in the required range of 0..=99",
        );
        insta::assert_snapshot!(
            p("%Y", "-10000"),
            @"strptime parsing failed: %Y failed: year number is invalid: parameter 'year' with value -10000 is not in the required range of -9999..=9999",
        );
        insta::assert_snapshot!(
            p("%Y", "10000"),
            @"strptime parsing failed: %Y failed: year number is invalid: parameter 'year' with value 10000 is not in the required range of -9999..=9999",
        );
        insta::assert_snapshot!(
            p("%A %m/%d/%y", "Mon 7/14/24"),
            @r###"strptime parsing failed: %A failed: unrecognized weekday abbreviation: failed to find expected choice at beginning of "Mon 7/14/24", available choices are: Sunday, Monday, Tueday, Wednesday, Thursday, Friday, Saturday"###,
        );
        insta::assert_snapshot!(
            p("%b", "Bad"),
            @r###"strptime parsing failed: %b failed: expected to find month name abbreviation, but found "Bad" instead"###,
        );
        insta::assert_snapshot!(
            p("%h", "July"),
            @r###"strptime expects to consume the entire input, but "y" remains unparsed"###,
        );
        insta::assert_snapshot!(
            p("%B", "Jul"),
            @r###"strptime parsing failed: %B failed: unrecognized month name: failed to find expected choice at beginning of "Jul", available choices are: January, February, March, April, May, June, July, August, September, October, November, December"###,
        );
        insta::assert_snapshot!(
            p("%H", "24"),
            @"strptime parsing failed: %H failed: hour number is invalid: parameter 'hour' with value 24 is not in the required range of 0..=23",
        );
        insta::assert_snapshot!(
            p("%M", "60"),
            @"strptime parsing failed: %M failed: minute number is invalid: parameter 'minute' with value 60 is not in the required range of 0..=59",
        );
        insta::assert_snapshot!(
            p("%S", "61"),
            @"strptime parsing failed: %S failed: second number is invalid: parameter 'second' with value 61 is not in the required range of 0..=59",
        );
        insta::assert_snapshot!(
            p("%I", "0"),
            @"strptime parsing failed: %I failed: hour number is invalid: parameter 'hour' with value 0 is not in the required range of 1..=12",
        );
        insta::assert_snapshot!(
            p("%I", "13"),
            @"strptime parsing failed: %I failed: hour number is invalid: parameter 'hour' with value 13 is not in the required range of 1..=12",
        );
        insta::assert_snapshot!(
            p("%p", "aa"),
            @r###"strptime parsing failed: %p failed: expected to find AM or PM, but found "aa" instead"###,
        );

        insta::assert_snapshot!(
            p("%_", " "),
            @r###"strptime parsing failed: found flag "_" after '%', and expected a directive after it, but found end of input"###,
        );
        insta::assert_snapshot!(
            p("%-", " "),
            @r###"strptime parsing failed: found flag "-" after '%', and expected a directive after it, but found end of input"###,
        );
        insta::assert_snapshot!(
            p("%0", " "),
            @r###"strptime parsing failed: found flag "0" after '%', and expected a directive after it, but found end of input"###,
        );
        insta::assert_snapshot!(
            p("%^", " "),
            @r###"strptime parsing failed: found flag "^" after '%', and expected a directive after it, but found end of input"###,
        );
        insta::assert_snapshot!(
            p("%#", " "),
            @r###"strptime parsing failed: found flag "#" after '%', and expected a directive after it, but found end of input"###,
        );
        insta::assert_snapshot!(
            p("%_1", " "),
            @r###"strptime parsing failed: found last width digit "1", and expected another width digit or a directive after it, but found end of input"###,
        );
        insta::assert_snapshot!(
            p("%_23", " "),
            @r###"strptime parsing failed: found last width digit "3", and expected another width digit or a directive after it, but found end of input"###,
        );
    }

    #[test]
    fn err_parse_date() {
        let p = |fmt: &str, input: &str| {
            BrokenDownTime::parse_mono(fmt.as_bytes(), input.as_bytes())
                .unwrap()
                .to_date()
                .unwrap_err()
                .to_string()
        };

        insta::assert_snapshot!(
            p("%Y", "2024"),
            @"parsing format did not include month directive, without it, a date cannot be created",
        );
        insta::assert_snapshot!(
            p("%m", "7"),
            @"parsing format did not include year directive, without it, a date cannot be created",
        );
        insta::assert_snapshot!(
            p("%d", "25"),
            @"parsing format did not include year directive, without it, a date cannot be created",
        );
        insta::assert_snapshot!(
            p("%Y-%m", "2024-7"),
            @"parsing format did not include day directive, without it, a date cannot be created",
        );
        insta::assert_snapshot!(
            p("%Y-%d", "2024-25"),
            @"parsing format did not include month directive, without it, a date cannot be created",
        );
        insta::assert_snapshot!(
            p("%m-%d", "7-25"),
            @"parsing format did not include year directive, without it, a date cannot be created",
        );

        insta::assert_snapshot!(
            p("%m/%d/%y", "6/31/24"),
            @"invalid date: parameter 'day' with value 31 is not in the required range of 1..=30",
        );
        insta::assert_snapshot!(
            p("%m/%d/%y", "2/29/23"),
            @"invalid date: parameter 'day' with value 29 is not in the required range of 1..=28",
        );
        insta::assert_snapshot!(
            p("%a %m/%d/%y", "Mon 7/14/24"),
            @"parsed weekday Monday does not match weekday Sunday from parsed date 2024-07-14",
        );
        insta::assert_snapshot!(
            p("%A %m/%d/%y", "Monday 7/14/24"),
            @"parsed weekday Monday does not match weekday Sunday from parsed date 2024-07-14",
        );
    }

    #[test]
    fn err_parse_time() {
        let p = |fmt: &str, input: &str| {
            BrokenDownTime::parse_mono(fmt.as_bytes(), input.as_bytes())
                .unwrap()
                .to_time()
                .unwrap_err()
                .to_string()
        };

        insta::assert_snapshot!(
            p("%M", "59"),
            @"parsing format did not include hour directive, but did include minute directive (cannot have smaller time units with bigger time units missing)",
        );
        insta::assert_snapshot!(
            p("%S", "59"),
            @"parsing format did not include hour directive, but did include second directive (cannot have smaller time units with bigger time units missing)",
        );
        insta::assert_snapshot!(
            p("%M:%S", "59:59"),
            @"parsing format did not include hour directive, but did include minute directive (cannot have smaller time units with bigger time units missing)",
        );
        insta::assert_snapshot!(
            p("%H:%S", "15:59"),
            @"parsing format did not include minute directive, but did include second directive (cannot have smaller time units with bigger time units missing)",
        );
    }
}
