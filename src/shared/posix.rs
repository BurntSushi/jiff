use alloc::string::String;

use super::{
    util::{Byte, Bytes},
    PosixDay, PosixDayTime, PosixDst, PosixRule, PosixTimeZone,
};

macro_rules! err {
    ($($tt:tt)*) => {{
        self::Error(alloc::format!($($tt)*))
    }}
}

/// An error that can be returned when parsing.
#[derive(Debug)]
pub struct Error(String);

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        core::fmt::Display::fmt(&self.0, f)
    }
}

#[cfg(feature = "alloc")]
impl PosixTimeZone<String> {
    /// Parse a POSIX `TZ` environment variable, assuming it's a rule and not
    /// an implementation defined value, from the given bytes.
    pub fn parse(bytes: &[u8]) -> Result<PosixTimeZone<String>, Error> {
        // We enable the IANA v3+ extensions here. (Namely, that the time
        // specification hour value has the range `-167..=167` instead of
        // `0..=24`.) Requiring strict POSIX rules doesn't seem necessary
        // since the extension is a strict superset. Plus, GNU tooling
        // seems to accept the extension.
        let parser =
            Parser { ianav3plus: true, ..Parser::new(bytes.as_ref()) };
        parser.parse()
    }

    /// Like parse, but parses a prefix of the input given and returns whatever
    /// is remaining.
    pub fn parse_prefix<'b>(
        bytes: &'b [u8],
    ) -> Result<(PosixTimeZone<String>, &'b [u8]), Error> {
        let parser =
            Parser { ianav3plus: true, ..Parser::new(bytes.as_ref()) };
        parser.parse_prefix()
    }
}

/// A parser for POSIX time zones.
#[derive(Debug)]
struct Parser<'s> {
    /// The `TZ` string that we're parsing.
    tz: &'s [u8],
    /// The parser's current position in `tz`.
    pos: core::cell::Cell<usize>,
    /// Whether to use IANA rules, i.e., when parsing a TZ string in a TZif
    /// file of version 3 or greater. From `tzfile(5)`:
    ///
    /// > First, the hours part of its transition times may be signed and range
    /// > from `-167` through `167` instead of the POSIX-required unsigned
    /// > values from `0` through `24`. Second, DST is in effect all year if
    /// > it starts January 1 at 00:00 and ends December 31 at 24:00 plus the
    /// > difference between daylight saving and standard time.
    ///
    /// At time of writing, I don't think I understand the significance of
    /// the second part above. (RFC 8536 elaborates that it is meant to be an
    /// explicit clarification of something that POSIX itself implies.) But the
    /// first part is clear: it permits the hours to be a bigger range.
    ianav3plus: bool,
}

impl<'s> Parser<'s> {
    /// Create a new parser for extracting a POSIX time zone from the given
    /// bytes.
    fn new<B: ?Sized + AsRef<[u8]>>(tz: &'s B) -> Parser<'s> {
        Parser {
            tz: tz.as_ref(),
            pos: core::cell::Cell::new(0),
            ianav3plus: false,
        }
    }

    /// Parses a POSIX time zone from the current position of the parser and
    /// ensures that the entire TZ string corresponds to a single valid POSIX
    /// time zone.
    fn parse(&self) -> Result<PosixTimeZone<String>, Error> {
        let (time_zone, remaining) = self.parse_prefix()?;
        if !remaining.is_empty() {
            return Err(err!(
                "expected entire TZ string to be a valid POSIX \
                 time zone, but found `{}` after what would otherwise \
                 be a valid POSIX TZ string",
                Bytes(remaining),
            ));
        }
        Ok(time_zone)
    }

    /// Parses a POSIX time zone from the current position of the parser and
    /// returns the remaining input.
    fn parse_prefix(
        &self,
    ) -> Result<(PosixTimeZone<String>, &'s [u8]), Error> {
        let time_zone = self.parse_posix_time_zone()?;
        Ok((time_zone, self.remaining()))
    }

    /// Parse a POSIX time zone from the current position of the parser.
    ///
    /// Upon success, the parser will be positioned immediately following the
    /// TZ string.
    fn parse_posix_time_zone(&self) -> Result<PosixTimeZone<String>, Error> {
        let std_abbrev = self
            .parse_abbreviation()
            .map_err(|e| err!("failed to parse standard abbreviation: {e}"))?;
        let std_offset = self
            .parse_posix_offset()
            .map_err(|e| err!("failed to parse standard offset: {e}"))?;
        let mut dst = None;
        if !self.is_done()
            && (self.byte().is_ascii_alphabetic() || self.byte() == b'<')
        {
            dst = Some(self.parse_posix_dst(std_offset)?);
        }
        Ok(PosixTimeZone { std_abbrev, std_offset, dst })
    }

    /// Parse a DST zone with an optional explicit transition rule.
    ///
    /// This assumes the parser is positioned at the first byte of the DST
    /// abbreviation.
    ///
    /// Upon success, the parser will be positioned immediately after the end
    /// of the DST transition rule (which might just be the abbreviation, but
    /// might also include explicit start/end datetime specifications).
    fn parse_posix_dst(
        &self,
        std_offset: i32,
    ) -> Result<PosixDst<String>, Error> {
        let abbrev = self
            .parse_abbreviation()
            .map_err(|e| err!("failed to parse DST abbreviation: {e}"))?;
        // This is the default: one hour ahead of standard time. We may
        // override this if the DST portion specifies an offset. (But it
        // usually doesn't.)
        let offset = std_offset + 3600;
        let mut dst = PosixDst { abbrev, offset, rule: None };
        if self.is_done() {
            return Ok(dst);
        }
        if self.byte() != b',' {
            dst.offset = self
                .parse_posix_offset()
                .map_err(|e| err!("failed to parse DST offset: {e}"))?;
            if self.is_done() {
                return Ok(dst);
            }
        }
        if self.byte() != b',' {
            return Err(err!(
                "after parsing DST offset in POSIX time zone string, \
                 found `{}` but expected a ','",
                Byte(self.byte()),
            ));
        }
        if !self.bump() {
            return Err(err!(
                "after parsing DST offset in POSIX time zone string, \
                 found end of string after a trailing ','",
            ));
        }
        dst.rule = Some(self.parse_rule()?);
        Ok(dst)
    }

    /// Parse a time zone abbreviation.
    ///
    /// This assumes the parser is positioned at the first byte of
    /// the abbreviation. This is either the first character in the
    /// abbreviation, or the opening quote of a quoted abbreviation.
    ///
    /// Upon success, the parser will be positioned immediately following
    /// the abbreviation name.
    ///
    /// The string returned is guaranteed to be no more than 30 bytes.
    /// (This restriction is somewhat arbitrary, but it's so we can put
    /// the abbreviation in a fixed capacity array.)
    fn parse_abbreviation(&self) -> Result<String, Error> {
        if self.byte() == b'<' {
            if !self.bump() {
                return Err(err!(
                    "found opening '<' quote for abbreviation in \
                         POSIX time zone string, and expected a name \
                         following it, but found the end of string instead"
                ));
            }
            self.parse_quoted_abbreviation()
        } else {
            self.parse_unquoted_abbreviation()
        }
    }

    /// Parses an unquoted time zone abbreviation.
    ///
    /// This assumes the parser is position at the first byte in the
    /// abbreviation.
    ///
    /// Upon success, the parser will be positioned immediately after the
    /// last byte in the abbreviation.
    ///
    /// The string returned is guaranteed to be no more than 30 bytes.
    /// (This restriction is somewhat arbitrary, but it's so we can put
    /// the abbreviation in a fixed capacity array.)
    fn parse_unquoted_abbreviation(&self) -> Result<String, Error> {
        const MAX_LEN: usize = 30;

        let start = self.pos();
        for i in 0.. {
            if !self.byte().is_ascii_alphabetic() {
                break;
            }
            if i >= MAX_LEN {
                return Err(err!(
                    "expected abbreviation with at most {MAX_LEN} bytes, \
                         but found a longer abbreviation beginning with `{}`",
                    Bytes(&self.tz[start..i]),
                ));
            }
            if !self.bump() {
                break;
            }
        }
        let end = self.pos();
        let abbrev =
            core::str::from_utf8(&self.tz[start..end]).map_err(|_| {
                // NOTE: I believe this error is technically impossible
                // since the loop above restricts letters in an
                // abbreviation to ASCII. So everything from `start` to
                // `end` is ASCII and thus should be UTF-8. But it doesn't
                // cost us anything to report an error here in case the
                // code above evolves somehow.
                err!(
                    "found abbreviation `{}`, but it is not valid UTF-8",
                    Bytes(&self.tz[start..end]),
                )
            })?;
        if abbrev.len() < 3 {
            return Err(err!(
                "expected abbreviation with 3 or more bytes, but found \
                     abbreviation {:?} with {} bytes",
                abbrev,
                abbrev.len(),
            ));
        }
        Ok(String::from(abbrev))
    }

    /// Parses a quoted time zone abbreviation.
    ///
    /// This assumes the parser is positioned immediately after the opening
    /// `<` quote. That is, at the first byte in the abbreviation.
    ///
    /// Upon success, the parser will be positioned immediately after the
    /// closing `>` quote.
    ///
    /// The string returned is guaranteed to be no more than 30 bytes.
    /// (This restriction is somewhat arbitrary, but it's so we can put
    /// the abbreviation in a fixed capacity array.)
    fn parse_quoted_abbreviation(&self) -> Result<String, Error> {
        const MAX_LEN: usize = 30;

        let start = self.pos();
        for i in 0.. {
            if !self.byte().is_ascii_alphanumeric()
                && self.byte() != b'+'
                && self.byte() != b'-'
            {
                break;
            }
            if i >= MAX_LEN {
                return Err(err!(
                    "expected abbreviation with at most {MAX_LEN} bytes, \
                         but found a longer abbreviation beginning with `{}`",
                    Bytes(&self.tz[start..i]),
                ));
            }
            if !self.bump() {
                break;
            }
        }
        let end = self.pos();
        let abbrev =
            core::str::from_utf8(&self.tz[start..end]).map_err(|_| {
                // NOTE: I believe this error is technically impossible
                // since the loop above restricts letters in an
                // abbreviation to ASCII. So everything from `start` to
                // `end` is ASCII and thus should be UTF-8. But it doesn't
                // cost us anything to report an error here in case the
                // code above evolves somehow.
                err!(
                    "found abbreviation `{}`, but it is not valid UTF-8",
                    Bytes(&self.tz[start..end]),
                )
            })?;
        if self.is_done() {
            return Err(err!(
                "found non-empty quoted abbreviation {abbrev:?}, but \
                     did not find expected end-of-quoted abbreviation \
                     '>' character",
            ));
        }
        if self.byte() != b'>' {
            return Err(err!(
                "found non-empty quoted abbreviation {abbrev:?}, but \
                     found `{}` instead of end-of-quoted abbreviation '>' \
                     character",
                Byte(self.byte()),
            ));
        }
        self.bump();
        if abbrev.len() < 3 {
            return Err(err!(
                "expected abbreviation with 3 or more bytes, but found \
                     abbreviation {abbrev:?} with {} bytes",
                abbrev.len(),
            ));
        }
        Ok(String::from(abbrev))
    }

    /// Parse a POSIX time offset.
    ///
    /// This assumes the parser is positioned at the first byte of the
    /// offset. This can either be a digit (for a positive offset) or the
    /// sign of the offset (which must be either `-` or `+`).
    ///
    /// Upon success, the parser will be positioned immediately after the
    /// end of the offset.
    fn parse_posix_offset(&self) -> Result<i32, Error> {
        let sign = self
            .parse_optional_sign()
            .map_err(|e| {
                err!(
                    "failed to parse sign for time offset \
                     in POSIX time zone string: {e}",
                )
            })?
            .unwrap_or(1);
        let hour = self.parse_hour_posix()?;
        let (mut minute, mut second) = (0, 0);
        if self.maybe_byte() == Some(b':') {
            if !self.bump() {
                return Err(err!(
                    "incomplete time in POSIX timezone (missing minutes)",
                ));
            }
            minute = self.parse_minute()?;
            if self.maybe_byte() == Some(b':') {
                if !self.bump() {
                    return Err(err!(
                        "incomplete time in POSIX timezone (missing seconds)",
                    ));
                }
                second = self.parse_second()?;
            }
        }
        let mut seconds = i32::from(hour) * 3600;
        seconds += i32::from(minute) * 60;
        seconds += i32::from(second);
        // Yes, we flip the sign, because POSIX is backwards.
        // For example, `EST5` corresponds to `-05:00`.
        seconds *= i32::from(-sign);
        // Must be true because the parsing routines for hours, minutes
        // and seconds enforce they are in the ranges -24..=24, 0..=59
        // and 0..=59, respectively.
        assert!(
            -89999 <= seconds && seconds <= 89999,
            "offset seconds {seconds} is out of range"
        );
        Ok(seconds)
    }

    /// Parses a POSIX DST transition rule.
    ///
    /// This assumes the parser is positioned at the first byte in the
    /// rule. That is, it comes immediately after the DST abbreviation or
    /// its optional offset.
    ///
    /// Upon success, the parser will be positioned immediately after the
    /// DST transition rule. In typical cases, this corresponds to the end
    /// of the TZ string.
    fn parse_rule(&self) -> Result<PosixRule, Error> {
        let start = self.parse_posix_datetime_spec().map_err(|e| {
            err!("failed to parse start of DST transition rule: {e}")
        })?;
        if self.maybe_byte() != Some(b',') || !self.bump() {
            return Err(err!(
                "expected end of DST rule after parsing the start \
                 of the DST rule"
            ));
        }
        let end = self.parse_posix_datetime_spec().map_err(|e| {
            err!("failed to parse end of DST transition rule: {e}")
        })?;
        Ok(PosixRule { start, end })
    }

    /// Parses a POSIX datetime specification.
    ///
    /// This assumes the parser is position at the first byte where a
    /// datetime specification is expected to occur.
    ///
    /// Upon success, the parser will be positioned after the datetime
    /// specification. This will either be immediately after the date, or
    /// if it's present, the time part of the specification.
    fn parse_posix_datetime_spec(&self) -> Result<PosixDayTime, Error> {
        let mut daytime = PosixDayTime {
            date: self.parse_posix_date_spec()?,
            time: 2 * 3600, // the default if the time is absent
        };
        if self.maybe_byte() != Some(b'/') {
            return Ok(daytime);
        }
        if !self.bump() {
            return Err(err!(
                "expected time specification after '/' following a date
                 specification in a POSIX time zone DST transition rule",
            ));
        }
        daytime.time = self.parse_posix_time_spec()?;
        Ok(daytime)
    }

    /// Parses a POSIX date specification.
    ///
    /// This assumes the parser is positioned at the first byte of the date
    /// specification. This can be `J` (for one based Julian day without
    /// leap days), `M` (for "weekday of month") or a digit starting the
    /// zero based Julian day with leap days. This routine will validate
    /// that the position points to one of these possible values. That is,
    /// the caller doesn't need to parse the `M` or the `J` or the leading
    /// digit. The caller should just call this routine when it *expect* a
    /// date specification to follow.
    ///
    /// Upon success, the parser will be positioned immediately after the
    /// date specification.
    fn parse_posix_date_spec(&self) -> Result<PosixDay, Error> {
        match self.byte() {
            b'J' => {
                if !self.bump() {
                    return Err(err!(
                        "expected one-based Julian day after 'J' in date \
                         specification of a POSIX time zone DST \
                         transition rule, but got the end of the string \
                         instead"
                    ));
                }
                Ok(PosixDay::JulianOne(self.parse_posix_julian_day_no_leap()?))
            }
            b'0'..=b'9' => Ok(PosixDay::JulianZero(
                self.parse_posix_julian_day_with_leap()?,
            )),
            b'M' => {
                if !self.bump() {
                    return Err(err!(
                        "expected month-week-weekday after 'M' in date \
                         specification of a POSIX time zone DST \
                         transition rule, but got the end of the string \
                         instead"
                    ));
                }
                let (month, week, weekday) = self.parse_weekday_of_month()?;
                Ok(PosixDay::WeekdayOfMonth { month, week, weekday })
            }
            _ => Err(err!(
                "expected 'J', a digit or 'M' at the beginning of a date \
                 specification of a POSIX time zone DST transition rule, \
                 but got `{}` instead",
                Byte(self.byte()),
            )),
        }
    }

    /// Parses a POSIX Julian day that does not include leap days
    /// (`1 <= n <= 365`).
    ///
    /// This assumes the parser is positioned just after the `J` and at the
    /// first digit of the Julian day. Upon success, the parser will be
    /// positioned immediately following the day number.
    fn parse_posix_julian_day_no_leap(&self) -> Result<i16, Error> {
        let number = self
            .parse_number_with_upto_n_digits(3)
            .map_err(|e| err!("invalid one based Julian day: {e}"))?;
        let number = i16::try_from(number).map_err(|_| {
            err!(
                "one based Julian day `{number}` in POSIX time zone \
                 does not fit into 16-bit integer"
            )
        })?;
        if !(1 <= number && number <= 365) {
            return Err(err!(
                "parsed one based Julian day `{number}`, \
                 but one based Julian day in POSIX time zone \
                 must be in range 1..=365",
            ));
        }
        Ok(number)
    }

    /// Parses a POSIX Julian day that includes leap days (`0 <= n <=
    /// 365`).
    ///
    /// This assumes the parser is positioned at the first digit of the
    /// Julian day. Upon success, the parser will be positioned immediately
    /// following the day number.
    fn parse_posix_julian_day_with_leap(&self) -> Result<i16, Error> {
        let number = self
            .parse_number_with_upto_n_digits(3)
            .map_err(|e| err!("invalid zero based Julian day: {e}"))?;
        let number = i16::try_from(number).map_err(|_| {
            err!(
                "zero based Julian day `{number}` in POSIX time zone \
                 does not fit into 16-bit integer"
            )
        })?;
        if !(0 <= number && number <= 365) {
            return Err(err!(
                "parsed zero based Julian day `{number}`, \
                 but zero based Julian day in POSIX time zone \
                 must be in range 0..=365",
            ));
        }
        Ok(number)
    }

    /// Parses a POSIX "weekday of month" specification.
    ///
    /// This assumes the parser is positioned just after the `M` byte and
    /// at the first digit of the month. Upon success, the parser will be
    /// positioned immediately following the "weekday of the month" that
    /// was parsed.
    ///
    /// The tuple returned is month (1..=12), week (1..=5) and weekday
    /// (0..=6 with 0=Sunday).
    fn parse_weekday_of_month(&self) -> Result<(i8, i8, i8), Error> {
        let month = self.parse_month()?;
        if self.maybe_byte() != Some(b'.') {
            return Err(err!(
                "expected '.' after month `{month}` in \
                 POSIX time zone rule"
            ));
        }
        if !self.bump() {
            return Err(err!(
                "expected week after month `{month}` in \
                 POSIX time zone rule"
            ));
        }
        let week = self.parse_week()?;
        if self.maybe_byte() != Some(b'.') {
            return Err(err!(
                "expected '.' after week `{week}` in POSIX time zone rule"
            ));
        }
        if !self.bump() {
            return Err(err!(
                "expected day-of-week after week `{week}` in \
                 POSIX time zone rule"
            ));
        }
        let weekday = self.parse_weekday()?;
        Ok((month, week, weekday))
    }

    /// This parses a POSIX time specification in the format
    /// `[+/-]hh?[:mm[:ss]]`.
    ///
    /// This assumes the parser is positioned at the first `h` (or the
    /// sign, if present). Upon success, the parser will be positioned
    /// immediately following the end of the time specification.
    fn parse_posix_time_spec(&self) -> Result<i32, Error> {
        let (sign, hour) = if self.ianav3plus {
            let sign = self
                .parse_optional_sign()
                .map_err(|e| {
                    err!(
                        "failed to parse sign for transition time \
                         in POSIX time zone string: {e}",
                    )
                })?
                .unwrap_or(1);
            let hour = self.parse_hour_ianav3plus()?;
            (sign, hour)
        } else {
            (1, i16::from(self.parse_hour_posix()?))
        };
        let (mut minute, mut second) = (0, 0);
        if self.maybe_byte() == Some(b':') {
            if !self.bump() {
                return Err(err!(
                    "incomplete transition time in \
                     POSIX time zone string (missing minutes)",
                ));
            }
            minute = self.parse_minute()?;
            if self.maybe_byte() == Some(b':') {
                if !self.bump() {
                    return Err(err!(
                        "incomplete transition time in \
                         POSIX time zone string (missing seconds)",
                    ));
                }
                second = self.parse_second()?;
            }
        }
        let mut seconds = i32::from(hour) * 3600;
        seconds += i32::from(minute) * 60;
        seconds += i32::from(second);
        seconds *= i32::from(sign);
        // Must be true because the parsing routines for hours, minutes
        // and seconds enforce they are in the ranges -167..=167, 0..=59
        // and 0..=59, respectively.
        assert!(-604799 <= seconds && seconds <= 604799);
        Ok(seconds)
    }

    /// Parses a month.
    ///
    /// This is expected to be positioned at the first digit. Upon success,
    /// the parser will be positioned after the month (which may contain
    /// two digits).
    fn parse_month(&self) -> Result<i8, Error> {
        let number = self.parse_number_with_upto_n_digits(2)?;
        let number = i8::try_from(number).map_err(|_| {
            err!(
                "month `{number}` in POSIX time zone \
                 does not fit into 8-bit integer"
            )
        })?;
        if !(1 <= number && number <= 12) {
            return Err(err!(
                "parsed month `{number}`, but month in \
                 POSIX time zone must be in range 1..=12",
            ));
        }
        Ok(number)
    }

    /// Parses a week-of-month number.
    ///
    /// This is expected to be positioned at the first digit. Upon success,
    /// the parser will be positioned after the week digit.
    fn parse_week(&self) -> Result<i8, Error> {
        let number = self.parse_number_with_exactly_n_digits(1)?;
        let number = i8::try_from(number).map_err(|_| {
            err!(
                "week `{number}` in POSIX time zone \
                 does not fit into 8-bit integer"
            )
        })?;
        if !(1 <= number && number <= 5) {
            return Err(err!(
                "parsed week `{number}`, but week in \
                 POSIX time zone must be in range 1..=5"
            ));
        }
        Ok(number)
    }

    /// Parses a weekday number.
    ///
    /// This is expected to be positioned at the first digit. Upon success,
    /// the parser will be positioned after the week digit.
    ///
    /// The weekday returned is guaranteed to be in the range `0..=6`, with
    /// `0` corresponding to Sunday.
    fn parse_weekday(&self) -> Result<i8, Error> {
        let number = self.parse_number_with_exactly_n_digits(1)?;
        let number = i8::try_from(number).map_err(|_| {
            err!(
                "weekday `{number}` in POSIX time zone \
                 does not fit into 8-bit integer"
            )
        })?;
        if !(0 <= number && number <= 6) {
            return Err(err!(
                "parsed weekday `{number}`, but weekday in \
                 POSIX time zone must be in range `0..=6` \
                 (with `0` corresponding to Sunday)",
            ));
        }
        Ok(number)
    }

    /// Parses an hour from a POSIX time specification with the IANA
    /// v3+ extension. That is, the hour may be in the range `0..=167`.
    /// (Callers should parse an optional sign preceding the hour digits
    /// when IANA V3+ parsing is enabled.)
    ///
    /// The hour is allowed to be a single digit (unlike minutes or
    /// seconds).
    ///
    /// This assumes the parser is positioned at the position where the
    /// first hour digit should occur. Upon success, the parser will be
    /// positioned immediately after the last hour digit.
    fn parse_hour_ianav3plus(&self) -> Result<i16, Error> {
        // Callers should only be using this method when IANA v3+ parsing
        // is enabled.
        assert!(self.ianav3plus);
        let number = self
            .parse_number_with_upto_n_digits(3)
            .map_err(|e| err!("invalid hour digits: {e}"))?;
        let number = i16::try_from(number).map_err(|_| {
            err!(
                "hour `{number}` in POSIX time zone \
                 does not fit into 16-bit integer"
            )
        })?;
        if !(0 <= number && number <= 167) {
            // The error message says -167 but the check above uses 0.
            // This is because the caller is responsible for parsing
            // the sign.
            return Err(err!(
                "parsed hour `{number}`, but hour in IANA v3+ \
                 POSIX time zone must be in range `-167..=167`",
            ));
        }
        Ok(number)
    }

    /// Parses an hour from a POSIX time specification, with the allowed
    /// range being `0..=24`.
    ///
    /// The hour is allowed to be a single digit (unlike minutes or
    /// seconds).
    ///
    /// This assumes the parser is positioned at the position where the
    /// first hour digit should occur. Upon success, the parser will be
    /// positioned immediately after the last hour digit.
    fn parse_hour_posix(&self) -> Result<i8, Error> {
        let number = self
            .parse_number_with_upto_n_digits(2)
            .map_err(|e| err!("invalid hour digits: {e}"))?;
        let number = i8::try_from(number).map_err(|_| {
            err!(
                "hour `{number}` in POSIX time zone \
                 does not fit into 8-bit integer"
            )
        })?;
        if !(0 <= number && number <= 24) {
            return Err(err!(
                "parsed hour `{number}`, but hour in \
                 POSIX time zone must be in range `0..=24`",
            ));
        }
        Ok(number)
    }

    /// Parses a minute from a POSIX time specification.
    ///
    /// The minute must be exactly two digits.
    ///
    /// This assumes the parser is positioned at the position where the
    /// first minute digit should occur. Upon success, the parser will be
    /// positioned immediately after the second minute digit.
    fn parse_minute(&self) -> Result<i8, Error> {
        let number = self
            .parse_number_with_exactly_n_digits(2)
            .map_err(|e| err!("invalid minute digits: {e}"))?;
        let number = i8::try_from(number).map_err(|_| {
            err!(
                "minute `{number}` in POSIX time zone \
                 does not fit into 8-bit integer"
            )
        })?;
        if !(0 <= number && number <= 59) {
            return Err(err!(
                "parsed minute `{number}`, but minute in \
                 POSIX time zone must be in range `0..=59`",
            ));
        }
        Ok(number)
    }

    /// Parses a second from a POSIX time specification.
    ///
    /// The second must be exactly two digits.
    ///
    /// This assumes the parser is positioned at the position where the
    /// first second digit should occur. Upon success, the parser will be
    /// positioned immediately after the second second digit.
    fn parse_second(&self) -> Result<i8, Error> {
        let number = self
            .parse_number_with_exactly_n_digits(2)
            .map_err(|e| err!("invalid second digits: {e}"))?;
        let number = i8::try_from(number).map_err(|_| {
            err!(
                "second `{number}` in POSIX time zone \
                 does not fit into 8-bit integer"
            )
        })?;
        if !(0 <= number && number <= 59) {
            return Err(err!(
                "parsed second `{number}`, but second in \
                 POSIX time zone must be in range `0..=59`",
            ));
        }
        Ok(number)
    }

    /// Parses a signed 64-bit integer expressed in exactly `n` digits.
    ///
    /// If `n` digits could not be found (or if the `TZ` string ends before
    /// `n` digits could be found), then this returns an error.
    ///
    /// This assumes that `n >= 1` and that the parser is positioned at the
    /// first digit. Upon success, the parser is positioned immediately
    /// after the `n`th digit.
    fn parse_number_with_exactly_n_digits(
        &self,
        n: usize,
    ) -> Result<i32, Error> {
        assert!(n >= 1, "numbers must have at least 1 digit");
        let start = self.pos();
        let mut number: i32 = 0;
        for i in 0..n {
            if self.is_done() {
                return Err(err!("expected {n} digits, but found {i}"));
            }
            let byte = self.byte();
            let digit = match byte.checked_sub(b'0') {
                None => {
                    return Err(err!(
                        "invalid digit, expected 0-9 but got {}",
                        Byte(byte),
                    ));
                }
                Some(digit) if digit > 9 => {
                    return Err(err!(
                        "invalid digit, expected 0-9 but got {}",
                        Byte(byte),
                    ))
                }
                Some(digit) => {
                    debug_assert!((0..=9).contains(&digit));
                    i32::from(digit)
                }
            };
            number = number
                .checked_mul(10)
                .and_then(|n| n.checked_add(digit))
                .ok_or_else(|| {
                    err!(
                        "number `{}` too big to parse into 64-bit integer",
                        Bytes(&self.tz[start..i]),
                    )
                })?;
            self.bump();
        }
        Ok(number)
    }

    /// Parses a signed 64-bit integer expressed with up to `n` digits and
    /// at least 1 digit.
    ///
    /// This assumes that `n >= 1` and that the parser is positioned at the
    /// first digit. Upon success, the parser is position immediately after
    /// the last digit (which can be at most `n`).
    fn parse_number_with_upto_n_digits(&self, n: usize) -> Result<i32, Error> {
        assert!(n >= 1, "numbers must have at least 1 digit");
        let start = self.pos();
        let mut number: i32 = 0;
        for i in 0..n {
            if self.is_done() || !self.byte().is_ascii_digit() {
                if i == 0 {
                    return Err(err!("invalid number, no digits found"));
                }
                break;
            }
            let digit = i32::from(self.byte() - b'0');
            number = number
                .checked_mul(10)
                .and_then(|n| n.checked_add(digit))
                .ok_or_else(|| {
                    err!(
                        "number `{}` too big to parse into 64-bit integer",
                        Bytes(&self.tz[start..i]),
                    )
                })?;
            self.bump();
        }
        Ok(number)
    }

    /// Parses an optional sign.
    ///
    /// This assumes the parser is positioned at the position where a
    /// positive or negative sign is permitted. If one exists, then it
    /// is consumed and returned. Moreover, if one exists, then this
    /// guarantees that it is not the last byte in the input. That is, upon
    /// success, it is valid to call `self.byte()`.
    fn parse_optional_sign(&self) -> Result<Option<i8>, Error> {
        if self.is_done() {
            return Ok(None);
        }
        Ok(match self.byte() {
            b'-' => {
                if !self.bump() {
                    return Err(err!(
                        "expected digit after '-' sign, \
                         but got end of input",
                    ));
                }
                Some(-1)
            }
            b'+' => {
                if !self.bump() {
                    return Err(err!(
                        "expected digit after '+' sign, \
                         but got end of input",
                    ));
                }
                Some(1)
            }
            _ => None,
        })
    }
}

/// Helper routines for parsing a POSIX `TZ` string.
impl<'s> Parser<'s> {
    /// Bump the parser to the next byte.
    ///
    /// If the end of the input has been reached, then `false` is returned.
    fn bump(&self) -> bool {
        if self.is_done() {
            return false;
        }
        self.pos.set(
            self.pos().checked_add(1).expect("pos cannot overflow usize"),
        );
        !self.is_done()
    }

    /// Returns true if the next call to `bump` would return false.
    fn is_done(&self) -> bool {
        self.pos() == self.tz.len()
    }

    /// Return the byte at the current position of the parser.
    ///
    /// This panics if the parser is positioned at the end of the TZ
    /// string.
    fn byte(&self) -> u8 {
        self.tz[self.pos()]
    }

    /// Return the byte at the current position of the parser. If the TZ
    /// string has been exhausted, then this returns `None`.
    fn maybe_byte(&self) -> Option<u8> {
        self.tz.get(self.pos()).copied()
    }

    /// Return the current byte offset of the parser.
    ///
    /// The offset starts at `0` from the beginning of the TZ string.
    fn pos(&self) -> usize {
        self.pos.get()
    }

    /// Returns the remaining bytes of the TZ string.
    ///
    /// This includes `self.byte()`. It may be empty.
    fn remaining(&self) -> &'s [u8] {
        &self.tz[self.pos()..]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parser(s: &str) -> Parser<'_> {
        Parser::new(s.as_bytes())
    }

    #[test]
    fn parse() {
        let p = parser("NZST-12NZDT,J60,J300");
        assert_eq!(
            p.parse().unwrap(),
            PosixTimeZone {
                std_abbrev: "NZST".into(),
                std_offset: 12 * 60 * 60,
                dst: Some(PosixDst {
                    abbrev: "NZDT".into(),
                    offset: 13 * 60 * 60,
                    rule: Some(PosixRule {
                        start: PosixDayTime {
                            date: PosixDay::JulianOne(60),
                            time: 2 * 60 * 60,
                        },
                        end: PosixDayTime {
                            date: PosixDay::JulianOne(300),
                            time: 2 * 60 * 60,
                        },
                    }),
                }),
            },
        );

        let p = Parser::new("NZST-12NZDT,J60,J300WAT");
        assert!(p.parse().is_err());
    }

    #[test]
    fn parse_posix_time_zone() {
        let p = Parser::new("NZST-12NZDT,M9.5.0,M4.1.0/3");
        assert_eq!(
            p.parse_posix_time_zone().unwrap(),
            PosixTimeZone {
                std_abbrev: "NZST".into(),
                std_offset: 12 * 60 * 60,
                dst: Some(PosixDst {
                    abbrev: "NZDT".into(),
                    offset: 13 * 60 * 60,
                    rule: Some(PosixRule {
                        start: PosixDayTime {
                            date: PosixDay::WeekdayOfMonth {
                                month: 9,
                                week: 5,
                                weekday: 0,
                            },
                            time: 2 * 60 * 60,
                        },
                        end: PosixDayTime {
                            date: PosixDay::WeekdayOfMonth {
                                month: 4,
                                week: 1,
                                weekday: 0,
                            },
                            time: 3 * 60 * 60,
                        },
                    })
                }),
            },
        );

        let p = Parser::new("NZST-12NZDT,M9.5.0,M4.1.0/3WAT");
        assert_eq!(
            p.parse_posix_time_zone().unwrap(),
            PosixTimeZone {
                std_abbrev: "NZST".into(),
                std_offset: 12 * 60 * 60,
                dst: Some(PosixDst {
                    abbrev: "NZDT".into(),
                    offset: 13 * 60 * 60,
                    rule: Some(PosixRule {
                        start: PosixDayTime {
                            date: PosixDay::WeekdayOfMonth {
                                month: 9,
                                week: 5,
                                weekday: 0,
                            },
                            time: 2 * 60 * 60,
                        },
                        end: PosixDayTime {
                            date: PosixDay::WeekdayOfMonth {
                                month: 4,
                                week: 1,
                                weekday: 0,
                            },
                            time: 3 * 60 * 60,
                        },
                    })
                }),
            },
        );

        let p = Parser::new("NZST-12NZDT,J60,J300");
        assert_eq!(
            p.parse_posix_time_zone().unwrap(),
            PosixTimeZone {
                std_abbrev: "NZST".into(),
                std_offset: 12 * 60 * 60,
                dst: Some(PosixDst {
                    abbrev: "NZDT".into(),
                    offset: 13 * 60 * 60,
                    rule: Some(PosixRule {
                        start: PosixDayTime {
                            date: PosixDay::JulianOne(60),
                            time: 2 * 60 * 60,
                        },
                        end: PosixDayTime {
                            date: PosixDay::JulianOne(300),
                            time: 2 * 60 * 60,
                        },
                    }),
                }),
            },
        );

        let p = Parser::new("NZST-12NZDT,J60,J300WAT");
        assert_eq!(
            p.parse_posix_time_zone().unwrap(),
            PosixTimeZone {
                std_abbrev: "NZST".into(),
                std_offset: 12 * 60 * 60,
                dst: Some(PosixDst {
                    abbrev: "NZDT".into(),
                    offset: 13 * 60 * 60,
                    rule: Some(PosixRule {
                        start: PosixDayTime {
                            date: PosixDay::JulianOne(60),
                            time: 2 * 60 * 60,
                        },
                        end: PosixDayTime {
                            date: PosixDay::JulianOne(300),
                            time: 2 * 60 * 60,
                        },
                    }),
                }),
            },
        );
    }

    #[test]
    fn parse_posix_dst() {
        let p = Parser::new("NZDT,M9.5.0,M4.1.0/3");
        assert_eq!(
            p.parse_posix_dst(12 * 60 * 60).unwrap(),
            PosixDst {
                abbrev: "NZDT".into(),
                offset: 13 * 60 * 60,
                rule: Some(PosixRule {
                    start: PosixDayTime {
                        date: PosixDay::WeekdayOfMonth {
                            month: 9,
                            week: 5,
                            weekday: 0,
                        },
                        time: 2 * 60 * 60,
                    },
                    end: PosixDayTime {
                        date: PosixDay::WeekdayOfMonth {
                            month: 4,
                            week: 1,
                            weekday: 0,
                        },
                        time: 3 * 60 * 60,
                    },
                }),
            },
        );

        let p = Parser::new("NZDT,J60,J300");
        assert_eq!(
            p.parse_posix_dst(12 * 60 * 60).unwrap(),
            PosixDst {
                abbrev: "NZDT".into(),
                offset: 13 * 60 * 60,
                rule: Some(PosixRule {
                    start: PosixDayTime {
                        date: PosixDay::JulianOne(60),
                        time: 2 * 60 * 60,
                    },
                    end: PosixDayTime {
                        date: PosixDay::JulianOne(300),
                        time: 2 * 60 * 60,
                    },
                }),
            },
        );

        let p = Parser::new("NZDT-7,J60,J300");
        assert_eq!(
            p.parse_posix_dst(12 * 60 * 60).unwrap(),
            PosixDst {
                abbrev: "NZDT".into(),
                offset: 7 * 60 * 60,
                rule: Some(PosixRule {
                    start: PosixDayTime {
                        date: PosixDay::JulianOne(60),
                        time: 2 * 60 * 60,
                    },
                    end: PosixDayTime {
                        date: PosixDay::JulianOne(300),
                        time: 2 * 60 * 60,
                    },
                }),
            },
        );

        let p = Parser::new("NZDT+7,J60,J300");
        assert_eq!(
            p.parse_posix_dst(12 * 60 * 60).unwrap(),
            PosixDst {
                abbrev: "NZDT".into(),
                offset: -7 * 60 * 60,
                rule: Some(PosixRule {
                    start: PosixDayTime {
                        date: PosixDay::JulianOne(60),
                        time: 2 * 60 * 60,
                    },
                    end: PosixDayTime {
                        date: PosixDay::JulianOne(300),
                        time: 2 * 60 * 60,
                    },
                }),
            },
        );

        let p = Parser::new("NZDT7,J60,J300");
        assert_eq!(
            p.parse_posix_dst(12 * 60 * 60).unwrap(),
            PosixDst {
                abbrev: "NZDT".into(),
                offset: -7 * 60 * 60,
                rule: Some(PosixRule {
                    start: PosixDayTime {
                        date: PosixDay::JulianOne(60),
                        time: 2 * 60 * 60,
                    },
                    end: PosixDayTime {
                        date: PosixDay::JulianOne(300),
                        time: 2 * 60 * 60,
                    },
                }),
            },
        );

        let p = Parser::new("NZDT7,");
        assert!(p.parse_posix_dst(12 * 60 * 60).is_err());

        let p = Parser::new("NZDT7!");
        assert!(p.parse_posix_dst(12 * 60 * 60).is_err());
    }

    #[test]
    fn parse_abbreviation() {
        let p = Parser::new("ABC");
        assert_eq!(p.parse_abbreviation().unwrap(), "ABC");

        let p = Parser::new("<ABC>");
        assert_eq!(p.parse_abbreviation().unwrap(), "ABC");

        let p = Parser::new("<+09>");
        assert_eq!(p.parse_abbreviation().unwrap(), "+09");

        let p = Parser::new("+09");
        assert!(p.parse_abbreviation().is_err());
    }

    #[test]
    fn parse_unquoted_abbreviation() {
        let p = Parser::new("ABC");
        assert_eq!(p.parse_unquoted_abbreviation().unwrap(), "ABC");

        let p = Parser::new("ABCXYZ");
        assert_eq!(p.parse_unquoted_abbreviation().unwrap(), "ABCXYZ");

        let p = Parser::new("ABC123");
        assert_eq!(p.parse_unquoted_abbreviation().unwrap(), "ABC");

        let tz = "a".repeat(30);
        let p = Parser::new(&tz);
        assert_eq!(p.parse_unquoted_abbreviation().unwrap(), &*tz);

        let p = Parser::new("a");
        assert!(p.parse_unquoted_abbreviation().is_err());

        let p = Parser::new("ab");
        assert!(p.parse_unquoted_abbreviation().is_err());

        let p = Parser::new("ab1");
        assert!(p.parse_unquoted_abbreviation().is_err());

        let tz = "a".repeat(31);
        let p = Parser::new(&tz);
        assert!(p.parse_unquoted_abbreviation().is_err());

        let p = Parser::new(b"ab\xFFcd");
        assert!(p.parse_unquoted_abbreviation().is_err());
    }

    #[test]
    fn parse_quoted_abbreviation() {
        // The inputs look a little funny here, but that's because
        // 'parse_quoted_abbreviation' starts after the opening quote
        // has been parsed.

        let p = Parser::new("ABC>");
        assert_eq!(p.parse_quoted_abbreviation().unwrap(), "ABC");

        let p = Parser::new("ABCXYZ>");
        assert_eq!(p.parse_quoted_abbreviation().unwrap(), "ABCXYZ");

        let p = Parser::new("ABC>123");
        assert_eq!(p.parse_quoted_abbreviation().unwrap(), "ABC");

        let p = Parser::new("ABC123>");
        assert_eq!(p.parse_quoted_abbreviation().unwrap(), "ABC123");

        let p = Parser::new("ab1>");
        assert_eq!(p.parse_quoted_abbreviation().unwrap(), "ab1");

        let p = Parser::new("+09>");
        assert_eq!(p.parse_quoted_abbreviation().unwrap(), "+09");

        let p = Parser::new("-09>");
        assert_eq!(p.parse_quoted_abbreviation().unwrap(), "-09");

        let tz = alloc::format!("{}>", "a".repeat(30));
        let p = Parser::new(&tz);
        assert_eq!(
            p.parse_quoted_abbreviation().unwrap(),
            tz.trim_end_matches(">")
        );

        let p = Parser::new("a>");
        assert!(p.parse_quoted_abbreviation().is_err());

        let p = Parser::new("ab>");
        assert!(p.parse_quoted_abbreviation().is_err());

        let tz = alloc::format!("{}>", "a".repeat(31));
        let p = Parser::new(&tz);
        assert!(p.parse_quoted_abbreviation().is_err());

        let p = Parser::new(b"ab\xFFcd>");
        assert!(p.parse_quoted_abbreviation().is_err());

        let p = Parser::new("ABC");
        assert!(p.parse_quoted_abbreviation().is_err());

        let p = Parser::new("ABC!>");
        assert!(p.parse_quoted_abbreviation().is_err());
    }

    #[test]
    fn parse_posix_offset() {
        let p = Parser::new("5");
        assert_eq!(p.parse_posix_offset().unwrap(), -5 * 60 * 60);

        let p = Parser::new("+5");
        assert_eq!(p.parse_posix_offset().unwrap(), -5 * 60 * 60);

        let p = Parser::new("-5");
        assert_eq!(p.parse_posix_offset().unwrap(), 5 * 60 * 60);

        let p = Parser::new("-12:34:56");
        assert_eq!(
            p.parse_posix_offset().unwrap(),
            12 * 60 * 60 + 34 * 60 + 56,
        );

        let p = Parser::new("a");
        assert!(p.parse_posix_offset().is_err());

        let p = Parser::new("-");
        assert!(p.parse_posix_offset().is_err());

        let p = Parser::new("+");
        assert!(p.parse_posix_offset().is_err());

        let p = Parser::new("-a");
        assert!(p.parse_posix_offset().is_err());

        let p = Parser::new("+a");
        assert!(p.parse_posix_offset().is_err());

        let p = Parser::new("-25");
        assert!(p.parse_posix_offset().is_err());

        let p = Parser::new("+25");
        assert!(p.parse_posix_offset().is_err());

        // This checks that we don't accidentally permit IANA rules for
        // offset parsing. Namely, the IANA tzfile v3+ extension only applies
        // to transition times. But since POSIX says that the "time" for the
        // offset and transition is the same format, it would be an easy
        // implementation mistake to implement the more flexible rule for
        // IANA and have it accidentally also apply to the offset. So we check
        // that it doesn't here.
        let p = Parser { ianav3plus: true, ..Parser::new("25") };
        assert!(p.parse_posix_offset().is_err());
        let p = Parser { ianav3plus: true, ..Parser::new("+25") };
        assert!(p.parse_posix_offset().is_err());
        let p = Parser { ianav3plus: true, ..Parser::new("-25") };
        assert!(p.parse_posix_offset().is_err());
    }

    #[test]
    fn parse_rule() {
        let p = Parser::new("M9.5.0,M4.1.0/3");
        assert_eq!(
            p.parse_rule().unwrap(),
            PosixRule {
                start: PosixDayTime {
                    date: PosixDay::WeekdayOfMonth {
                        month: 9,
                        week: 5,
                        weekday: 0,
                    },
                    time: 2 * 60 * 60,
                },
                end: PosixDayTime {
                    date: PosixDay::WeekdayOfMonth {
                        month: 4,
                        week: 1,
                        weekday: 0,
                    },
                    time: 3 * 60 * 60,
                },
            },
        );

        let p = Parser::new("M9.5.0");
        assert!(p.parse_rule().is_err());

        let p = Parser::new(",M9.5.0,M4.1.0/3");
        assert!(p.parse_rule().is_err());

        let p = Parser::new("M9.5.0/");
        assert!(p.parse_rule().is_err());

        let p = Parser::new("M9.5.0,M4.1.0/");
        assert!(p.parse_rule().is_err());
    }

    #[test]
    fn parse_posix_datetime_spec() {
        let p = Parser::new("J1");
        assert_eq!(
            p.parse_posix_datetime_spec().unwrap(),
            PosixDayTime { date: PosixDay::JulianOne(1), time: 2 * 60 * 60 },
        );

        let p = Parser::new("J1/3");
        assert_eq!(
            p.parse_posix_datetime_spec().unwrap(),
            PosixDayTime { date: PosixDay::JulianOne(1), time: 3 * 60 * 60 },
        );

        let p = Parser::new("M4.1.0/3");
        assert_eq!(
            p.parse_posix_datetime_spec().unwrap(),
            PosixDayTime {
                date: PosixDay::WeekdayOfMonth {
                    month: 4,
                    week: 1,
                    weekday: 0,
                },
                time: 3 * 60 * 60,
            },
        );

        let p = Parser::new("1/3:45:05");
        assert_eq!(
            p.parse_posix_datetime_spec().unwrap(),
            PosixDayTime {
                date: PosixDay::JulianZero(1),
                time: 3 * 60 * 60 + 45 * 60 + 5,
            },
        );

        let p = Parser::new("a");
        assert!(p.parse_posix_datetime_spec().is_err());

        let p = Parser::new("J1/");
        assert!(p.parse_posix_datetime_spec().is_err());

        let p = Parser::new("1/");
        assert!(p.parse_posix_datetime_spec().is_err());

        let p = Parser::new("M4.1.0/");
        assert!(p.parse_posix_datetime_spec().is_err());
    }

    #[test]
    fn parse_posix_date_spec() {
        let p = Parser::new("J1");
        assert_eq!(p.parse_posix_date_spec().unwrap(), PosixDay::JulianOne(1));
        let p = Parser::new("J365");
        assert_eq!(
            p.parse_posix_date_spec().unwrap(),
            PosixDay::JulianOne(365)
        );

        let p = Parser::new("0");
        assert_eq!(
            p.parse_posix_date_spec().unwrap(),
            PosixDay::JulianZero(0)
        );
        let p = Parser::new("1");
        assert_eq!(
            p.parse_posix_date_spec().unwrap(),
            PosixDay::JulianZero(1)
        );
        let p = Parser::new("365");
        assert_eq!(
            p.parse_posix_date_spec().unwrap(),
            PosixDay::JulianZero(365)
        );

        let p = Parser::new("M9.5.0");
        assert_eq!(
            p.parse_posix_date_spec().unwrap(),
            PosixDay::WeekdayOfMonth { month: 9, week: 5, weekday: 0 },
        );
        let p = Parser::new("M9.5.6");
        assert_eq!(
            p.parse_posix_date_spec().unwrap(),
            PosixDay::WeekdayOfMonth { month: 9, week: 5, weekday: 6 },
        );
        let p = Parser::new("M09.5.6");
        assert_eq!(
            p.parse_posix_date_spec().unwrap(),
            PosixDay::WeekdayOfMonth { month: 9, week: 5, weekday: 6 },
        );
        let p = Parser::new("M12.1.1");
        assert_eq!(
            p.parse_posix_date_spec().unwrap(),
            PosixDay::WeekdayOfMonth { month: 12, week: 1, weekday: 1 },
        );

        let p = Parser::new("a");
        assert!(p.parse_posix_date_spec().is_err());

        let p = Parser::new("j");
        assert!(p.parse_posix_date_spec().is_err());

        let p = Parser::new("m");
        assert!(p.parse_posix_date_spec().is_err());

        let p = Parser::new("n");
        assert!(p.parse_posix_date_spec().is_err());

        let p = Parser::new("J366");
        assert!(p.parse_posix_date_spec().is_err());

        let p = Parser::new("366");
        assert!(p.parse_posix_date_spec().is_err());
    }

    #[test]
    fn parse_posix_julian_day_no_leap() {
        let p = Parser::new("1");
        assert_eq!(p.parse_posix_julian_day_no_leap().unwrap(), 1);

        let p = Parser::new("001");
        assert_eq!(p.parse_posix_julian_day_no_leap().unwrap(), 1);

        let p = Parser::new("365");
        assert_eq!(p.parse_posix_julian_day_no_leap().unwrap(), 365);

        let p = Parser::new("3655");
        assert_eq!(p.parse_posix_julian_day_no_leap().unwrap(), 365);

        let p = Parser::new("0");
        assert!(p.parse_posix_julian_day_no_leap().is_err());

        let p = Parser::new("366");
        assert!(p.parse_posix_julian_day_no_leap().is_err());
    }

    #[test]
    fn parse_posix_julian_day_with_leap() {
        let p = Parser::new("0");
        assert_eq!(p.parse_posix_julian_day_with_leap().unwrap(), 0);

        let p = Parser::new("1");
        assert_eq!(p.parse_posix_julian_day_with_leap().unwrap(), 1);

        let p = Parser::new("001");
        assert_eq!(p.parse_posix_julian_day_with_leap().unwrap(), 1);

        let p = Parser::new("365");
        assert_eq!(p.parse_posix_julian_day_with_leap().unwrap(), 365);

        let p = Parser::new("3655");
        assert_eq!(p.parse_posix_julian_day_with_leap().unwrap(), 365);

        let p = Parser::new("366");
        assert!(p.parse_posix_julian_day_with_leap().is_err());
    }

    #[test]
    fn parse_weekday_of_month() {
        let p = Parser::new("9.5.0");
        assert_eq!(p.parse_weekday_of_month().unwrap(), (9, 5, 0));

        let p = Parser::new("9.1.6");
        assert_eq!(p.parse_weekday_of_month().unwrap(), (9, 1, 6));

        let p = Parser::new("09.1.6");
        assert_eq!(p.parse_weekday_of_month().unwrap(), (9, 1, 6));

        let p = Parser::new("9");
        assert!(p.parse_weekday_of_month().is_err());

        let p = Parser::new("9.");
        assert!(p.parse_weekday_of_month().is_err());

        let p = Parser::new("9.5");
        assert!(p.parse_weekday_of_month().is_err());

        let p = Parser::new("9.5.");
        assert!(p.parse_weekday_of_month().is_err());

        let p = Parser::new("0.5.0");
        assert!(p.parse_weekday_of_month().is_err());

        let p = Parser::new("13.5.0");
        assert!(p.parse_weekday_of_month().is_err());

        let p = Parser::new("9.0.0");
        assert!(p.parse_weekday_of_month().is_err());

        let p = Parser::new("9.6.0");
        assert!(p.parse_weekday_of_month().is_err());

        let p = Parser::new("9.5.7");
        assert!(p.parse_weekday_of_month().is_err());
    }

    #[test]
    fn parse_posix_time_spec() {
        let p = Parser::new("5");
        assert_eq!(p.parse_posix_time_spec().unwrap(), 5 * 60 * 60);

        let p = Parser::new("22");
        assert_eq!(p.parse_posix_time_spec().unwrap(), 22 * 60 * 60);

        let p = Parser::new("02");
        assert_eq!(p.parse_posix_time_spec().unwrap(), 2 * 60 * 60);

        let p = Parser::new("5:45");
        assert_eq!(p.parse_posix_time_spec().unwrap(), 5 * 60 * 60 + 45 * 60);

        let p = Parser::new("5:45:12");
        assert_eq!(
            p.parse_posix_time_spec().unwrap(),
            5 * 60 * 60 + 45 * 60 + 12
        );

        let p = Parser::new("5:45:129");
        assert_eq!(
            p.parse_posix_time_spec().unwrap(),
            5 * 60 * 60 + 45 * 60 + 12
        );

        let p = Parser::new("5:45:12:");
        assert_eq!(
            p.parse_posix_time_spec().unwrap(),
            5 * 60 * 60 + 45 * 60 + 12
        );

        let p = Parser { ianav3plus: true, ..Parser::new("+5:45:12") };
        assert_eq!(
            p.parse_posix_time_spec().unwrap(),
            5 * 60 * 60 + 45 * 60 + 12
        );

        let p = Parser { ianav3plus: true, ..Parser::new("-5:45:12") };
        assert_eq!(
            p.parse_posix_time_spec().unwrap(),
            -(5 * 60 * 60 + 45 * 60 + 12)
        );

        let p = Parser { ianav3plus: true, ..Parser::new("-167:45:12") };
        assert_eq!(
            p.parse_posix_time_spec().unwrap(),
            -(167 * 60 * 60 + 45 * 60 + 12),
        );

        let p = Parser::new("25");
        assert!(p.parse_posix_time_spec().is_err());

        let p = Parser::new("12:2");
        assert!(p.parse_posix_time_spec().is_err());

        let p = Parser::new("12:");
        assert!(p.parse_posix_time_spec().is_err());

        let p = Parser::new("12:23:5");
        assert!(p.parse_posix_time_spec().is_err());

        let p = Parser::new("12:23:");
        assert!(p.parse_posix_time_spec().is_err());

        let p = Parser { ianav3plus: true, ..Parser::new("168") };
        assert!(p.parse_posix_time_spec().is_err());

        let p = Parser { ianav3plus: true, ..Parser::new("-168") };
        assert!(p.parse_posix_time_spec().is_err());

        let p = Parser { ianav3plus: true, ..Parser::new("+168") };
        assert!(p.parse_posix_time_spec().is_err());
    }

    #[test]
    fn parse_month() {
        let p = Parser::new("1");
        assert_eq!(p.parse_month().unwrap(), 1);

        // Should this be allowed? POSIX spec is unclear.
        // We allow it because our parse does stop at 2
        // digits, so this seems harmless. Namely, '001'
        // results in an error.
        let p = Parser::new("01");
        assert_eq!(p.parse_month().unwrap(), 1);

        let p = Parser::new("12");
        assert_eq!(p.parse_month().unwrap(), 12);

        let p = Parser::new("0");
        assert!(p.parse_month().is_err());

        let p = Parser::new("00");
        assert!(p.parse_month().is_err());

        let p = Parser::new("001");
        assert!(p.parse_month().is_err());

        let p = Parser::new("13");
        assert!(p.parse_month().is_err());
    }

    #[test]
    fn parse_week() {
        let p = Parser::new("1");
        assert_eq!(p.parse_week().unwrap(), 1);

        let p = Parser::new("5");
        assert_eq!(p.parse_week().unwrap(), 5);

        let p = Parser::new("55");
        assert_eq!(p.parse_week().unwrap(), 5);

        let p = Parser::new("0");
        assert!(p.parse_week().is_err());

        let p = Parser::new("6");
        assert!(p.parse_week().is_err());

        let p = Parser::new("00");
        assert!(p.parse_week().is_err());

        let p = Parser::new("01");
        assert!(p.parse_week().is_err());

        let p = Parser::new("05");
        assert!(p.parse_week().is_err());
    }

    #[test]
    fn parse_weekday() {
        let p = Parser::new("0");
        assert_eq!(p.parse_weekday().unwrap(), 0);

        let p = Parser::new("1");
        assert_eq!(p.parse_weekday().unwrap(), 1);

        let p = Parser::new("6");
        assert_eq!(p.parse_weekday().unwrap(), 6);

        let p = Parser::new("00");
        assert_eq!(p.parse_weekday().unwrap(), 0);

        let p = Parser::new("06");
        assert_eq!(p.parse_weekday().unwrap(), 0);

        let p = Parser::new("60");
        assert_eq!(p.parse_weekday().unwrap(), 6);

        let p = Parser::new("7");
        assert!(p.parse_weekday().is_err());
    }

    #[test]
    fn parse_hour_posix() {
        let p = Parser::new("5");
        assert_eq!(p.parse_hour_posix().unwrap(), 5);

        let p = Parser::new("0");
        assert_eq!(p.parse_hour_posix().unwrap(), 0);

        let p = Parser::new("00");
        assert_eq!(p.parse_hour_posix().unwrap(), 0);

        let p = Parser::new("24");
        assert_eq!(p.parse_hour_posix().unwrap(), 24);

        let p = Parser::new("100");
        assert_eq!(p.parse_hour_posix().unwrap(), 10);

        let p = Parser::new("25");
        assert!(p.parse_hour_posix().is_err());

        let p = Parser::new("99");
        assert!(p.parse_hour_posix().is_err());
    }

    #[test]
    fn parse_hour_ianav3plus() {
        let new = |input| Parser { ianav3plus: true, ..Parser::new(input) };

        let p = new("5");
        assert_eq!(p.parse_hour_ianav3plus().unwrap(), 5);

        let p = new("0");
        assert_eq!(p.parse_hour_ianav3plus().unwrap(), 0);

        let p = new("00");
        assert_eq!(p.parse_hour_ianav3plus().unwrap(), 0);

        let p = new("000");
        assert_eq!(p.parse_hour_ianav3plus().unwrap(), 0);

        let p = new("24");
        assert_eq!(p.parse_hour_ianav3plus().unwrap(), 24);

        let p = new("100");
        assert_eq!(p.parse_hour_ianav3plus().unwrap(), 100);

        let p = new("1000");
        assert_eq!(p.parse_hour_ianav3plus().unwrap(), 100);

        let p = new("167");
        assert_eq!(p.parse_hour_ianav3plus().unwrap(), 167);

        let p = new("168");
        assert!(p.parse_hour_ianav3plus().is_err());

        let p = new("999");
        assert!(p.parse_hour_ianav3plus().is_err());
    }

    #[test]
    fn parse_minute() {
        let p = Parser::new("00");
        assert_eq!(p.parse_minute().unwrap(), 0);

        let p = Parser::new("24");
        assert_eq!(p.parse_minute().unwrap(), 24);

        let p = Parser::new("59");
        assert_eq!(p.parse_minute().unwrap(), 59);

        let p = Parser::new("599");
        assert_eq!(p.parse_minute().unwrap(), 59);

        let p = Parser::new("0");
        assert!(p.parse_minute().is_err());

        let p = Parser::new("1");
        assert!(p.parse_minute().is_err());

        let p = Parser::new("9");
        assert!(p.parse_minute().is_err());

        let p = Parser::new("60");
        assert!(p.parse_minute().is_err());
    }

    #[test]
    fn parse_second() {
        let p = Parser::new("00");
        assert_eq!(p.parse_second().unwrap(), 0);

        let p = Parser::new("24");
        assert_eq!(p.parse_second().unwrap(), 24);

        let p = Parser::new("59");
        assert_eq!(p.parse_second().unwrap(), 59);

        let p = Parser::new("599");
        assert_eq!(p.parse_second().unwrap(), 59);

        let p = Parser::new("0");
        assert!(p.parse_second().is_err());

        let p = Parser::new("1");
        assert!(p.parse_second().is_err());

        let p = Parser::new("9");
        assert!(p.parse_second().is_err());

        let p = Parser::new("60");
        assert!(p.parse_second().is_err());
    }

    #[test]
    fn parse_number_with_exactly_n_digits() {
        let p = Parser::new("1");
        assert_eq!(p.parse_number_with_exactly_n_digits(1).unwrap(), 1);

        let p = Parser::new("12");
        assert_eq!(p.parse_number_with_exactly_n_digits(2).unwrap(), 12);

        let p = Parser::new("123");
        assert_eq!(p.parse_number_with_exactly_n_digits(2).unwrap(), 12);

        let p = Parser::new("");
        assert!(p.parse_number_with_exactly_n_digits(1).is_err());

        let p = Parser::new("1");
        assert!(p.parse_number_with_exactly_n_digits(2).is_err());

        let p = Parser::new("12");
        assert!(p.parse_number_with_exactly_n_digits(3).is_err());
    }

    #[test]
    fn parse_number_with_upto_n_digits() {
        let p = Parser::new("1");
        assert_eq!(p.parse_number_with_upto_n_digits(1).unwrap(), 1);

        let p = Parser::new("1");
        assert_eq!(p.parse_number_with_upto_n_digits(2).unwrap(), 1);

        let p = Parser::new("12");
        assert_eq!(p.parse_number_with_upto_n_digits(2).unwrap(), 12);

        let p = Parser::new("12");
        assert_eq!(p.parse_number_with_upto_n_digits(3).unwrap(), 12);

        let p = Parser::new("123");
        assert_eq!(p.parse_number_with_upto_n_digits(2).unwrap(), 12);

        let p = Parser::new("");
        assert!(p.parse_number_with_upto_n_digits(1).is_err());

        let p = Parser::new("a");
        assert!(p.parse_number_with_upto_n_digits(1).is_err());
    }
}
