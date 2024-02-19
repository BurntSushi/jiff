#![allow(warnings)]

use crate::{
    error::{err, ErrorContext},
    fmt::{
        strtime::{
            month_name_abbrev, month_name_full, weekday_name_abbrev,
            weekday_name_full, BrokenDownTime,
        },
        util::DecimalFormatter,
        Write, WriteExt,
    },
    util::{escape, parse},
    Error,
};

pub(super) struct Formatter<'f, 't, 'w, W> {
    pub(super) fmt: &'f [u8],
    pub(super) tm: &'t BrokenDownTime,
    pub(super) wtr: &'w mut W,
}

impl<'f, 't, 'w, W: Write> Formatter<'f, 't, 'w, W> {
    pub(super) fn format(&mut self) -> Result<(), Error> {
        while !self.fmt.is_empty() {
            if self.f() != b'%' {
                if !self.f().is_ascii() {
                    return Err(err!(
                        "found non-ASCII byte {byte:?} in format \
                         string (ASCII is currently required)",
                        byte = escape::Byte(self.f()),
                    ));
                }
                self.wtr.write_char(char::from(self.f()))?;
                self.bump_fmt();
                continue;
            }
            if !self.bump_fmt() {
                return Err(err!(
                    "invalid format string, expected byte after '%', \
                     but found end of format string",
                ));
            }
            // Parse extensions like padding/case options and padding width.
            let ext = self.parse_extension()?;
            match self.f() {
                b'%' => self.wtr.write_str("%").context("%% failed")?,
                b'A' => self.fmt_weekday_full(ext).context("%A failed")?,
                b'a' => self.fmt_weekday_abbrev(ext).context("%a failed")?,
                b'B' => self.fmt_month_full(ext).context("%B failed")?,
                b'b' => self.fmt_month_abbrev(ext).context("%b failed")?,
                b'D' => self.fmt_american_date(ext).context("%D failed")?,
                b'd' => self.fmt_day_zero(ext).context("%d failed")?,
                b'e' => self.fmt_day_space(ext).context("%e failed")?,
                b'F' => self.fmt_iso_date(ext).context("%F failed")?,
                b'H' => self.fmt_hour24(ext).context("%H failed")?,
                b'h' => self.fmt_month_abbrev(ext).context("%b failed")?,
                b'I' => self.fmt_hour12(ext).context("%H failed")?,
                b'M' => self.fmt_minute(ext).context("%M failed")?,
                b'm' => self.fmt_month(ext).context("%m failed")?,
                b'P' => self.fmt_ampm_lower(ext).context("%P failed")?,
                b'p' => self.fmt_ampm_upper(ext).context("%p failed")?,
                b'S' => self.fmt_second(ext).context("%S failed")?,
                b'T' => self.fmt_clock(ext).context("%T failed")?,
                b'Y' => self.fmt_year(ext).context("%Y failed")?,
                b'y' => self.fmt_year_2digit(ext).context("%y failed")?,
                b'Z' => self.fmt_tzabbrev(ext).context("%Z failed")?,
                b'z' => self.fmt_offset_nocolon().context("%z failed")?,
                b':' => {
                    if !self.bump_fmt() {
                        return Err(err!(
                            "invalid format string, expected directive \
                             after '%:'",
                        ));
                    }
                    match self.f() {
                        b'z' => {
                            self.fmt_offset_colon().context("%:z failed")?
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
                unk => {
                    return Err(err!(
                        "found unrecognized specifier directive %{unk}",
                        unk = escape::Byte(unk),
                    ));
                }
            }
            self.bump_fmt();
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

    /// Bumps the position of the format string.
    ///
    /// This returns true in precisely the cases where `self.f()` will not
    /// panic. i.e., When the end of the format string hasn't been reached yet.
    fn bump_fmt(&mut self) -> bool {
        self.fmt = &self.fmt[1..];
        !self.fmt.is_empty()
    }

    // The parsing routines below are helpers for parsing the format string
    // itself. Ironically, the strtime parser doesn't need to do as much
    // parsing of the format string as the strtime formatter, since the parser
    // doesn't care about zero pad versus space pad. It just supports accepting
    // all of it unconditionally.

    /// Parses optional extensions before a specifier directive. That is, right
    /// after the `%`. If any extensions are parsed, the parser is bumped
    /// to the next byte. (If no next byte exists, then an error is returned.)
    fn parse_extension(&mut self) -> Result<Extension, Error> {
        let flag = self.parse_flag()?;
        let width = self.parse_width()?;
        Ok(Extension { flag, width })
    }

    /// Parses an optional flag. And if one is parsed, the parser is bumped
    /// to the next byte. (If no next byte exists, then an error is returned.)
    fn parse_flag(&mut self) -> Result<Option<Flag>, Error> {
        let byte = self.f();
        let flag = match byte {
            b'_' => Flag::PadSpace,
            b'0' => Flag::PadZero,
            b'-' => Flag::NoPad,
            b'^' => Flag::Uppercase,
            b'#' => Flag::Swapcase,
            _ => return Ok(None),
        };
        if !self.bump_fmt() {
            return Err(err!(
                "expected to find specifier directive after flag \
                 {byte:?}, but found end of format string",
                byte = escape::Byte(byte),
            ));
        }
        Ok(Some(flag))
    }

    /// Parses an optional width that comes after a (possibly absent) flag and
    /// before the specifier directive itself. And if a width is parsed, the
    /// parser is bumped to the next byte. (If no next byte exists, then an
    /// error is returned.)
    fn parse_width(&mut self) -> Result<Option<u8>, Error> {
        let mut digits = 0;
        while digits < self.fmt.len() && self.fmt[digits].is_ascii_digit() {
            digits += 1;
        }
        if digits == 0 {
            return Ok(None);
        }
        let (digits, fmt) = parse::split(self.fmt, digits).unwrap();
        self.fmt = fmt;

        let width = parse::i64(digits)
            .context("failed to parse conversion specifier width")?;
        let width = u8::try_from(width).map_err(|_| {
            err!("{width} is too big, max is {max}", max = u8::MAX)
        })?;
        if self.fmt.is_empty() {
            return Err(err!(
                "expected to find specifier directive after width \
                 {width}, but found end of format string",
            ));
        }
        Ok(Some(width))
    }

    // These are the formatting functions. They are pretty much responsible
    // for getting what they need for the broken down time and reporting a
    // decent failure mode if what they need couldn't be found. And then,
    // of course, doing the actual formatting.

    /// %P
    fn fmt_ampm_lower(&mut self, ext: Extension) -> Result<(), Error> {
        let hour = self
            .tm
            .hour
            .ok_or_else(|| err!("requires time to format AM/PM"))?
            .get();
        ext.write_str(
            Case::AsIs,
            if hour < 12 { "am" } else { "pm" },
            self.wtr,
        )
    }

    /// %p
    fn fmt_ampm_upper(&mut self, ext: Extension) -> Result<(), Error> {
        let hour = self
            .tm
            .hour
            .ok_or_else(|| err!("requires time to format AM/PM"))?
            .get();
        ext.write_str(
            Case::Upper,
            if hour < 12 { "AM" } else { "PM" },
            self.wtr,
        )
    }

    /// %D
    fn fmt_american_date(&mut self, ext: Extension) -> Result<(), Error> {
        self.fmt_month(ext)?;
        self.wtr.write_char('/')?;
        self.fmt_day_zero(ext)?;
        self.wtr.write_char('/')?;
        self.fmt_year_2digit(ext)?;
        Ok(())
    }

    /// %T
    fn fmt_clock(&mut self, ext: Extension) -> Result<(), Error> {
        self.fmt_hour24(ext)?;
        self.wtr.write_char(':')?;
        self.fmt_minute(ext)?;
        self.wtr.write_char(':')?;
        self.fmt_second(ext)?;
        Ok(())
    }

    /// %d
    fn fmt_day_zero(&mut self, ext: Extension) -> Result<(), Error> {
        let day = self
            .tm
            .day
            .ok_or_else(|| err!("requires date to format day"))?
            .get();
        ext.write_int(b'0', Some(2), day, self.wtr)
    }

    /// %e
    fn fmt_day_space(&mut self, ext: Extension) -> Result<(), Error> {
        let day = self
            .tm
            .day
            .ok_or_else(|| err!("requires date to format day"))?
            .get();
        ext.write_int(b' ', Some(2), day, self.wtr)
    }

    /// %I
    fn fmt_hour12(&mut self, ext: Extension) -> Result<(), Error> {
        let mut hour = self
            .tm
            .hour
            .ok_or_else(|| err!("requires time to format hour"))?
            .get();
        if hour == 0 {
            hour = 12;
        } else if hour > 12 {
            hour -= 12;
        }
        ext.write_int(b'0', Some(2), hour, self.wtr)
    }

    /// %H
    fn fmt_hour24(&mut self, ext: Extension) -> Result<(), Error> {
        let hour = self
            .tm
            .hour
            .ok_or_else(|| err!("requires time to format hour"))?
            .get();
        ext.write_int(b'0', Some(2), hour, self.wtr)
    }

    /// %F
    fn fmt_iso_date(&mut self, ext: Extension) -> Result<(), Error> {
        self.fmt_year(ext)?;
        self.wtr.write_char('-')?;
        self.fmt_month(ext)?;
        self.wtr.write_char('-')?;
        self.fmt_day_zero(ext)?;
        Ok(())
    }

    /// %M
    fn fmt_minute(&mut self, ext: Extension) -> Result<(), Error> {
        let minute = self
            .tm
            .minute
            .ok_or_else(|| err!("requires time to format minute"))?
            .get();
        ext.write_int(b'0', Some(2), minute, self.wtr)
    }

    /// %m
    fn fmt_month(&mut self, ext: Extension) -> Result<(), Error> {
        let month = self
            .tm
            .month
            .ok_or_else(|| err!("requires date to format month"))?
            .get();
        ext.write_int(b'0', Some(2), month, self.wtr)
    }

    /// %B
    fn fmt_month_full(&mut self, ext: Extension) -> Result<(), Error> {
        let month = self
            .tm
            .month
            .ok_or_else(|| err!("requires date to format month"))?;
        ext.write_str(Case::AsIs, month_name_full(month), self.wtr)
    }

    /// %b, %h
    fn fmt_month_abbrev(&mut self, ext: Extension) -> Result<(), Error> {
        let month = self
            .tm
            .month
            .ok_or_else(|| err!("requires date to format month"))?;
        ext.write_str(Case::AsIs, month_name_abbrev(month), self.wtr)
    }

    /// %z
    fn fmt_offset_nocolon(&mut self) -> Result<(), Error> {
        static FMT_TWO: DecimalFormatter = DecimalFormatter::new().padding(2);

        let offset = self.tm.offset.ok_or_else(|| {
            err!("requires offset to format time zone offset")
        })?;
        let hours = offset.part_hours_ranged().abs().get();
        let minutes = offset.part_minutes_ranged().abs().get();
        let seconds = offset.part_seconds_ranged().abs().get();

        self.wtr.write_str(if offset.is_negative() { "-" } else { "+" })?;
        self.wtr.write_int(&FMT_TWO, hours)?;
        self.wtr.write_int(&FMT_TWO, minutes)?;
        if seconds != 0 {
            self.wtr.write_int(&FMT_TWO, seconds)?;
        }
        Ok(())
    }

    /// %:z
    fn fmt_offset_colon(&mut self) -> Result<(), Error> {
        static FMT_TWO: DecimalFormatter = DecimalFormatter::new().padding(2);

        let offset = self.tm.offset.ok_or_else(|| {
            err!("requires offset to format time zone offset")
        })?;
        let hours = offset.part_hours_ranged().abs().get();
        let minutes = offset.part_minutes_ranged().abs().get();
        let seconds = offset.part_seconds_ranged().abs().get();

        self.wtr.write_str(if offset.is_negative() { "-" } else { "+" })?;
        self.wtr.write_int(&FMT_TWO, hours)?;
        self.wtr.write_str(":")?;
        self.wtr.write_int(&FMT_TWO, minutes)?;
        if seconds != 0 {
            self.wtr.write_str(":")?;
            self.wtr.write_int(&FMT_TWO, seconds)?;
        }
        Ok(())
    }

    /// %S
    fn fmt_second(&mut self, ext: Extension) -> Result<(), Error> {
        let second = self
            .tm
            .second
            .ok_or_else(|| err!("requires time to format second"))?
            .get();
        ext.write_int(b'0', Some(2), second, self.wtr)
    }

    /// %Z
    fn fmt_tzabbrev(&mut self, ext: Extension) -> Result<(), Error> {
        let tzabbrev = self.tm.tzabbrev.as_ref().ok_or_else(|| {
            err!("requires time zone abbreviation in broken down time")
        })?;
        ext.write_str(Case::Upper, tzabbrev, self.wtr)
    }

    /// %A
    fn fmt_weekday_full(&mut self, ext: Extension) -> Result<(), Error> {
        let weekday = self
            .tm
            .weekday
            .ok_or_else(|| err!("requires date to format weekday"))?;
        ext.write_str(Case::AsIs, weekday_name_full(weekday), self.wtr)
    }

    /// %a
    fn fmt_weekday_abbrev(&mut self, ext: Extension) -> Result<(), Error> {
        let weekday = self
            .tm
            .weekday
            .ok_or_else(|| err!("requires date to format weekday"))?;
        ext.write_str(Case::AsIs, weekday_name_abbrev(weekday), self.wtr)
    }

    /// %Y
    fn fmt_year(&mut self, ext: Extension) -> Result<(), Error> {
        let year = self
            .tm
            .year
            .ok_or_else(|| err!("requires date to format year"))?
            .get();
        ext.write_int(b'0', Some(4), year, self.wtr)
    }

    /// %y
    fn fmt_year_2digit(&mut self, ext: Extension) -> Result<(), Error> {
        let year = self
            .tm
            .year
            .ok_or_else(|| err!("requires date to format year (2-digit)"))?
            .get();
        if !(1969 <= year && year <= 2068) {
            return Err(err!(
                "formatting a 2-digit year requires that it be in \
                 the inclusive range 1969 to 2068, but got {year}",
            ));
        }
        let year = year % 100;
        ext.write_int(b'0', Some(2), year, self.wtr)
    }
}

/// These are "extensions" to the standard `strftime` conversion specifiers.
///
/// Basically, these provide control over padding (zeros, spaces or none),
/// how much to pad and the case of string enumerations.
#[derive(Clone, Copy, Debug)]
struct Extension {
    flag: Option<Flag>,
    width: Option<u8>,
}

impl Extension {
    /// Writes the given string using the default case rule provided, unless
    /// an option in this extension config overrides the default case.
    fn write_str<W: Write>(
        self,
        default: Case,
        string: &str,
        mut wtr: &mut W,
    ) -> Result<(), Error> {
        let case = match self.flag {
            Some(Flag::Uppercase) => Case::Upper,
            Some(Flag::Swapcase) => default.swap(),
            _ => default,
        };
        match case {
            Case::AsIs => {
                wtr.write_str(string)?;
            }
            Case::Upper => {
                for ch in string.chars() {
                    for ch in ch.to_uppercase() {
                        wtr.write_char(ch)?;
                    }
                }
            }
            Case::Lower => {
                for ch in string.chars() {
                    for ch in ch.to_lowercase() {
                        wtr.write_char(ch)?;
                    }
                }
            }
        }
        Ok(())
    }

    /// Writes the given integer using the given padding width and byte, unless
    /// an option in this extension config overrides a default setting.
    fn write_int<W: Write>(
        self,
        pad_byte: u8,
        pad_width: Option<u8>,
        number: impl Into<i64>,
        mut wtr: &mut W,
    ) -> Result<(), Error> {
        let number = number.into();
        let pad_byte = match self.flag {
            Some(Flag::PadZero) => b'0',
            Some(Flag::PadSpace) => b' ',
            _ => pad_byte,
        };
        let pad_width = if matches!(self.flag, Some(Flag::NoPad)) {
            None
        } else {
            self.width.or(pad_width)
        };

        let mut formatter = DecimalFormatter::new().padding_byte(pad_byte);
        if let Some(width) = pad_width {
            formatter = formatter.padding(width);
        }
        wtr.write_int(&formatter, number)
    }
}

/// The different flags one can set. They are mutually exclusive.
#[derive(Clone, Copy, Debug)]
enum Flag {
    PadSpace,
    PadZero,
    NoPad,
    Uppercase,
    Swapcase,
}

/// The case to use when printing a string like weekday or TZ abbreviation.
#[derive(Clone, Copy, Debug)]
enum Case {
    AsIs,
    Upper,
    Lower,
}

impl Case {
    /// Swap upper to lowercase, and lower to uppercase.
    fn swap(self) -> Case {
        match self {
            Case::AsIs => Case::AsIs,
            Case::Upper => Case::Lower,
            Case::Lower => Case::Upper,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        civil::{date, time, Date, Time},
        fmt::strtime::format,
        Zoned,
    };

    use super::*;

    #[test]
    fn ok_format_american_date() {
        let f = |fmt: &str, date: Date| format(fmt, date).unwrap();

        insta::assert_snapshot!(f("%D", date(2024, 7, 9)), @"07/09/24");
        insta::assert_snapshot!(f("%-D", date(2024, 7, 9)), @"7/9/24");
        insta::assert_snapshot!(f("%3D", date(2024, 7, 9)), @"007/009/024");
        insta::assert_snapshot!(f("%03D", date(2024, 7, 9)), @"007/009/024");
    }

    #[test]
    fn ok_format_ampm() {
        let f = |fmt: &str, time: Time| format(fmt, time).unwrap();

        insta::assert_snapshot!(f("%H%P", time(9, 0, 0, 0)), @"09am");
        insta::assert_snapshot!(f("%H%P", time(11, 0, 0, 0)), @"11am");
        insta::assert_snapshot!(f("%H%P", time(23, 0, 0, 0)), @"23pm");
        insta::assert_snapshot!(f("%H%P", time(0, 0, 0, 0)), @"00am");

        insta::assert_snapshot!(f("%H%p", time(9, 0, 0, 0)), @"09AM");
        insta::assert_snapshot!(f("%H%p", time(11, 0, 0, 0)), @"11AM");
        insta::assert_snapshot!(f("%H%p", time(23, 0, 0, 0)), @"23PM");
        insta::assert_snapshot!(f("%H%p", time(0, 0, 0, 0)), @"00AM");

        insta::assert_snapshot!(f("%H%#p", time(9, 0, 0, 0)), @"09am");
    }

    #[test]
    fn ok_format_clock() {
        let f = |fmt: &str, time: Time| format(fmt, time).unwrap();

        insta::assert_snapshot!(f("%T", time(23, 59, 8, 0)), @"23:59:08");
    }

    #[test]
    fn ok_format_day() {
        let f = |fmt: &str, date: Date| format(fmt, date).unwrap();

        insta::assert_snapshot!(f("%d", date(2024, 7, 9)), @"09");
        insta::assert_snapshot!(f("%0d", date(2024, 7, 9)), @"09");
        insta::assert_snapshot!(f("%-d", date(2024, 7, 9)), @"9");
        insta::assert_snapshot!(f("%_d", date(2024, 7, 9)), @" 9");

        insta::assert_snapshot!(f("%e", date(2024, 7, 9)), @" 9");
        insta::assert_snapshot!(f("%0e", date(2024, 7, 9)), @"09");
        insta::assert_snapshot!(f("%-e", date(2024, 7, 9)), @"9");
        insta::assert_snapshot!(f("%_e", date(2024, 7, 9)), @" 9");
    }

    #[test]
    fn ok_format_iso_date() {
        let f = |fmt: &str, date: Date| format(fmt, date).unwrap();

        insta::assert_snapshot!(f("%F", date(2024, 7, 9)), @"2024-07-09");
        insta::assert_snapshot!(f("%-F", date(2024, 7, 9)), @"2024-7-9");
        insta::assert_snapshot!(f("%3F", date(2024, 7, 9)), @"2024-007-009");
        insta::assert_snapshot!(f("%03F", date(2024, 7, 9)), @"2024-007-009");
    }

    #[test]
    fn ok_format_hour() {
        let f = |fmt: &str, time: Time| format(fmt, time).unwrap();

        insta::assert_snapshot!(f("%H", time(9, 0, 0, 0)), @"09");
        insta::assert_snapshot!(f("%H", time(11, 0, 0, 0)), @"11");
        insta::assert_snapshot!(f("%H", time(23, 0, 0, 0)), @"23");
        insta::assert_snapshot!(f("%H", time(0, 0, 0, 0)), @"00");

        insta::assert_snapshot!(f("%I", time(9, 0, 0, 0)), @"09");
        insta::assert_snapshot!(f("%I", time(11, 0, 0, 0)), @"11");
        insta::assert_snapshot!(f("%I", time(23, 0, 0, 0)), @"11");
        insta::assert_snapshot!(f("%I", time(0, 0, 0, 0)), @"12");
    }

    #[test]
    fn ok_format_minute() {
        let f = |fmt: &str, time: Time| format(fmt, time).unwrap();

        insta::assert_snapshot!(f("%M", time(0, 9, 0, 0)), @"09");
        insta::assert_snapshot!(f("%M", time(0, 11, 0, 0)), @"11");
        insta::assert_snapshot!(f("%M", time(0, 23, 0, 0)), @"23");
        insta::assert_snapshot!(f("%M", time(0, 0, 0, 0)), @"00");
    }

    #[test]
    fn ok_format_month() {
        let f = |fmt: &str, date: Date| format(fmt, date).unwrap();

        insta::assert_snapshot!(f("%m", date(2024, 7, 14)), @"07");
        insta::assert_snapshot!(f("%m", date(2024, 12, 14)), @"12");
        insta::assert_snapshot!(f("%0m", date(2024, 7, 14)), @"07");
        insta::assert_snapshot!(f("%0m", date(2024, 12, 14)), @"12");
        insta::assert_snapshot!(f("%-m", date(2024, 7, 14)), @"7");
        insta::assert_snapshot!(f("%-m", date(2024, 12, 14)), @"12");
        insta::assert_snapshot!(f("%_m", date(2024, 7, 14)), @" 7");
        insta::assert_snapshot!(f("%_m", date(2024, 12, 14)), @"12");
    }

    #[test]
    fn ok_format_month_name() {
        let f = |fmt: &str, date: Date| format(fmt, date).unwrap();

        insta::assert_snapshot!(f("%B", date(2024, 7, 14)), @"July");
        insta::assert_snapshot!(f("%b", date(2024, 7, 14)), @"Jul");
        insta::assert_snapshot!(f("%h", date(2024, 7, 14)), @"Jul");

        insta::assert_snapshot!(f("%#B", date(2024, 7, 14)), @"July");
        insta::assert_snapshot!(f("%^B", date(2024, 7, 14)), @"JULY");
    }

    #[test]
    fn ok_format_offset() {
        let f = |fmt: &str, zdt: &Zoned| format(fmt, zdt).unwrap();

        let zdt = date(2024, 7, 14)
            .at(22, 24, 0, 0)
            .intz("America/New_York")
            .unwrap();
        insta::assert_snapshot!(f("%z", &zdt), @"-0400");
        insta::assert_snapshot!(f("%:z", &zdt), @"-04:00");

        let zdt = zdt.checked_add(crate::Span::new().months(5)).unwrap();
        insta::assert_snapshot!(f("%z", &zdt), @"-0500");
        insta::assert_snapshot!(f("%:z", &zdt), @"-05:00");
    }

    #[test]
    fn ok_format_second() {
        let f = |fmt: &str, time: Time| format(fmt, time).unwrap();

        insta::assert_snapshot!(f("%S", time(0, 0, 9, 0)), @"09");
        insta::assert_snapshot!(f("%S", time(0, 0, 11, 0)), @"11");
        insta::assert_snapshot!(f("%S", time(0, 0, 23, 0)), @"23");
        insta::assert_snapshot!(f("%S", time(0, 0, 0, 0)), @"00");
    }

    #[test]
    fn ok_format_tzabbrev() {
        let f = |fmt: &str, zdt: &Zoned| format(fmt, zdt).unwrap();

        let zdt = date(2024, 7, 14)
            .at(22, 24, 0, 0)
            .intz("America/New_York")
            .unwrap();
        insta::assert_snapshot!(f("%Z", &zdt), @"EDT");
        insta::assert_snapshot!(f("%^Z", &zdt), @"EDT");
        insta::assert_snapshot!(f("%#Z", &zdt), @"edt");

        let zdt = zdt.checked_add(crate::Span::new().months(5)).unwrap();
        insta::assert_snapshot!(f("%Z", &zdt), @"EST");
    }

    #[test]
    fn ok_format_weekday_name() {
        let f = |fmt: &str, date: Date| format(fmt, date).unwrap();

        insta::assert_snapshot!(f("%A", date(2024, 7, 14)), @"Sunday");
        insta::assert_snapshot!(f("%a", date(2024, 7, 14)), @"Sun");

        insta::assert_snapshot!(f("%#A", date(2024, 7, 14)), @"Sunday");
        insta::assert_snapshot!(f("%^A", date(2024, 7, 14)), @"SUNDAY");
    }

    #[test]
    fn ok_format_year() {
        let f = |fmt: &str, date: Date| format(fmt, date).unwrap();

        insta::assert_snapshot!(f("%Y", date(2024, 7, 14)), @"2024");
        insta::assert_snapshot!(f("%Y", date(24, 7, 14)), @"0024");
        insta::assert_snapshot!(f("%Y", date(-24, 7, 14)), @"-0024");
    }

    #[test]
    fn ok_format_year_2digit() {
        let f = |fmt: &str, date: Date| format(fmt, date).unwrap();

        insta::assert_snapshot!(f("%y", date(2024, 7, 14)), @"24");
        insta::assert_snapshot!(f("%y", date(2001, 7, 14)), @"01");
        insta::assert_snapshot!(f("%-y", date(2001, 7, 14)), @"1");
        insta::assert_snapshot!(f("%5y", date(2001, 7, 14)), @"00001");
        insta::assert_snapshot!(f("%-5y", date(2001, 7, 14)), @"1");
        insta::assert_snapshot!(f("%05y", date(2001, 7, 14)), @"00001");
        insta::assert_snapshot!(f("%_y", date(2001, 7, 14)), @" 1");
        insta::assert_snapshot!(f("%_5y", date(2001, 7, 14)), @"    1");
    }
}
