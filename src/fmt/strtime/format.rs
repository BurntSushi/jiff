#![allow(warnings)]

use crate::{
    error::{err, ErrorContext},
    fmt::{
        strtime::{
            month_name_abbrev, month_name_full, weekday_name_abbrev,
            weekday_name_full, BrokenDownTime, Extension, Flag,
        },
        util::{DecimalFormatter, FractionalFormatter},
        Write, WriteExt,
    },
    tz::Offset,
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
                b'f' => self.fmt_fractional(ext).context("%f failed")?,
                b'H' => self.fmt_hour24(ext).context("%H failed")?,
                b'h' => self.fmt_month_abbrev(ext).context("%b failed")?,
                b'I' => self.fmt_hour12(ext).context("%H failed")?,
                b'M' => self.fmt_minute(ext).context("%M failed")?,
                b'm' => self.fmt_month(ext).context("%m failed")?,
                b'P' => self.fmt_ampm_lower(ext).context("%P failed")?,
                b'p' => self.fmt_ampm_upper(ext).context("%p failed")?,
                b'S' => self.fmt_second(ext).context("%S failed")?,
                b'T' => self.fmt_clock(ext).context("%T failed")?,
                b'V' => self.fmt_iana_nocolon().context("%V failed")?,
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
                        b'V' => self.fmt_iana_colon().context("%:V failed")?,
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
                b'.' => {
                    if !self.bump_fmt() {
                        return Err(err!(
                            "invalid format string, expected directive \
                             after '%.'",
                        ));
                    }
                    // Parse precision settings after the `.`, effectively
                    // overriding any digits that came before it.
                    let ext = Extension { width: self.parse_width()?, ..ext };
                    match self.f() {
                        b'f' => self
                            .fmt_dot_fractional(ext)
                            .context("%.f failed")?,
                        unk => {
                            return Err(err!(
                                "found unrecognized directive %{unk} \
                                 following %.",
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
        let (flag, fmt) = Extension::parse_flag(self.fmt)?;
        self.fmt = fmt;
        Ok(flag)
    }

    /// Parses an optional width that comes after a (possibly absent) flag and
    /// before the specifier directive itself. And if a width is parsed, the
    /// parser is bumped to the next byte. (If no next byte exists, then an
    /// error is returned.)
    ///
    /// Note that this is also used to parse precision settings for `%f` and
    /// `%.f`. In the former case, the width is just re-interpreted as a
    /// precision setting. In the latter case, something like `%5.9f` is
    /// technically valid, but the `5` is ignored.
    fn parse_width(&mut self) -> Result<Option<u8>, Error> {
        let (width, fmt) = Extension::parse_width(self.fmt)?;
        self.fmt = fmt;
        Ok(width)
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

    /// %V
    fn fmt_iana_nocolon(&mut self) -> Result<(), Error> {
        let Some(iana) = self.tm.iana.as_ref() else {
            let offset = self.tm.offset.ok_or_else(|| {
                err!(
                    "requires IANA time zone identifier or time \
                     zone offset, but none were present"
                )
            })?;
            return write_offset(offset, false, &mut self.wtr);
        };
        self.wtr.write_str(iana)?;
        Ok(())
    }

    /// %:V
    fn fmt_iana_colon(&mut self) -> Result<(), Error> {
        let Some(iana) = self.tm.iana.as_ref() else {
            let offset = self.tm.offset.ok_or_else(|| {
                err!(
                    "requires IANA time zone identifier or time \
                     zone offset, but none were present"
                )
            })?;
            return write_offset(offset, true, &mut self.wtr);
        };
        self.wtr.write_str(iana)?;
        Ok(())
    }

    /// %z
    fn fmt_offset_nocolon(&mut self) -> Result<(), Error> {
        let offset = self.tm.offset.ok_or_else(|| {
            err!("requires offset to format time zone offset")
        })?;
        write_offset(offset, false, self.wtr)
    }

    /// %:z
    fn fmt_offset_colon(&mut self) -> Result<(), Error> {
        let offset = self.tm.offset.ok_or_else(|| {
            err!("requires offset to format time zone offset")
        })?;
        write_offset(offset, true, self.wtr)
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

    /// %f
    fn fmt_fractional(&mut self, ext: Extension) -> Result<(), Error> {
        let subsec = self.tm.subsec.ok_or_else(|| {
            err!("requires time to format subsecond nanoseconds")
        })?;
        // For %f, we always want to emit at least one digit. The only way we
        // wouldn't is if our fractional component is zero. One exception to
        // this is when the width is `0` (which looks like `%00f`), in which
        // case, we emit an error. We could allow it to emit an empty string,
        // but this seems very odd. And an empty string cannot be parsed by
        // `%f`.
        if ext.width == Some(0) {
            return Err(err!("zero precision with %f is not allowed"));
        }
        if subsec == 0 && ext.width.is_none() {
            self.wtr.write_str("0")?;
            return Ok(());
        }
        ext.write_fractional_seconds(subsec, self.wtr)?;
        Ok(())
    }

    /// %.f
    fn fmt_dot_fractional(&mut self, ext: Extension) -> Result<(), Error> {
        let Some(subsec) = self.tm.subsec else { return Ok(()) };
        if subsec == 0 && ext.width.is_none() || ext.width == Some(0) {
            return Ok(());
        }
        ext.write_str(Case::AsIs, ".", self.wtr)?;
        ext.write_fractional_seconds(subsec, self.wtr)?;
        Ok(())
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

/// Writes the given time zone offset to the writer.
///
/// When `colon` is true, the hour, minute and optional second components are
/// delimited by a colon. Otherwise, no delimiter is used.
fn write_offset<W: Write>(
    offset: Offset,
    colon: bool,
    mut wtr: &mut W,
) -> Result<(), Error> {
    static FMT_TWO: DecimalFormatter = DecimalFormatter::new().padding(2);

    let hours = offset.part_hours_ranged().abs().get();
    let minutes = offset.part_minutes_ranged().abs().get();
    let seconds = offset.part_seconds_ranged().abs().get();

    wtr.write_str(if offset.is_negative() { "-" } else { "+" })?;
    wtr.write_int(&FMT_TWO, hours)?;
    if colon {
        wtr.write_str(":")?;
    }
    wtr.write_int(&FMT_TWO, minutes)?;
    if seconds != 0 {
        if colon {
            wtr.write_str(":")?;
        }
        wtr.write_int(&FMT_TWO, seconds)?;
    }
    Ok(())
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

    /// Writes the given number of nanoseconds as a fractional component of
    /// a second. This does not include the leading `.`.
    ///
    /// The `width` setting on `Extension` is treated as a precision setting.
    fn write_fractional_seconds<W: Write>(
        self,
        number: impl Into<i64>,
        mut wtr: &mut W,
    ) -> Result<(), Error> {
        let number = number.into();

        let formatter = FractionalFormatter::new().precision(self.width);
        wtr.write_fraction(&formatter, number)
    }
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
        if crate::tz::db().is_definitively_empty() {
            return;
        }

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
    fn ok_format_subsec_nanosecond() {
        let f = |fmt: &str, time: Time| format(fmt, time).unwrap();
        let mk = |subsec| time(0, 0, 0, subsec);

        insta::assert_snapshot!(f("%f", mk(123_000_000)), @"123");
        insta::assert_snapshot!(f("%f", mk(0)), @"0");
        insta::assert_snapshot!(f("%3f", mk(0)), @"000");
        insta::assert_snapshot!(f("%3f", mk(123_000_000)), @"123");
        insta::assert_snapshot!(f("%6f", mk(123_000_000)), @"123000");
        insta::assert_snapshot!(f("%9f", mk(123_000_000)), @"123000000");
        insta::assert_snapshot!(f("%255f", mk(123_000_000)), @"123000000");

        insta::assert_snapshot!(f("%.f", mk(123_000_000)), @".123");
        insta::assert_snapshot!(f("%.f", mk(0)), @"");
        insta::assert_snapshot!(f("%3.f", mk(0)), @"");
        insta::assert_snapshot!(f("%.3f", mk(0)), @".000");
        insta::assert_snapshot!(f("%.3f", mk(123_000_000)), @".123");
        insta::assert_snapshot!(f("%.6f", mk(123_000_000)), @".123000");
        insta::assert_snapshot!(f("%.9f", mk(123_000_000)), @".123000000");
        insta::assert_snapshot!(f("%.255f", mk(123_000_000)), @".123000000");

        insta::assert_snapshot!(f("%3f", mk(123_456_789)), @"123");
        insta::assert_snapshot!(f("%6f", mk(123_456_789)), @"123456");
        insta::assert_snapshot!(f("%9f", mk(123_456_789)), @"123456789");

        insta::assert_snapshot!(f("%.0f", mk(123_456_789)), @"");
        insta::assert_snapshot!(f("%.3f", mk(123_456_789)), @".123");
        insta::assert_snapshot!(f("%.6f", mk(123_456_789)), @".123456");
        insta::assert_snapshot!(f("%.9f", mk(123_456_789)), @".123456789");
    }

    #[test]
    fn ok_format_tzabbrev() {
        if crate::tz::db().is_definitively_empty() {
            return;
        }

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
    fn ok_format_iana() {
        if crate::tz::db().is_definitively_empty() {
            return;
        }

        let f = |fmt: &str, zdt: &Zoned| format(fmt, zdt).unwrap();

        let zdt = date(2024, 7, 14)
            .at(22, 24, 0, 0)
            .intz("America/New_York")
            .unwrap();
        insta::assert_snapshot!(f("%V", &zdt), @"America/New_York");
        insta::assert_snapshot!(f("%:V", &zdt), @"America/New_York");

        let zdt = date(2024, 7, 14)
            .at(22, 24, 0, 0)
            .to_zoned(crate::tz::offset(-4).to_time_zone())
            .unwrap();
        insta::assert_snapshot!(f("%V", &zdt), @"-0400");
        insta::assert_snapshot!(f("%:V", &zdt), @"-04:00");

        let zdt = date(2024, 7, 14)
            .at(22, 24, 0, 0)
            .to_zoned(crate::tz::TimeZone::UTC)
            .unwrap();
        insta::assert_snapshot!(f("%V", &zdt), @"UTC");
        insta::assert_snapshot!(f("%:V", &zdt), @"UTC");
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

    #[test]
    fn err_format_subsec_nanosecond() {
        let f = |fmt: &str, time: Time| format(fmt, time).unwrap_err();
        let mk = |subsec| time(0, 0, 0, subsec);

        insta::assert_snapshot!(
            f("%00f", mk(123_456_789)),
            @"strftime formatting failed: %f failed: zero precision with %f is not allowed",
        );
    }
}
