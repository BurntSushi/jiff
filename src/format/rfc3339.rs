use alloc::{string::String, vec::Vec};

use crate::{
    civil::DateTime,
    error::Error,
    format::{self, util::DecimalFormatter, Write, WriteExt},
    tz::Offset,
    Instant, TimeScale, TimeZone, Zoned,
};

#[derive(Clone, Debug)]
pub struct Parser {
    flexible_separator: bool,
    rfc9557: bool,
}

#[derive(Clone, Debug)]
pub struct Printer {
    lowercase: bool,
    separator: u8,
    rfc9557: bool,
}

impl Printer {
    pub const fn new() -> Printer {
        Printer { lowercase: false, separator: b'T', rfc9557: true }
    }

    pub const fn lowercase(self, yes: bool) -> Printer {
        Printer { lowercase: yes, ..self }
    }

    pub const fn separator(self, ascii_char: u8) -> Printer {
        assert!(ascii_char.is_ascii(), "RFC3339 separator must be ASCII");
        Printer { separator: ascii_char, ..self }
    }

    pub const fn rfc9557(self, yes: bool) -> Printer {
        Printer { rfc9557: yes, ..self }
    }

    /// Formats the given datetime into the writer given.
    fn print_datetime<W: Write>(
        &self,
        dt: &DateTime,
        mut wtr: W,
    ) -> Result<(), Error> {
        static FMT_YEAR: DecimalFormatter =
            DecimalFormatter::new().minimum_digits(4);
        static FMT_TWO: DecimalFormatter =
            DecimalFormatter::new().minimum_digits(2);
        static FMT_FRACTION: DecimalFormatter =
            DecimalFormatter::new().minimum_digits(9);

        wtr.write_int(&FMT_YEAR, dt.date().year())?;
        wtr.write_str("-");
        wtr.write_int(&FMT_TWO, dt.date().month())?;
        wtr.write_str("-")?;
        wtr.write_int(&FMT_TWO, dt.date().day())?;
        wtr.write_char(char::from(if self.lowercase {
            self.separator.to_ascii_lowercase()
        } else {
            self.separator
        }))?;
        wtr.write_int(&FMT_TWO, dt.time().hour())?;
        wtr.write_str(":")?;
        wtr.write_int(&FMT_TWO, dt.time().minute())?;
        wtr.write_str(":")?;
        wtr.write_int(&FMT_TWO, dt.time().second())?;
        let fractional_nanosecond = dt.time().subsec_nanosecond();
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

impl Default for Printer {
    fn default() -> Printer {
        Printer::new()
    }
}

impl format::Printer for Printer {
    fn name(&self) -> &'static str {
        "RFC3339"
    }

    fn print_zoned<S: TimeScale, W: Write>(
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

    fn print_instant<S: TimeScale, W: Write>(
        &self,
        instant: &Instant<S>,
        mut wtr: W,
    ) -> Result<(), Error> {
        let dt = TimeZone::UTC.to_datetime(*instant);
        self.print_datetime(&dt, &mut wtr)?;
        self.print_zulu(&mut wtr)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::format::Printer as _;

    use super::*;

    #[test]
    fn print_zoned() {
        let dt = DateTime::constant(2024, 3, 10, 5, 34, 45, 0);
        let zoned: Zoned = dt.to_zoned("America/New_York").unwrap();
        let mut buf = String::new();
        Printer::new().print_zoned(&zoned, &mut buf).unwrap();
        assert_eq!(buf, "2024-03-10T05:34:45-04:00[America/New_York]");

        let dt = DateTime::constant(2024, 3, 10, 5, 34, 45, 0);
        let zoned: Zoned = dt.to_zoned("America/New_York").unwrap();
        let zoned = zoned.with_time_zone(TimeZone::UTC);
        let mut buf = String::new();
        Printer::new().print_zoned(&zoned, &mut buf).unwrap();
        assert_eq!(buf, "2024-03-10T09:34:45+00:00[UTC]");
    }

    #[test]
    fn print_instant() {
        let dt = DateTime::constant(2024, 3, 10, 5, 34, 45, 0);
        let zoned: Zoned = dt.to_zoned("America/New_York").unwrap();
        let mut buf = String::new();
        Printer::new().print_instant(&zoned.to_instant(), &mut buf).unwrap();
        assert_eq!(buf, "2024-03-10T09:34:45Z");
    }
}
