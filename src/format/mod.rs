use alloc::{string::String, vec::Vec};

use crate::{
    civil,
    error::{err, Error},
    tz::Offset,
    util::{escape, t},
    Instant, TimeScale, Zoned,
};

use self::util::{Decimal, DecimalFormatter};

mod offset;
pub mod rfc3339;
mod rfc9557;
pub mod temporal;
mod util;

const _: &'static dyn Printer = &self::rfc3339::Printer::new();

pub trait Parser {
    fn name(&self) -> &'static str;

    fn parse_zoned<'i, S: TimeScale>(
        &self,
        _input: &'i [u8],
    ) -> Result<Parsed<'i, Zoned<S>>, Error> {
        Err(err!(
            "{name} does not support parsing zoned instants",
            name = self.name()
        ))
    }

    fn parse_instant<'i, S: TimeScale>(
        &self,
        _input: &'i [u8],
    ) -> Result<Parsed<'i, Instant<S>>, Error> {
        Err(err!(
            "{name} does not support parsing instants",
            name = self.name()
        ))
    }

    fn parse_datetime<'i>(
        &self,
        _input: &'i [u8],
    ) -> Result<Parsed<'i, civil::DateTime>, Error> {
        Err(err!(
            "{name} does not support parsing civil datetimes",
            name = self.name()
        ))
    }

    fn parse_date<'i>(
        &self,
        _input: &'i [u8],
    ) -> Result<Parsed<'i, civil::Date>, Error> {
        Err(err!(
            "{name} does not support parsing civil date",
            name = self.name()
        ))
    }

    fn parse_time<'i>(
        &self,
        _input: &'i [u8],
    ) -> Result<Parsed<'i, civil::Time>, Error> {
        Err(err!(
            "{name} does not support parsing civil times",
            name = self.name()
        ))
    }
}

/// The result of parsing a value out of a slice of bytes.
///
/// This contains both the parsed value and the offset at which the value
/// ended in the input given. This makes it possible to parse, for example, a
/// datetime value as a prefix of some larger string without knowing ahead of
/// time where it ends.
#[derive(Clone, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct Parsed<'i, V> {
    /// The value parsed.
    pub value: V,
    /// The remaining unparsed input.
    pub input: &'i [u8],
}

impl<'i, V: core::fmt::Display> Parsed<'i, V> {
    /// Ensures that the parsed value represents the entire input. This occurs
    /// precisely when the `input` on this parsed value is empty.
    ///
    /// This is useful when one expects a parsed value to consume the entire
    /// input, and to consider it an error if it doesn't.
    pub fn into_full(self) -> Result<V, Error> {
        if self.input.is_empty() {
            return Ok(self.value);
        }
        Err(err!(
            "parsed value '{value}', but unparsed input {unparsed:?}
             remains (expected no unparsed input)",
            value = self.value,
            unparsed = escape::Bytes(self.input),
        ))
    }
}

impl<'i, V: core::fmt::Debug> core::fmt::Debug for Parsed<'i, V> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("Parsed")
            .field("value", &self.value)
            .field("input", &escape::Bytes(self.input))
            .finish()
    }
}

pub trait Printer {
    fn name(&self) -> &'static str;

    fn print_zoned<S: TimeScale, W: Write>(
        &self,
        _zoned: &Zoned<S>,
        _wtr: W,
    ) -> Result<(), Error>
    where
        Self: Sized,
    {
        Err(err!(
            "{name} does not support printing zoned instants",
            name = self.name()
        ))
    }

    fn print_instant<S: TimeScale, W: Write>(
        &self,
        _instant: &Instant<S>,
        _wtr: W,
    ) -> Result<(), Error>
    where
        Self: Sized,
    {
        Err(err!(
            "{name} does not support printing instants",
            name = self.name()
        ))
    }

    fn print_datetime<W: Write>(
        &self,
        _datetime: &civil::DateTime,
        _wtr: W,
    ) -> Result<(), Error>
    where
        Self: Sized,
    {
        Err(err!(
            "{name} does not support printing civil datetimes",
            name = self.name()
        ))
    }

    fn print_date<W: Write>(
        &self,
        _date: &civil::Date,
        _wtr: W,
    ) -> Result<(), Error>
    where
        Self: Sized,
    {
        Err(err!(
            "{name} does not support printing civil dates",
            name = self.name()
        ))
    }

    fn print_time<W: Write>(
        &self,
        _time: &civil::Time,
        _wtr: W,
    ) -> Result<(), Error>
    where
        Self: Sized,
    {
        Err(err!(
            "{name} does not support printing civil times",
            name = self.name()
        ))
    }
}

pub trait Write {
    fn write_str(&mut self, string: &str) -> Result<(), Error>;

    #[inline]
    fn write_char(&mut self, char: char) -> Result<(), Error> {
        self.write_str(char.encode_utf8(&mut [0; 4]))
    }
}

impl Write for String {
    #[inline]
    fn write_str(&mut self, string: &str) -> Result<(), Error> {
        self.push_str(string);
        Ok(())
    }
}

impl Write for Vec<u8> {
    #[inline]
    fn write_str(&mut self, string: &str) -> Result<(), Error> {
        self.extend_from_slice(string.as_bytes());
        Ok(())
    }
}

impl<W: Write> Write for &mut W {
    fn write_str(&mut self, string: &str) -> Result<(), Error> {
        (**self).write_str(string)
    }

    #[inline]
    fn write_char(&mut self, char: char) -> Result<(), Error> {
        (**self).write_char(char)
    }
}

#[cfg(feature = "std")]
#[derive(Clone, Debug)]
pub struct StdWrite<W>(pub W);

#[cfg(feature = "std")]
impl<W: std::io::Write> Write for StdWrite<W> {
    #[inline]
    fn write_str(&mut self, string: &str) -> Result<(), Error> {
        use alloc::string::ToString;

        self.0.write_all(string.as_bytes()).map_err(Error::adhoc)
    }
}

#[derive(Clone, Debug)]
pub struct FmtWrite<W>(pub W);

impl<W: core::fmt::Write> Write for FmtWrite<W> {
    #[inline]
    fn write_str(&mut self, string: &str) -> Result<(), Error> {
        use alloc::string::ToString;

        self.0.write_str(string).map_err(Error::adhoc)
    }
}

trait WriteExt: Write {
    /// Write the given number as a decimal using ASCII digits to this buffer.
    /// The given formatter controls how the decimal is formatted.
    #[inline]
    fn write_int(
        &mut self,
        formatter: &DecimalFormatter,
        n: impl Into<i64>,
    ) -> Result<(), Error> {
        self.write_decimal(&Decimal::new(formatter, n.into()))
    }

    /// Write the given decimal number to this buffer.
    #[inline]
    fn write_decimal(&mut self, decimal: &Decimal) -> Result<(), Error> {
        self.write_str(decimal.as_str())
    }
}

impl<W: Write> WriteExt for W {}
