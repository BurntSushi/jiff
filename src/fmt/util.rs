use crate::{
    error::{err, Error},
    fmt::Parsed,
    util::{escape, parse, t},
};

/// A simple formatter for converting `i64` values to ASCII byte strings.
///
/// This avoids going through the formatting machinery which seems to
/// substantially slow things down.
///
/// The `itoa` crate does the same thing as this formatter, but is a bit
/// faster. We roll our own which is a bit slower, but gets us enough of a win
/// to be satisfied with and with (almost) pure safe code.
///
/// By default, this only includes the sign if it's negative. To always include
/// the sign, set `force_sign` to `true`.
#[derive(Clone, Copy, Debug)]
pub(crate) struct DecimalFormatter {
    force_sign: Option<bool>,
    minimum_digits: Option<u8>,
    padding_byte: u8,
    fractional: bool,
}

impl DecimalFormatter {
    /// Creates a new decimal formatter using the default configuration.
    pub(crate) const fn new() -> DecimalFormatter {
        DecimalFormatter {
            force_sign: None,
            minimum_digits: None,
            padding_byte: b'0',
            fractional: false,
        }
    }

    /// Format the given value using this configuration as a decimal ASCII
    /// number.
    pub(crate) const fn format(&self, value: i64) -> Decimal {
        Decimal::new(self, value)
    }

    /// Forces the sign to be rendered, even if it's positive.
    ///
    /// When `zero_is_positive` is true, then a zero value is formatted with a
    /// positive sign. Otherwise, it is formatted with a negative sign.
    #[cfg(test)]
    pub(crate) const fn force_sign(
        self,
        zero_is_positive: bool,
    ) -> DecimalFormatter {
        DecimalFormatter { force_sign: Some(zero_is_positive), ..self }
    }

    /// The minimum number of digits/padding that this number should be
    /// formatted with. If the number would have fewer digits than this, then
    /// it is padded out with the padding byte (which is zero by default) until
    /// the minimum is reached.
    ///
    /// The minimum number of digits is capped at the maximum number of digits
    /// for an i64 value (which is 19).
    pub(crate) const fn padding(self, mut digits: u8) -> DecimalFormatter {
        if digits > Decimal::MAX_I64_DIGITS {
            digits = Decimal::MAX_I64_DIGITS;
        }
        DecimalFormatter { minimum_digits: Some(digits), ..self }
    }

    /// The padding byte to use when `padding` is set.
    ///
    /// The default is `0`.
    pub(crate) const fn padding_byte(self, byte: u8) -> DecimalFormatter {
        DecimalFormatter { padding_byte: byte, ..self }
    }

    /// Sets the maximum precision of this as a fractional number.
    ///
    /// This is useful for formatting the fractional digits to the right-hand
    /// side of a decimal point.
    ///
    /// This implies `minimum_digits(max_precision)`, but also strips all
    /// trailing zeros.
    ///
    /// The maximum precision is capped at the maximum number of digits for an
    /// i64 value (which is 19).
    pub(crate) const fn fractional(
        self,
        max_precision: u8,
    ) -> DecimalFormatter {
        DecimalFormatter { fractional: true, ..self.padding(max_precision) }
    }
}

impl Default for DecimalFormatter {
    fn default() -> DecimalFormatter {
        DecimalFormatter::new()
    }
}

/// A formatted decimal number that can be converted to a sequence of bytes.
#[derive(Debug)]
pub(crate) struct Decimal {
    buf: [u8; Self::MAX_I64_LEN as usize],
    start: u8,
    end: u8,
}

impl Decimal {
    /// Discovered via `i64::MIN.to_string().len()`.
    const MAX_I64_LEN: u8 = 20;
    /// Discovered via `i64::MAX.to_string().len()`.
    const MAX_I64_DIGITS: u8 = 19;

    /// Using the given formatter, turn the value given into a decimal
    /// representation using ASCII bytes.
    pub(crate) const fn new(
        formatter: &DecimalFormatter,
        value: i64,
    ) -> Decimal {
        let sign = value.signum();
        let Some(mut value) = value.checked_abs() else {
            let buf = [
                b'-', b'9', b'2', b'2', b'3', b'3', b'7', b'2', b'0', b'3',
                b'6', b'8', b'5', b'4', b'7', b'7', b'5', b'8', b'0', b'8',
            ];
            return Decimal { buf, start: 0, end: Self::MAX_I64_LEN };
        };
        let mut decimal = Decimal {
            buf: [0; Self::MAX_I64_LEN as usize],
            start: Self::MAX_I64_LEN,
            end: Self::MAX_I64_LEN,
        };
        loop {
            decimal.start -= 1;

            let digit = (value % 10) as u8;
            value /= 10;
            decimal.buf[decimal.start as usize] = b'0' + digit;
            if value == 0 {
                break;
            }
        }
        if let Some(minimum_digits) = formatter.minimum_digits {
            while decimal.len() < minimum_digits {
                decimal.start -= 1;
                decimal.buf[decimal.start as usize] = formatter.padding_byte;
            }
        }
        if sign < 0 {
            decimal.start -= 1;
            decimal.buf[decimal.start as usize] = b'-';
        } else if let Some(zero_is_positive) = formatter.force_sign {
            let ascii_sign =
                if sign > 0 || zero_is_positive { b'+' } else { b'-' };
            decimal.start -= 1;
            decimal.buf[decimal.start as usize] = ascii_sign;
        }
        if formatter.fractional {
            while decimal.end > 0
                && decimal.buf[decimal.end as usize - 1] == b'0'
            {
                decimal.end -= 1;
            }
        }
        decimal
    }

    /// Returns the total number of ASCII bytes (including the sign) that are
    /// used to represent this decimal number.
    const fn len(&self) -> u8 {
        Self::MAX_I64_LEN - self.start
    }

    /// Returns the ASCII representation of this decimal as a byte slice.
    ///
    /// The slice returned is guaranteed to be valid ASCII.
    pub(crate) fn as_bytes(&self) -> &[u8] {
        &self.buf[usize::from(self.start)..usize::from(self.end)]
    }

    /// Returns the ASCII representation of this decimal as a string slice.
    pub(crate) fn as_str(&self) -> &str {
        // SAFETY: This is safe because all bytes written to `self.buf` are
        // guaranteed to be ASCII (including in its initial state), and thus,
        // any subsequence is guaranteed to be valid UTF-8.
        unsafe { core::str::from_utf8_unchecked(self.as_bytes()) }
    }
}

/// Parses an optional fractional number from the start of `input`.
///
/// If `input` does not begin with a `.` (or a `,`), then this returns `None`
/// and no input is consumed. Otherwise, up to 9 ASCII digits are parsed after
/// the decimal separator.
///
/// While this is most typically used to parse the fractional component of
/// second units, it is also used to parse the fractional component of hours
/// or minutes in ISO 8601 duration parsing. The return type in that case is
/// obviously a misnomer, but the range of possible values is still correct.
/// (That is, the fractional component of an hour is still limited to 9 decimal
/// places per the Temporal spec.)
pub(crate) fn parse_temporal_fraction<'i>(
    mut input: &'i [u8],
) -> Result<Parsed<'i, Option<t::SubsecNanosecond>>, Error> {
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
    let nanoseconds = t::SubsecNanosecond::try_new("nanoseconds", nanoseconds)
        .map_err(|err| err!("fractional nanoseconds are not valid: {err}"))?;
    Ok(Parsed { value: Some(nanoseconds), input })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decimal() {
        let x = DecimalFormatter::new().format(i64::MIN);
        assert_eq!(x.as_str(), "-9223372036854775808");

        let x = DecimalFormatter::new().format(i64::MIN + 1);
        assert_eq!(x.as_str(), "-9223372036854775807");

        let x = DecimalFormatter::new().format(i64::MAX);
        assert_eq!(x.as_str(), "9223372036854775807");

        let x = DecimalFormatter::new().force_sign(true).format(i64::MAX);
        assert_eq!(x.as_str(), "+9223372036854775807");

        let x = DecimalFormatter::new().format(0);
        assert_eq!(x.as_str(), "0");

        let x = DecimalFormatter::new().force_sign(true).format(0);
        assert_eq!(x.as_str(), "+0");

        let x = DecimalFormatter::new().force_sign(false).format(0);
        assert_eq!(x.as_str(), "-0");

        let x = DecimalFormatter::new().padding(4).format(0);
        assert_eq!(x.as_str(), "0000");

        let x = DecimalFormatter::new().padding(4).format(789);
        assert_eq!(x.as_str(), "0789");

        let x = DecimalFormatter::new().padding(4).format(-789);
        assert_eq!(x.as_str(), "-0789");

        let x =
            DecimalFormatter::new().force_sign(true).padding(4).format(789);
        assert_eq!(x.as_str(), "+0789");

        let x = DecimalFormatter::new().fractional(9).format(123_000_000);
        assert_eq!(x.as_str(), "123");

        let x = DecimalFormatter::new().fractional(9).format(123_456_000);
        assert_eq!(x.as_str(), "123456");

        let x = DecimalFormatter::new().fractional(9).format(123_456_789);
        assert_eq!(x.as_str(), "123456789");

        let x = DecimalFormatter::new().fractional(9).format(456_789);
        assert_eq!(x.as_str(), "000456789");

        let x = DecimalFormatter::new().fractional(9).format(789);
        assert_eq!(x.as_str(), "000000789");
    }
}
