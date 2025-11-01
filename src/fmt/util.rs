use crate::{
    error::{err, ErrorContext},
    fmt::Parsed,
    util::{escape, parse, t},
    Error, SignedDuration, Span, Unit,
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
    minimum_digits: u8,
    padding_byte: u8,
}

impl DecimalFormatter {
    /// Creates a new decimal formatter using the default configuration.
    pub(crate) const fn new() -> DecimalFormatter {
        DecimalFormatter {
            force_sign: None,
            minimum_digits: 0,
            padding_byte: b'0',
        }
    }

    /// Format the given value using this configuration as a decimal ASCII
    /// number.
    #[cfg(test)]
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
        DecimalFormatter { minimum_digits: digits, ..self }
    }

    /// The padding byte to use when `padding` is set.
    ///
    /// The default is `0`.
    pub(crate) const fn padding_byte(self, byte: u8) -> DecimalFormatter {
        DecimalFormatter { padding_byte: byte, ..self }
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
    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) const fn new(
        formatter: &DecimalFormatter,
        mut value: i64,
    ) -> Decimal {
        // Specialize the common case to generate tighter codegen.
        if value >= 0 && formatter.force_sign.is_none() {
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
            while decimal.len() < formatter.minimum_digits {
                decimal.start -= 1;
                decimal.buf[decimal.start as usize] = formatter.padding_byte;
            }
            return decimal;
        }
        Decimal::new_cold(formatter, value)
    }

    #[cold]
    #[inline(never)]
    const fn new_cold(formatter: &DecimalFormatter, value: i64) -> Decimal {
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
        while decimal.len() < formatter.minimum_digits {
            decimal.start -= 1;
            decimal.buf[decimal.start as usize] = formatter.padding_byte;
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
        decimal
    }

    /// Returns the total number of ASCII bytes (including the sign) that are
    /// used to represent this decimal number.
    #[inline]
    const fn len(&self) -> u8 {
        self.end - self.start
    }

    /// Returns the ASCII representation of this decimal as a byte slice.
    ///
    /// The slice returned is guaranteed to be valid ASCII.
    #[inline]
    pub(crate) fn as_bytes(&self) -> &[u8] {
        &self.buf[usize::from(self.start)..usize::from(self.end)]
    }

    /// Returns the ASCII representation of this decimal as a string slice.
    #[inline]
    pub(crate) fn as_str(&self) -> &str {
        // SAFETY: This is safe because all bytes written to `self.buf` are
        // guaranteed to be ASCII (including in its initial state), and thus,
        // any subsequence is guaranteed to be valid UTF-8.
        unsafe { core::str::from_utf8_unchecked(self.as_bytes()) }
    }
}

/// A simple formatter for converting fractional components to ASCII byte
/// strings.
///
/// We only support precision to 9 decimal places, which corresponds to
/// nanosecond precision as a fractional second component.
#[derive(Clone, Copy, Debug)]
pub(crate) struct FractionalFormatter {
    precision: Option<u8>,
}

impl FractionalFormatter {
    /// Creates a new fractional formatter using the given precision settings.
    pub(crate) const fn new() -> FractionalFormatter {
        FractionalFormatter { precision: None }
    }

    /// Format the given value using this configuration as a decimal ASCII
    /// fractional number.
    pub(crate) const fn format(&self, value: i64) -> Fractional {
        Fractional::new(self, value)
    }

    /// Set the precision.
    ///
    /// If the `precision` is greater than `9`, then it is clamped to `9`.
    ///
    /// When the precision is not set, then it is automatically determined
    /// based on the value.
    pub(crate) const fn precision(
        self,
        precision: Option<u8>,
    ) -> FractionalFormatter {
        let precision = match precision {
            None => None,
            Some(p) if p > 9 => Some(9),
            Some(p) => Some(p),
        };
        FractionalFormatter { precision, ..self }
    }

    /// Returns true if and only if at least one digit will be written for the
    /// given value.
    ///
    /// This is useful for callers that need to know whether to write
    /// a decimal separator, e.g., `.`, before the digits.
    pub(crate) fn will_write_digits(self, value: i64) -> bool {
        self.precision.map_or_else(|| value != 0, |p| p > 0)
    }

    /// Returns true if and only if this formatter has an explicit non-zero
    /// precision setting.
    ///
    /// This is useful for determining whether something like `0.000` needs to
    /// be written in the case of a `precision=Some(3)` setting and a zero
    /// value.
    pub(crate) fn has_non_zero_fixed_precision(self) -> bool {
        self.precision.map_or(false, |p| p > 0)
    }

    /// Returns true if and only if this formatter has fixed zero precision.
    /// That is, no matter what is given as input, a fraction is never written.
    pub(crate) fn has_zero_fixed_precision(self) -> bool {
        self.precision.map_or(false, |p| p == 0)
    }
}

/// A formatted fractional number that can be converted to a sequence of bytes.
#[derive(Debug)]
pub(crate) struct Fractional {
    buf: [u8; Self::MAX_LEN as usize],
    end: u8,
}

impl Fractional {
    /// Since we don't support precision bigger than this.
    const MAX_LEN: u8 = 9;

    /// Using the given formatter, turn the value given into a fractional
    /// decimal representation using ASCII bytes.
    ///
    /// Note that the fractional number returned *may* expand to an empty
    /// slice of bytes. This occurs whenever the precision is set to `0`, or
    /// when the precision is not set and the value is `0`. Any non-zero
    /// explicitly set precision guarantees that the slice returned is not
    /// empty.
    ///
    /// This panics if the value given isn't in the range `0..=999_999_999`.
    pub(crate) const fn new(
        formatter: &FractionalFormatter,
        mut value: i64,
    ) -> Fractional {
        assert!(0 <= value && value <= 999_999_999);
        let mut fractional = Fractional {
            buf: [b'0'; Self::MAX_LEN as usize],
            end: Self::MAX_LEN,
        };
        let mut i = 9;
        loop {
            i -= 1;

            let digit = (value % 10) as u8;
            value /= 10;
            fractional.buf[i] += digit;
            if value == 0 {
                break;
            }
        }
        if let Some(precision) = formatter.precision {
            fractional.end = precision;
        } else {
            while fractional.end > 0
                && fractional.buf[fractional.end as usize - 1] == b'0'
            {
                fractional.end -= 1;
            }
        }
        fractional
    }

    /// Returns the ASCII representation of this fractional number as a byte
    /// slice. The slice returned may be empty.
    ///
    /// The slice returned is guaranteed to be valid ASCII.
    pub(crate) fn as_bytes(&self) -> &[u8] {
        &self.buf[..usize::from(self.end)]
    }

    /// Returns the ASCII representation of this fractional number as a string
    /// slice. The slice returned may be empty.
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
/// second units, it is also used to parse the fractional component of hours or
/// minutes in ISO 8601 duration parsing, and milliseconds and microseconds in
/// the "friendly" duration format. The return type in that case is obviously a
/// misnomer, but the range of possible values is still correct. (That is, the
/// fractional component of an hour is still limited to 9 decimal places per
/// the Temporal spec.)
#[cfg_attr(feature = "perf-inline", inline(always))]
pub(crate) fn parse_temporal_fraction<'i>(
    input: &'i [u8],
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

    #[inline(never)]
    fn imp<'i>(
        mut input: &'i [u8],
    ) -> Result<Parsed<'i, Option<t::SubsecNanosecond>>, Error> {
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
            t::SubsecNanosecond::try_new("nanoseconds", nanoseconds).map_err(
                |err| err!("fractional nanoseconds are not valid: {err}"),
            )?;
        Ok(Parsed { value: Some(nanoseconds), input })
    }

    if input.is_empty() || (input[0] != b'.' && input[0] != b',') {
        return Ok(Parsed { value: None, input });
    }
    imp(&input[1..])
}

/// This routine returns a span based on the given with fractional time applied
/// to it.
///
/// For example, given a span like `P1dT1.5h`, the `unit` would be
/// `Unit::Hour`, the `value` would be `1` and the `fraction` would be
/// `500_000_000`. The span given would just be `1d`. The span returned would
/// be `P1dT1h30m`.
///
/// Note that `fraction` can be a fractional hour, minute, second, millisecond
/// or microsecond (even though its type suggests its only a fraction of a
/// second). When milliseconds or microseconds, the given fraction has any
/// sub-nanosecond precision truncated.
///
/// # Errors
///
/// This can error if the resulting units would be too large for the limits on
/// a `span`. This also errors if `unit` is not `Hour`, `Minute`, `Second`,
/// `Millisecond` or `Microsecond`.
#[inline(never)]
pub(crate) fn fractional_time_to_span(
    unit: Unit,
    value: i64,
    fraction: t::SubsecNanosecond,
    mut span: Span,
) -> Result<Span, Error> {
    const MAX_HOURS: i64 = t::SpanHours::MAX_SELF.get_unchecked() as i64;
    const MAX_MINS: i64 = t::SpanMinutes::MAX_SELF.get_unchecked() as i64;
    const MAX_SECS: i64 = t::SpanSeconds::MAX_SELF.get_unchecked() as i64;
    const MAX_MILLIS: i128 =
        t::SpanMilliseconds::MAX_SELF.get_unchecked() as i128;
    const MAX_MICROS: i128 =
        t::SpanMicroseconds::MAX_SELF.get_unchecked() as i128;

    // We switch everything over to nanoseconds and then divy that up as
    // appropriate. In general, we always create a balanced span, but there
    // are some cases where we can't. For example, if one serializes a span
    // with both the maximum number of seconds and the maximum number of
    // milliseconds, then this just can't be balanced due to the limits on
    // each of the units. When this kind of span is serialized to a string,
    // it results in a second value that is actually bigger than the maximum
    // allowed number of seconds in a span. So here, we have to reverse that
    // operation and spread the seconds over smaller units. This in turn
    // creates an unbalanced span. Annoying.
    //
    // The above is why we have `if unit_value > MAX { <do adjustments> }` in
    // the balancing code below. Basically, if we overshoot our limit, we back
    // out anything over the limit and carry it over to the lesser units. If
    // our value is truly too big, then the final call to set nanoseconds will
    // fail.
    let mut sdur = fractional_time_to_duration(
        unit,
        value,
        fraction,
        SignedDuration::ZERO,
        false,
    )?;

    if unit >= Unit::Hour && !sdur.is_zero() {
        let (mut hours, rem) = sdur.as_hours_with_remainder();
        sdur = rem;
        if hours > MAX_HOURS {
            sdur += SignedDuration::from_hours(hours - MAX_HOURS);
            hours = MAX_HOURS;
        }
        // OK because we just checked that our units are in range.
        span = span.hours(hours);
    }
    if unit >= Unit::Minute && !sdur.is_zero() {
        let (mut mins, rem) = sdur.as_mins_with_remainder();
        sdur = rem;
        if mins > MAX_MINS {
            sdur += SignedDuration::from_mins(mins - MAX_MINS);
            mins = MAX_MINS;
        }
        // OK because we just checked that our units are in range.
        span = span.minutes(mins);
    }
    if unit >= Unit::Second && !sdur.is_zero() {
        let (mut secs, rem) = sdur.as_secs_with_remainder();
        sdur = rem;
        if secs > MAX_SECS {
            sdur += SignedDuration::from_secs(secs - MAX_SECS);
            secs = MAX_SECS;
        }
        // OK because we just checked that our units are in range.
        span = span.seconds(secs);
    }
    if unit >= Unit::Millisecond && !sdur.is_zero() {
        let (mut millis, rem) = sdur.as_millis_with_remainder();
        sdur = rem;
        if millis > MAX_MILLIS {
            sdur += SignedDuration::from_millis_i128(millis - MAX_MILLIS);
            millis = MAX_MILLIS;
        }
        // OK because we just checked that our units are in range.
        span = span.milliseconds(i64::try_from(millis).unwrap());
    }
    if unit >= Unit::Microsecond && !sdur.is_zero() {
        let (mut micros, rem) = sdur.as_micros_with_remainder();
        sdur = rem;
        if micros > MAX_MICROS {
            sdur += SignedDuration::from_micros_i128(micros - MAX_MICROS);
            micros = MAX_MICROS;
        }
        // OK because we just checked that our units are in range.
        span = span.microseconds(i64::try_from(micros).unwrap());
    }
    if !sdur.is_zero() {
        let nanos = sdur.as_nanos();
        let nanos64 = i64::try_from(nanos).map_err(|_| {
            err!(
                "failed to set nanosecond value {nanos} (it overflows \
                 `i64`) on span determined from {value}.{fraction}",
            )
        })?;
        span = span.try_nanoseconds(nanos64).with_context(|| {
            err!(
                "failed to set nanosecond value {nanos64} on span \
                 determined from {value}.{fraction}",
            )
        })?;
    }

    Ok(span)
}

/// Set the given unit to the given value on the given span.
///
/// If the value is outside the legal boundaries for the given unit, then an
/// error is returned.
#[cfg_attr(feature = "perf-inline", inline(always))]
pub(crate) fn set_span_unit_value(
    unit: Unit,
    value: i64,
    span: Span,
) -> Result<Span, Error> {
    let result = span.try_units(unit, value).with_context(|| {
        err!(
            "failed to set value {value:?} \
             as {unit} unit on span",
            unit = unit.singular(),
        )
    });
    result.or_else(|err| {
        if unit > Unit::Hour {
            Err(err)
        } else {
            // This is annoying, but because we can write out a larger
            // number of hours/minutes/seconds than what we actually
            // support, we need to be prepared to parse an unbalanced span
            // if our time units are too big here. In essence, this lets a
            // single time unit "overflow" into smaller units if it exceeds
            // the limits.
            fractional_time_to_span(
                unit,
                value,
                t::SubsecNanosecond::N::<0>(),
                span,
            )
        }
    })
}

/// Like `fractional_time_to_span`, but just converts the fraction of the given
/// unit to a signed duration.
///
/// Since a signed duration doesn't keep track of individual units, there is
/// no loss of fidelity between it and ISO 8601 durations like there is for
/// `Span`.
///
/// Note that `fraction` can be a fractional hour, minute, second, millisecond
/// or microsecond (even though its type suggests it's only a fraction of a
/// second). When milliseconds or microseconds, the given fraction has any
/// sub-nanosecond precision truncated.
///
/// # Errors
///
/// This returns an error if `unit` is not `Hour`, `Minute`, `Second`,
/// `Millisecond` or `Microsecond`.
#[inline(never)]
pub(crate) fn fractional_time_to_duration(
    unit: Unit,
    value: i64,
    fraction: t::SubsecNanosecond,
    sdur: SignedDuration,
    negative: bool,
) -> Result<SignedDuration, Error> {
    let fraction = i64::from(fraction.get());
    let nanos = match unit {
        Unit::Hour => fraction.wrapping_mul(t::SECONDS_PER_HOUR.value()),
        Unit::Minute => fraction.wrapping_mul(t::SECONDS_PER_MINUTE.value()),
        Unit::Second => fraction,
        Unit::Millisecond => fraction.wrapping_div(t::NANOS_PER_MICRO.value()),
        Unit::Microsecond => fraction.wrapping_div(t::NANOS_PER_MILLI.value()),
        unit => {
            return Err(err!(
                "fractional {unit} units are not allowed",
                unit = unit.singular(),
            ))
        }
    };
    let sdur = set_duration_unit_value(unit, value, sdur, negative)?;
    let fraction_dur = SignedDuration::from_nanos(nanos);
    if negative {
        sdur.checked_sub(fraction_dur)
    } else {
        sdur.checked_add(fraction_dur)
    }
    .ok_or_else(|| {
        err!(
            "accumulated `SignedDuration` of `{sdur:?}` overflowed \
             when adding `{fraction_dur:?}` (from fractional {unit} units)",
            unit = unit.singular(),
        )
    })
}

/// Set the given unit to the given value on the given duration.
///
/// If the value is outside the legal boundaries for the given unit, then an
/// error is returned. Moreover, if adding `value` (in terms of `unit`) to
/// the given signed duration would overflow, then an error is returned.
#[cfg_attr(feature = "perf-inline", inline(always))]
pub(crate) fn set_duration_unit_value(
    unit: Unit,
    value: i64,
    sdur: SignedDuration,
    negative: bool,
) -> Result<SignedDuration, Error> {
    let value_dur = duration_unit_value(unit, value)?;
    if negative {
        sdur.checked_sub(value_dur)
    } else {
        sdur.checked_add(value_dur)
    }
    .ok_or_else(|| {
        err!(
            "accumulated `SignedDuration` of `{sdur:?}` overflowed when \
             adding {value} of unit {unit}",
            unit = unit.singular(),
        )
    })
}

/// Returns the given parsed value, interpreted as the given unit, as a
/// `SignedDuration`.
///
/// If the given unit is not supported for signed durations (i.e., calendar
/// units), or if converting the given value to a `SignedDuration` for the
/// given units overflows, then an error is returned.
#[cfg_attr(feature = "perf-inline", inline(always))]
fn duration_unit_value(
    unit: Unit,
    value: i64,
) -> Result<SignedDuration, Error> {
    // Convert our parsed unit into a number of nanoseconds.
    //
    // Note also that overflow isn't possible here for units less than minutes,
    // since a `SignedDuration` supports all `i64` second values.
    let sdur = match unit {
        Unit::Hour => {
            let seconds = value
                .checked_mul(t::SECONDS_PER_HOUR.value())
                .ok_or_else(|| {
                    err!("converting {value} hours to seconds overflows i64")
                })?;
            SignedDuration::from_secs(seconds)
        }
        Unit::Minute => {
            let seconds = value
                .checked_mul(t::SECONDS_PER_MINUTE.value())
                .ok_or_else(|| {
                    err!("converting {value} minutes to seconds overflows i64")
                })?;
            SignedDuration::from_secs(seconds)
        }
        Unit::Second => SignedDuration::from_secs(value),
        Unit::Millisecond => SignedDuration::from_millis(value),
        Unit::Microsecond => SignedDuration::from_micros(value),
        Unit::Nanosecond => SignedDuration::from_nanos(value),
        unsupported => {
            return Err(err!(
                "parsing {unit} units into a `SignedDuration` is not supported \
                 (perhaps try parsing into a `Span` instead)",
                unit = unsupported.singular(),
            ));
        }
    };
    Ok(sdur)
}

#[cfg(test)]
mod tests {
    use alloc::string::ToString;

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
    }

    #[test]
    fn fractional_auto() {
        let f = |n| FractionalFormatter::new().format(n).as_str().to_string();

        assert_eq!(f(0), "");
        assert_eq!(f(123_000_000), "123");
        assert_eq!(f(123_456_000), "123456");
        assert_eq!(f(123_456_789), "123456789");
        assert_eq!(f(456_789), "000456789");
        assert_eq!(f(789), "000000789");
    }

    #[test]
    fn fractional_precision() {
        let f = |precision, n| {
            FractionalFormatter::new()
                .precision(Some(precision))
                .format(n)
                .as_str()
                .to_string()
        };

        assert_eq!(f(0, 0), "");
        assert_eq!(f(1, 0), "0");
        assert_eq!(f(9, 0), "000000000");

        assert_eq!(f(3, 123_000_000), "123");
        assert_eq!(f(6, 123_000_000), "123000");
        assert_eq!(f(9, 123_000_000), "123000000");

        assert_eq!(f(3, 123_456_000), "123");
        assert_eq!(f(6, 123_456_000), "123456");
        assert_eq!(f(9, 123_456_000), "123456000");

        assert_eq!(f(3, 123_456_789), "123");
        assert_eq!(f(6, 123_456_789), "123456");
        assert_eq!(f(9, 123_456_789), "123456789");

        // We use truncation, no rounding.
        assert_eq!(f(2, 889_000_000), "88");
        assert_eq!(f(2, 999_000_000), "99");
    }
}
