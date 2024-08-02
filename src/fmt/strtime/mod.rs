/*!
Support for "printf"-style parsing and formatting.

While the routines exposed in this module very closely resemble the
corresponding [`strptime`] and [`strftime`] POSIX functions, it is not a goal
for the formatting machinery to precisely match POSIX semantics.

If there is a conversion specifier you need that Jiff doesn't support, please
[create a new issue][create-issue].

The formatting and parsing in this module does not currently support any
form of localization. Please see [this issue][locale] about the topic of
localization in Jiff.

[create-issue]: https://github.com/BurntSushi/jiff/issues/new
[locale]: https://github.com/BurntSushi/jiff/issues/4

# Example

This shows how to parse a civil date and its weekday:

```
use jiff::civil::Date;

let date = Date::strptime("%Y-%m-%d is a %A", "2024-07-15 is a Monday")?;
assert_eq!(date.to_string(), "2024-07-15");
// Leading zeros are optional for numbers in all cases:
let date = Date::strptime("%Y-%m-%d is a %A", "2024-07-15 is a Monday")?;
assert_eq!(date.to_string(), "2024-07-15");
// Parsing does error checking! 2024-07-15 was not a Tuesday.
assert!(Date::strptime("%Y-%m-%d is a %A", "2024-07-15 is a Tuesday").is_err());

# Ok::<(), Box<dyn std::error::Error>>(())
```

And this shows how to format a zoned datetime with a time zone abbreviation:

```
use jiff::civil::date;

let zdt = date(2024, 7, 15).at(17, 30, 59, 0).intz("Australia/Tasmania")?;
// %-I instead of %I means no padding.
let string = zdt.strftime("%A, %B %d, %Y at %-I:%M%P %Z").to_string();
assert_eq!(string, "Monday, July 15, 2024 at 5:30pm AEST");

# Ok::<(), Box<dyn std::error::Error>>(())
```

# Usage

For most cases, you can use the `strptime` and `strftime` methods on the
corresponding datetime type. For example, [`Zoned::strptime`] and
[`Zoned::strftime`]. However, the [`BrokenDownTime`] type in this module
provides a little more control.

For example, assuming `t` is a `civil::Time`, then
`t.strftime("%Y").to_string()` will actually panic because a `civil::Time` does
not have a year. While the underlying formatting machinery actually returns
an error, this error gets turned into a panic by virtue of going through the
`std::fmt::Display` and `std::string::ToString` APIs.

In contrast, [`BrokenDownTime::format`] (or just [`format`](format())) can
report the error to you without any panicking:

```
use jiff::{civil::time, fmt::strtime};

let t = time(23, 59, 59, 0);
assert_eq!(
    strtime::format("%Y", t).unwrap_err().to_string(),
    "strftime formatting failed: %Y failed: requires date to format year",
);
```

# Advice

The formatting machinery supported by this module is not especially expressive.
The pattern language is a simple sequence of conversion specifiers interspersed
by literals and arbitrary whitespace. This means that you sometimes need
delimiters or spaces between components. For example, this is fine:

```
use jiff::fmt::strtime;

let date = strtime::parse("%Y%m%d", "20240715")?.to_date()?;
assert_eq!(date.to_string(), "2024-07-15");
# Ok::<(), Box<dyn std::error::Error>>(())
```

But this is ambiguous (is the year `999` or `9990`?):

```
use jiff::fmt::strtime;

assert!(strtime::parse("%Y%m%d", "9990715").is_err());
```

In this case, since years greedily consume up to 4 digits by default, `9990`
is parsed as the year. And since months greedily consume up to 2 digits by
default, `71` is parsed as the month, which results in an invalid day. If you
expect your datetimes to always use 4 digits for the year, then it might be
okay to skip on the delimiters. For example, the year `999` could be written
with a leading zero:

```
use jiff::fmt::strtime;

let date = strtime::parse("%Y%m%d", "09990715")?.to_date()?;
assert_eq!(date.to_string(), "0999-07-15");
// Indeed, the leading zero is written by default when
// formatting, since years are padded out to 4 digits
// by default:
assert_eq!(date.strftime("%Y%m%d").to_string(), "09990715");

# Ok::<(), Box<dyn std::error::Error>>(())
```

Additionally, the parsing and formatting in this module does not currently
support IANA time zone identifiers. This means that it isn't suitable as an
interchange format. And time zone abbreviations, i.e., `%Z` when formatting,
aren't supported when parsing because time zone abbreviations are ambiguous.

The main advice here is that these APIs can come in handy for ad hoc tasks that
would otherwise be annoying to deal with. For example, I once wrote a tool to
extract data from an XML dump of my SMS messages, and one of the date formats
used was `Apr 1, 2022 20:46:15`. That doesn't correspond to any standard, and
while parsing it with a regex isn't that difficult, it's pretty annoying,
especially because of the English abbreviated month name. That's exactly the
kind of use case where this module shines.

If the formatting machinery in this module isn't flexible enough for your use
case and you don't control the format, it is recommended to write a bespoke
parser (possibly with regex). It is unlikely that the expressiveness of this
formatting machinery will be improved much. (Although it is plausible to add
new conversion specifiers.)

# Conversion specifications

This table lists the complete set of conversion specifiers supported in the
format. While most conversion specifiers are supported as is in both parsing
and formatting, there are some differences. Where differences occur, they are
noted in the table below.

When parsing, and whenever a conversion specifier matches an enumeration of
strings, the strings are matched without regard to ASCII case.

| Specifier | Example | Description |
| --------- | ------- | ----------- |
| `%%` | `%%` | A literal `%`. |
| `%A`, `%a` | `Sunday`, `Sun` | The full and abbreviated weekday, respectively. |
| `%B`, `%b`, `%h` | `June`, `Jun`, `Jun` | The full and abbreviated month name, respectively. |
| `%D` | `7/14/24` | Equivalent to `%m/%d/%y`. |
| `%d`, `%e` | `25`, ` 5` | The day of the month. `%d` is zero-padded, `%e` is space padded. |
| `%F` | `2024-07-14` | Equivalent to `%Y-%m-%d`. |
| `%f` | `000456` | Fractional seconds, up to nanosecond precision. |
| `%.f` | `.000456` | Optional fractional seconds, with dot, up to nanosecond precision. |
| `%H` | `23` | The hour in a 24 hour clock. Zero padded. |
| `%I` | `11` | The hour in a 12 hour clock. Zero padded. |
| `%M` | `04` | The minute. Zero padded. |
| `%m` | `01` | The month. Zero padded. |
| `%P` | `am` | Whether the time is in the AM or PM, lowercase. |
| `%p` | `PM` | Whether the time is in the AM or PM, uppercase. |
| `%S` | `59` | The second. Zero padded. |
| `%T` | `23:30:59` | Equivalent to `%H:%M:%S`. |
| `%Y` | `2024` | A full year, including century. Zero padded to 4 digits. |
| `%y` | `24` | A two-digit year. Represents only 1969-2068. Zero padded. |
| `%Z` | `EDT` | A time zone abbreviation. Supported when formatting only. |
| `%z` | `+0530` | A time zone offset in the format `[+-]HHMM[SS]`. |
| `%:z` | `+05:30` | A time zone offset in the format `[+-]HH:MM[:SS]`. |

When formatting, the following flags can be inserted immediately after the `%`
and before the directive:

* `_` - Pad a numeric result to the left with spaces.
* `-` - Do not pad a numeric result.
* `0` - Pad a numeric result to the left with zeros.
* `^` - Use alphabetic uppercase for all relevant strings.
* `#` - Swap the case of the result string. This is typically only useful with
`%p` or `%Z`, since they are the only conversion specifiers that emit strings
entirely in uppercase by default.

The above flags override the "default" settings of a specifier. For example,
`%_d` pads with spaces instead of zeros, and `%0e` pads with zeros instead of
spaces. The exceptions are the `%z` and `%:z` specifiers. They are unaffected
by any flags.

Moreover, any number of decimal digits can be inserted after the (possibly
absent) flag and before the directive, so long as the parsed number is less
than 256. The number formed by these digits will correspond to the minimum
amount of padding (to the left).

The flags and padding amount above may be used when parsing as well. Most
settings are ignoring during parsing except for padding. For example, if one
wanted to parse `003` as the day `3`, then one should use `%03d`. Otherwise, by
default, `%d` will only try to consume at most 2 digits.

The `%f` and `%.f` flags also support specifying the precision, up to
nanoseconds. For example, `%3f` and `%.3f` will both always print a fractional
second component to at least 3 decimal places. When no precision is specified,
then `%f` will always emit at least one digit, even if it's zero. But `%.f`
will emit the empty string when the fractional component is zero. Otherwise, it
will include the leading `.`. For parsing, `%f` does not include the leading
dot, but `%.f` does. Note that all of the options above are still parsed for
`%f` and `%.f`, but they are all no-ops (except for the padding for `%f`, which
is instead interpreted as a precision setting).

# Unsupported

The following things are currently unsupported:

* Parsing or formatting IANA time zone identifiers.
* Parsing or formatting fractional seconds in the time time zone offset.
* Conversion specifiers related to week numbers.
* Conversion specifiers related to day-of-year numbers, like the Julian day.
* The `%s` conversion specifier, for Unix timestamps in seconds.

[`strftime`]: https://pubs.opengroup.org/onlinepubs/009695399/functions/strftime.html
[`strptime`]: https://pubs.opengroup.org/onlinepubs/009695399/functions/strptime.html
*/

use alloc::string::{String, ToString};

use crate::{
    civil::{Date, DateTime, Time, Weekday},
    error::{err, ErrorContext},
    fmt::{
        strtime::{format::Formatter, parse::Parser},
        Write,
    },
    tz::{Offset, TimeZone},
    util::{
        self, escape,
        t::{self, C},
    },
    Error, Timestamp, Zoned,
};

mod format;
mod parse;

/// Parse the given `input` according to the given `format` string.
///
/// See the [module documentation](self) for details on what's supported.
///
/// This routine is the same as [`BrokenDownTime::parse`], but may be more
/// convenient to call.
///
/// # Errors
///
/// This returns an error when parsing failed. This might happen because
/// the format string itself was invalid, or because the input didn't match
/// the format string.
///
/// # Example
///
/// This example shows how to parse something resembling a RFC 2822 datetime:
///
/// ```
/// use jiff::{civil::date, fmt::strtime, tz};
///
/// let zdt = strtime::parse(
///     "%a, %d %b %Y %T %z",
///     "Mon, 15 Jul 2024 16:24:59 -0400",
/// )?.to_zoned()?;
///
/// let tz = tz::offset(-4).to_time_zone();
/// assert_eq!(zdt, date(2024, 7, 15).at(16, 24, 59, 0).to_zoned(tz)?);
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// Of course, one should prefer using the [`fmt::rfc2822`](super::rfc2822)
/// module, which contains a dedicated RFC 2822 parser. For example, the above
/// format string does not part all valid RFC 2822 datetimes, since, e.g.,
/// the leading weekday is optional and so are the seconds in the time, but
/// `strptime`-like APIs have no way of expressing such requirements.
///
/// [RFC 2822]: https://datatracker.ietf.org/doc/html/rfc2822
///
/// # Example: parse RFC 3339 timestamp with fractional seconds
///
/// ```
/// use jiff::{civil::date, fmt::strtime};
///
/// let zdt = strtime::parse(
///     "%Y-%m-%dT%H:%M:%S%.f%:z",
///     "2024-07-15T16:24:59.123456789-04:00",
/// )?.to_zoned()?;
/// assert_eq!(
///     zdt,
///     date(2024, 7, 15).at(16, 24, 59, 123_456_789).intz("America/New_York")?,
/// );
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[inline]
pub fn parse(
    format: impl AsRef<[u8]>,
    input: impl AsRef<[u8]>,
) -> Result<BrokenDownTime, Error> {
    BrokenDownTime::parse(format, input)
}

/// Format the given broken down time using the format string given.
///
/// See the [module documentation](self) for details on what's supported.
///
/// This routine is like [`BrokenDownTime::format`], but may be more
/// convenient to call. Also, it returns a `String` instead of accepting a
/// [`fmt::Write`](super::Write) trait implementation to write to.
///
/// Note that `broken_down_time` can be _anything_ that can be converted into
/// it. This includes, for example, [`Zoned`], [`Timestamp`], [`DateTime`],
/// [`Date`] and [`Time`].
///
/// # Errors
///
/// This returns an error when formatting failed. Formatting can fail either
/// because of an invalid format string, or if formatting requires a field in
/// `BrokenDownTime` to be set that isn't. For example, trying to format a
/// [`DateTime`] with the `%z` specifier will fail because a `DateTime` has no
/// time zone or offset information associated with it.
///
/// # Example
///
/// This example shows how to format a `Zoned` into something resembling a RFC
/// 2822 datetime:
///
/// ```
/// use jiff::{civil::date, fmt::strtime, tz};
///
/// let zdt = date(2024, 7, 15).at(16, 24, 59, 0).intz("America/New_York")?;
/// let string = strtime::format("%a, %-d %b %Y %T %z", &zdt)?;
/// assert_eq!(string, "Mon, 15 Jul 2024 16:24:59 -0400");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// Of course, one should prefer using the [`fmt::rfc2822`](super::rfc2822)
/// module, which contains a dedicated RFC 2822 printer.
///
/// [RFC 2822]: https://datatracker.ietf.org/doc/html/rfc2822
///
/// # Example: `date`-like output
///
/// While the output of the Unix `date` command is likely locale specific,
/// this is what it looks like on my system:
///
/// ```
/// use jiff::{civil::date, fmt::strtime, tz};
///
/// let zdt = date(2024, 7, 15).at(16, 24, 59, 0).intz("America/New_York")?;
/// let string = strtime::format("%a %b %e %I:%M:%S %p %Z %Y", &zdt)?;
/// assert_eq!(string, "Mon Jul 15 04:24:59 PM EDT 2024");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Example: RFC 3339 compatible output with fractional seconds
///
/// ```
/// use jiff::{civil::date, fmt::strtime, tz};
///
/// let zdt = date(2024, 7, 15)
///     .at(16, 24, 59, 123_456_789)
///     .intz("America/New_York")?;
/// let string = strtime::format("%Y-%m-%dT%H:%M:%S%.f%:z", &zdt)?;
/// assert_eq!(string, "2024-07-15T16:24:59.123456789-04:00");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[inline]
pub fn format(
    format: impl AsRef<[u8]>,
    broken_down_time: impl Into<BrokenDownTime>,
) -> Result<String, Error> {
    let broken_down_time: BrokenDownTime = broken_down_time.into();

    let mut buf = String::new();
    broken_down_time.format(format, &mut buf)?;
    Ok(buf)
}

/// The "broken down time" used by parsing and formatting.
///
/// This is a lower level aspect of the `strptime` and `strftime` APIs that you
/// probably won't need to use directly. The main use case is if you want to
/// observe formatting errors or if you want to format a datetime to something
/// other than a `String` via the [`fmt::Write`](super::Write) trait.
///
/// Otherwise, typical use of this module happens indirectly via APIs like
/// [`Zoned::strptime`] and [`Zoned::strftime`].
///
/// # Design
///
/// This is the type that parsing writes to and formatting reads from. That
/// is, parsing proceeds by writing individual parsed fields to this type, and
/// then converting the fields to datetime types like [`Zoned`] only after
/// parsing is complete. Similarly, formatting always begins by converting
/// datetime types like `Zoned` into a `BrokenDownTime`, and then formatting
/// the individual fields from there.
// Design:
//
// This is meant to be very similar to libc's `struct tm` in that it
// represents civil time, although may have an offset attached to it, in which
// case it represents an absolute time. The main difference is that each field
// is explicitly optional, where as in C, there's no way to tell whether a
// field is "set" or not. In C, this isn't so much a problem, because the
// caller needs to explicitly pass in a pointer to a `struct tm`, and so the
// API makes it clear that it's going to mutate the time.
//
// But in Rust, we really just want to accept a format string, an input and
// return a fresh datetime. (Nevermind the fact that we don't provide a way
// to mutate datetimes in place.) We could just use "default" units like you
// might in C, but it would be very surprising if `%m-%d` just decided to fill
// in the year for you with some default value. So we track which pieces have
// been set individually and return errors when requesting, e.g., a `Date`
// when no `year` has been parsed.
//
// We do permit time units to be filled in by default, as-is consistent with
// the rest of Jiff's API. e.g., If a `DateTime` is requested but the format
// string has no directives for time, we'll happy default to midnight. The
// only catch is that you can't omit time units bigger than any present time
// unit. For example, `%M` doesn't fly. If you want to parse minutes, you
// also have to parse hours.
//
// This design does also let us possibly do "incomplete" parsing by asking
// the caller for a datetime to "seed" a `Fields` struct, and then execute
// parsing. But Jiff doesn't currently expose an API to do that. But this
// implementation was intentionally designed to support that use case, C
// style, if it comes up.
#[derive(Debug, Default)]
pub struct BrokenDownTime {
    year: Option<t::Year>,
    month: Option<t::Month>,
    day: Option<t::Day>,
    hour: Option<t::Hour>,
    minute: Option<t::Minute>,
    second: Option<t::Second>,
    subsec: Option<t::SubsecNanosecond>,
    offset: Option<Offset>,
    // Only used to confirm that it is consistent
    // with the date given. But otherwise cannot
    // pick a date on its own.
    weekday: Option<Weekday>,
    // Only generally useful with %I. But can still
    // be used with, say, %H. In that case, AM will
    // turn 13 o'clock to 1 o'clock.
    meridiem: Option<Meridiem>,
    // The time zone abbreviation. Used only when
    // formatting a `Zoned`.
    tzabbrev: Option<String>,
}

impl BrokenDownTime {
    /// Parse the given `input` according to the given `format` string.
    ///
    /// See the [module documentation](self) for details on what's supported.
    ///
    /// This routine is the same as the module level free function
    /// [`strtime::parse`](parse()).
    ///
    /// # Errors
    ///
    /// This returns an error when parsing failed. This might happen because
    /// the format string itself was invalid, or because the input didn't match
    /// the format string.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::{civil, fmt::strtime::BrokenDownTime};
    ///
    /// let tm = BrokenDownTime::parse("%m/%d/%y", "7/14/24")?;
    /// let date = tm.to_date()?;
    /// assert_eq!(date, civil::date(2024, 7, 14));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn parse(
        format: impl AsRef<[u8]>,
        input: impl AsRef<[u8]>,
    ) -> Result<BrokenDownTime, Error> {
        BrokenDownTime::parse_mono(format.as_ref(), input.as_ref())
    }

    #[inline]
    fn parse_mono(fmt: &[u8], inp: &[u8]) -> Result<BrokenDownTime, Error> {
        let mut pieces = BrokenDownTime::default();
        let mut p = Parser { fmt, inp, tm: &mut pieces };
        p.parse().context("strptime parsing failed")?;
        if !p.inp.is_empty() {
            return Err(err!(
                "strptime expects to consume the entire input, but \
                 {remaining:?} remains unparsed",
                remaining = escape::Bytes(p.inp),
            ));
        }
        Ok(pieces)
    }

    /// Format this broken down time using the format string given.
    ///
    /// See the [module documentation](self) for details on what's supported.
    ///
    /// This routine is like the module level free function
    /// [`strtime::format`](parse()), except it takes a
    /// [`fmt::Write`](super::Write) trait implementations instead of assuming
    /// you want a `String`.
    ///
    /// # Errors
    ///
    /// This returns an error when formatting failed. Formatting can fail
    /// either because of an invalid format string, or if formatting requires
    /// a field in `BrokenDownTime` to be set that isn't. For example, trying
    /// to format a [`DateTime`] with the `%z` specifier will fail because a
    /// `DateTime` has no time zone or offset information associated with it.
    ///
    /// Formatting also fails if writing to the given writer fails.
    ///
    /// # Example
    ///
    /// This example shows a formatting option, `%Z`, that isn't available
    /// during parsing. Namely, `%Z` inserts a time zone abbreviation. This
    /// is generally only intended for display purposes, since it can be
    /// ambiguous when parsing.
    ///
    /// ```
    /// use jiff::{civil::date, fmt::strtime::BrokenDownTime};
    ///
    /// let zdt = date(2024, 7, 9).at(16, 24, 0, 0).intz("America/New_York")?;
    /// let tm = BrokenDownTime::from(&zdt);
    ///
    /// let mut buf = String::new();
    /// tm.format("%a %b %e %I:%M:%S %p %Z %Y", &mut buf)?;
    ///
    /// assert_eq!(buf, "Tue Jul  9 04:24:00 PM EDT 2024");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn format<W: Write>(
        &self,
        format: impl AsRef<[u8]>,
        mut wtr: W,
    ) -> Result<(), Error> {
        let fmt = format.as_ref();
        let mut formatter = Formatter { fmt, tm: self, wtr: &mut wtr };
        formatter.format().context("strftime formatting failed")?;
        Ok(())
    }

    /// Format this broken down time using the format string given into a new
    /// `String`.
    ///
    /// See the [module documentation](self) for details on what's supported.
    ///
    /// This is like [`BrokenDownTime::format`], but always uses a `String` to
    /// format the time into. If you need to reuse allocations or write a
    /// formatted time into a different type, then you should use
    /// [`BrokenDownTime::format`] instead.
    ///
    /// # Errors
    ///
    /// This returns an error when formatting failed. Formatting can fail
    /// either because of an invalid format string, or if formatting requires
    /// a field in `BrokenDownTime` to be set that isn't. For example, trying
    /// to format a [`DateTime`] with the `%z` specifier will fail because a
    /// `DateTime` has no time zone or offset information associated with it.
    ///
    /// # Example
    ///
    /// This example shows a formatting option, `%Z`, that isn't available
    /// during parsing. Namely, `%Z` inserts a time zone abbreviation. This
    /// is generally only intended for display purposes, since it can be
    /// ambiguous when parsing.
    ///
    /// ```
    /// use jiff::{civil::date, fmt::strtime::BrokenDownTime};
    ///
    /// let zdt = date(2024, 7, 9).at(16, 24, 0, 0).intz("America/New_York")?;
    /// let tm = BrokenDownTime::from(&zdt);
    /// let string = tm.to_string("%a %b %e %I:%M:%S %p %Z %Y")?;
    /// assert_eq!(string, "Tue Jul  9 04:24:00 PM EDT 2024");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn to_string(
        &self,
        format: impl AsRef<[u8]>,
    ) -> Result<String, Error> {
        let mut buf = String::new();
        self.format(format, &mut buf)?;
        Ok(buf)
    }

    /// Extracts a zoned datetime from this broken down time.
    ///
    /// # Warning
    ///
    /// The `strtime` module APIs do not support parsing or formatting with
    /// IANA time zone identifiers. This means that if you format a zoned
    /// datetime in a time zone like `America/New_York` and then parse it back
    /// again, the zoned datetime you get back will be a "fixed offset" zoned
    /// datetime. This in turn means it will not perform daylight saving time
    /// safe arithmetic.
    ///
    /// The `strtime` modules APIs are useful for ad hoc formatting and
    /// parsing, but they shouldn't be used as an interchange format. For
    /// an interchange format, the default `std::fmt::Display` and
    /// `std::str::FromStr` trait implementations on `Zoned` are appropriate.
    ///
    /// # Errors
    ///
    /// This returns an error if there weren't enough components to construct
    /// a civil datetime _and_ a UTC offset.
    ///
    /// # Example
    ///
    /// This example shows how to parse a zoned datetime:
    ///
    /// ```
    /// use jiff::fmt::strtime;
    ///
    /// let zdt = strtime::parse(
    ///     "%F %H:%M %:z",
    ///     "2024-07-14 21:14 -04:00",
    /// )?.to_zoned()?;
    /// assert_eq!(zdt.to_string(), "2024-07-14T21:14:00-04:00[-04:00]");
    ///
    /// // It might be prudent to convert the zoned datetime you get back
    /// // into a "real" time zone:
    /// let zdt = zdt.intz("Australia/Tasmania")?;
    /// assert_eq!(
    ///     zdt.to_string(),
    ///     "2024-07-15T11:14:00+10:00[Australia/Tasmania]",
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn to_zoned(&self) -> Result<Zoned, Error> {
        let dt = self
            .to_datetime()
            .context("datetime required to parse zoned datetime")?;
        let offset = self
            .to_offset()
            .context("offset required to parse zoned datetime")?;
        let ts = offset.to_timestamp(dt).with_context(|| {
            err!(
                "parsed datetime {dt} and offset {offset}, \
                 but combining them into a zoned datetime is outside \
                 Jiff's supported timestamp range",
            )
        })?;
        Ok(ts.to_zoned(TimeZone::fixed(offset)))
    }

    /// Extracts a timestamp from this broken down time.
    ///
    /// # Errors
    ///
    /// This returns an error if there weren't enough components to construct
    /// a civil datetime _and_ a UTC offset.
    ///
    /// # Example
    ///
    /// This example shows how to parse a timestamp from a broken down time:
    ///
    /// ```
    /// use jiff::fmt::strtime;
    ///
    /// let ts = strtime::parse(
    ///     "%F %H:%M %:z",
    ///     "2024-07-14 21:14 -04:00",
    /// )?.to_timestamp()?;
    /// assert_eq!(ts.to_string(), "2024-07-15T01:14:00Z");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn to_timestamp(&self) -> Result<Timestamp, Error> {
        let dt = self
            .to_datetime()
            .context("datetime required to parse timestamp")?;
        let offset =
            self.to_offset().context("offset required to parse timestamp")?;
        offset.to_timestamp(dt).with_context(|| {
            err!(
                "parsed datetime {dt} and offset {offset}, \
                 but combining them into a timestamp is outside \
                 Jiff's supported timestamp range",
            )
        })
    }

    #[inline]
    fn to_offset(&self) -> Result<Offset, Error> {
        let Some(offset) = self.offset else {
            return Err(err!(
                "parsing format did not include time zone offset directive",
            ));
        };
        Ok(offset)
    }

    /// Extracts a civil datetime from this broken down time.
    ///
    /// # Errors
    ///
    /// This returns an error if there weren't enough components to construct
    /// a civil datetime. This means there must be at least a year, month and
    /// day.
    ///
    /// It's okay if there are more units than are needed to construct a civil
    /// datetime. For example, if this broken down time contains an offset,
    /// then it won't prevent a conversion to a civil datetime.
    ///
    /// # Example
    ///
    /// This example shows how to parse a civil datetime from a broken down
    /// time:
    ///
    /// ```
    /// use jiff::fmt::strtime;
    ///
    /// let dt = strtime::parse("%F %H:%M", "2024-07-14 21:14")?.to_datetime()?;
    /// assert_eq!(dt.to_string(), "2024-07-14T21:14:00");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn to_datetime(&self) -> Result<DateTime, Error> {
        let date =
            self.to_date().context("date required to parse datetime")?;
        let time =
            self.to_time().context("time required to parse datetime")?;
        Ok(DateTime::from_parts(date, time))
    }

    /// Extracts a civil date from this broken down time.
    ///
    /// # Errors
    ///
    /// This returns an error if there weren't enough components to construct a
    /// civil date. This means there must be at least a year, month and day.
    ///
    /// It's okay if there are more units than are needed to construct a civil
    /// datetime. For example, if this broken down time contain a civil time,
    /// then it won't prevent a conversion to a civil date.
    ///
    /// # Example
    ///
    /// This example shows how to parse a civil date from a broken down time:
    ///
    /// ```
    /// use jiff::fmt::strtime;
    ///
    /// let date = strtime::parse("%m/%d/%y", "7/14/24")?.to_date()?;
    /// assert_eq!(date.to_string(), "2024-07-14");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn to_date(&self) -> Result<Date, Error> {
        let Some(year) = self.year else {
            return Err(err!(
                "parsing format did not include year directive, \
                 without it, a date cannot be created",
            ));
        };
        let Some(month) = self.month else {
            return Err(err!(
                "parsing format did not include month directive, \
                 without it, a date cannot be created",
            ));
        };
        let Some(day) = self.day else {
            return Err(err!(
                "parsing format did not include day directive, \
                 without it, a date cannot be created",
            ));
        };
        let date =
            Date::new_ranged(year, month, day).context("invalid date")?;
        if let Some(weekday) = self.weekday {
            if weekday != date.weekday() {
                return Err(err!(
                    "parsed weekday {weekday} does not match \
                     weekday {got} from parsed date {date}",
                    weekday = weekday_name_full(weekday),
                    got = weekday_name_full(date.weekday()),
                ));
            }
        }
        Ok(date)
    }

    /// Extracts a civil time from this broken down time.
    ///
    /// # Errors
    ///
    /// This returns an error if there weren't enough components to construct
    /// a civil time. Interestingly, this succeeds if there are no time units,
    /// since this will assume an absent time is midnight. However, this can
    /// still error when, for example, there are minutes but no hours.
    ///
    /// It's okay if there are more units than are needed to construct a civil
    /// time. For example, if this broken down time contains a date, then it
    /// won't prevent a conversion to a civil time.
    ///
    /// # Example
    ///
    /// This example shows how to parse a civil time from a broken down
    /// time:
    ///
    /// ```
    /// use jiff::fmt::strtime;
    ///
    /// let time = strtime::parse("%H:%M:%S", "21:14:59")?.to_time()?;
    /// assert_eq!(time.to_string(), "21:14:59");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: time defaults to midnight
    ///
    /// Since time defaults to midnight, one can parse an empty input string
    /// with an empty format string and still extract a `Time`:
    ///
    /// ```
    /// use jiff::fmt::strtime;
    ///
    /// let time = strtime::parse("", "")?.to_time()?;
    /// assert_eq!(time.to_string(), "00:00:00");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: invalid time
    ///
    /// Other than using illegal values (like `24` for hours), if lower units
    /// are parsed without higher units, then this results in an error:
    ///
    /// ```
    /// use jiff::fmt::strtime;
    ///
    /// assert!(strtime::parse("%M:%S", "15:36")?.to_time().is_err());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: invalid date
    ///
    /// Since validation of a date is only done when a date is requested, it is
    /// actually possible to parse an invalid date and extract the time without
    /// an error occurring:
    ///
    /// ```
    /// use jiff::fmt::strtime;
    ///
    /// // 31 is a legal day value, but not for June.
    /// // However, this is not validated unless you
    /// // ask for a `Date` from the parsed `BrokenDownTime`.
    /// // Everything except for `BrokenDownTime::time`
    /// // creates a date, so asking for only a `time`
    /// // will circumvent date validation!
    /// let tm = strtime::parse("%Y-%m-%d %H:%M:%S", "2024-06-31 21:14:59")?;
    /// let time = tm.to_time()?;
    /// assert_eq!(time.to_string(), "21:14:59");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn to_time(&self) -> Result<Time, Error> {
        let Some(hour) = self.hour_ranged() else {
            if self.minute.is_some() {
                return Err(err!(
                    "parsing format did not include hour directive, \
                     but did include minute directive (cannot have \
                     smaller time units with bigger time units missing)",
                ));
            }
            if self.second.is_some() {
                return Err(err!(
                    "parsing format did not include hour directive, \
                     but did include second directive (cannot have \
                     smaller time units with bigger time units missing)",
                ));
            }
            if self.subsec.is_some() {
                return Err(err!(
                    "parsing format did not include hour directive, \
                     but did include fractional second directive (cannot have \
                     smaller time units with bigger time units missing)",
                ));
            }
            return Ok(Time::midnight());
        };
        let Some(minute) = self.minute else {
            if self.second.is_some() {
                return Err(err!(
                    "parsing format did not include minute directive, \
                     but did include second directive (cannot have \
                     smaller time units with bigger time units missing)",
                ));
            }
            if self.subsec.is_some() {
                return Err(err!(
                    "parsing format did not include minute directive, \
                     but did include fractional second directive (cannot have \
                     smaller time units with bigger time units missing)",
                ));
            }
            return Ok(Time::new_ranged(hour, C(0), C(0), C(0)));
        };
        let Some(second) = self.second else {
            if self.subsec.is_some() {
                return Err(err!(
                    "parsing format did not include second directive, \
                     but did include fractional second directive (cannot have \
                     smaller time units with bigger time units missing)",
                ));
            }
            return Ok(Time::new_ranged(hour, minute, C(0), C(0)));
        };
        let Some(subsec) = self.subsec else {
            return Ok(Time::new_ranged(hour, minute, second, C(0)));
        };
        Ok(Time::new_ranged(hour, minute, second, subsec))
    }

    /// Returns the parsed year, if available.
    ///
    /// This is also set when a 2 digit year is parsed. (But that's limited to
    /// the years 1969 to 2068, inclusive.)
    ///
    /// # Example
    ///
    /// This shows how to parse just a year:
    ///
    /// ```
    /// use jiff::fmt::strtime::BrokenDownTime;
    ///
    /// let tm = BrokenDownTime::parse("%Y", "2024")?;
    /// assert_eq!(tm.year(), Some(2024));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// And 2-digit years are supported too:
    ///
    /// ```
    /// use jiff::fmt::strtime::BrokenDownTime;
    ///
    /// let tm = BrokenDownTime::parse("%y", "24")?;
    /// assert_eq!(tm.year(), Some(2024));
    /// let tm = BrokenDownTime::parse("%y", "00")?;
    /// assert_eq!(tm.year(), Some(2000));
    /// let tm = BrokenDownTime::parse("%y", "69")?;
    /// assert_eq!(tm.year(), Some(1969));
    ///
    /// // 2-digit years have limited range. They must
    /// // be in the range 0-99.
    /// assert!(BrokenDownTime::parse("%y", "2024").is_err());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn year(&self) -> Option<i16> {
        self.year.map(|x| x.get())
    }

    /// Returns the parsed month, if available.
    ///
    /// # Example
    ///
    /// This shows a few different ways of parsing just a month:
    ///
    /// ```
    /// use jiff::fmt::strtime::BrokenDownTime;
    ///
    /// let tm = BrokenDownTime::parse("%m", "12")?;
    /// assert_eq!(tm.month(), Some(12));
    ///
    /// let tm = BrokenDownTime::parse("%B", "December")?;
    /// assert_eq!(tm.month(), Some(12));
    ///
    /// let tm = BrokenDownTime::parse("%b", "Dec")?;
    /// assert_eq!(tm.month(), Some(12));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn month(&self) -> Option<i8> {
        self.month.map(|x| x.get())
    }

    /// Returns the parsed day, if available.
    ///
    /// # Example
    ///
    /// This shows how to parse the day of the month:
    ///
    /// ```
    /// use jiff::fmt::strtime::BrokenDownTime;
    ///
    /// let tm = BrokenDownTime::parse("%d", "5")?;
    /// assert_eq!(tm.day(), Some(5));
    ///
    /// let tm = BrokenDownTime::parse("%d", "05")?;
    /// assert_eq!(tm.day(), Some(5));
    ///
    /// let tm = BrokenDownTime::parse("%03d", "005")?;
    /// assert_eq!(tm.day(), Some(5));
    ///
    /// // Parsing a day only works for all possible legal
    /// // values, even if, e.g., 31 isn't valid for all
    /// // possible year/month combinations.
    /// let tm = BrokenDownTime::parse("%d", "31")?;
    /// assert_eq!(tm.day(), Some(31));
    /// // This is true even if you're parsing a full date:
    /// let tm = BrokenDownTime::parse("%Y-%m-%d", "2024-04-31")?;
    /// assert_eq!(tm.day(), Some(31));
    /// // An error only occurs when you try to extract a date:
    /// assert!(tm.to_date().is_err());
    /// // But parsing a value that is always illegal will
    /// // result in an error:
    /// assert!(BrokenDownTime::parse("%d", "32").is_err());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn day(&self) -> Option<i8> {
        self.day.map(|x| x.get())
    }

    /// Returns the parsed hour, if available.
    ///
    /// The hour returned incorporates [`BrokenDownTime::meridiem`] if it's
    /// set. That is, if the actual parsed hour value is `1` but the meridiem
    /// is `PM`, then the hour returned by this method will be `13`.
    ///
    /// # Example
    ///
    /// This shows a how to parse an hour:
    ///
    /// ```
    /// use jiff::fmt::strtime::BrokenDownTime;
    ///
    /// let tm = BrokenDownTime::parse("%H", "13")?;
    /// assert_eq!(tm.hour(), Some(13));
    ///
    /// // When parsing a 12-hour clock without a
    /// // meridiem, the hour value is as parsed.
    /// let tm = BrokenDownTime::parse("%I", "1")?;
    /// assert_eq!(tm.hour(), Some(1));
    ///
    /// // If a meridiem is parsed, then it is used
    /// // to calculate the correct hour value.
    /// let tm = BrokenDownTime::parse("%I%P", "1pm")?;
    /// assert_eq!(tm.hour(), Some(13));
    ///
    /// // This works even if the hour and meridiem are
    /// // inconsistent with each other:
    /// let tm = BrokenDownTime::parse("%H%P", "13am")?;
    /// assert_eq!(tm.hour(), Some(1));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn hour(&self) -> Option<i8> {
        self.hour_ranged().map(|x| x.get())
    }

    #[inline]
    fn hour_ranged(&self) -> Option<t::Hour> {
        let hour = self.hour?;
        Some(match self.meridiem() {
            None => hour,
            Some(Meridiem::AM) => hour % C(12),
            Some(Meridiem::PM) => (hour % C(12)) + C(12),
        })
    }

    /// Returns the parsed minute, if available.
    ///
    /// # Example
    ///
    /// This shows how to parse the minute:
    ///
    /// ```
    /// use jiff::fmt::strtime::BrokenDownTime;
    ///
    /// let tm = BrokenDownTime::parse("%M", "5")?;
    /// assert_eq!(tm.minute(), Some(5));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn minute(&self) -> Option<i8> {
        self.minute.map(|x| x.get())
    }

    /// Returns the parsed second, if available.
    ///
    /// # Example
    ///
    /// This shows how to parse the second:
    ///
    /// ```
    /// use jiff::fmt::strtime::BrokenDownTime;
    ///
    /// let tm = BrokenDownTime::parse("%S", "5")?;
    /// assert_eq!(tm.second(), Some(5));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn second(&self) -> Option<i8> {
        self.second.map(|x| x.get())
    }

    /// Returns the parsed subsecond nanosecond, if available.
    ///
    /// # Example
    ///
    /// This shows how to parse fractional seconds:
    ///
    /// ```
    /// use jiff::fmt::strtime::BrokenDownTime;
    ///
    /// let tm = BrokenDownTime::parse("%f", "123456")?;
    /// assert_eq!(tm.subsec_nanosecond(), Some(123_456_000));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// Note that when using `%.f`, the fractional component is optional!
    ///
    /// ```
    /// use jiff::fmt::strtime::BrokenDownTime;
    ///
    /// let tm = BrokenDownTime::parse("%S%.f", "1")?;
    /// assert_eq!(tm.second(), Some(1));
    /// assert_eq!(tm.subsec_nanosecond(), None);
    ///
    /// let tm = BrokenDownTime::parse("%S%.f", "1.789")?;
    /// assert_eq!(tm.second(), Some(1));
    /// assert_eq!(tm.subsec_nanosecond(), Some(789_000_000));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn subsec_nanosecond(&self) -> Option<i32> {
        self.subsec.map(|x| x.get())
    }

    /// Returns the parsed offset, if available.
    ///
    /// # Example
    ///
    /// This shows how to parse the offset:
    ///
    /// ```
    /// use jiff::{fmt::strtime::BrokenDownTime, tz::Offset};
    ///
    /// let tm = BrokenDownTime::parse("%z", "-0430")?;
    /// assert_eq!(
    ///     tm.offset(),
    ///     Some(Offset::from_seconds(-4 * 60 * 60 - 30 * 60).unwrap()),
    /// );
    /// let tm = BrokenDownTime::parse("%z", "-043059")?;
    /// assert_eq!(
    ///     tm.offset(),
    ///     Some(Offset::from_seconds(-4 * 60 * 60 - 30 * 60 - 59).unwrap()),
    /// );
    ///
    /// // Or, if you want colons:
    /// let tm = BrokenDownTime::parse("%:z", "-04:30")?;
    /// assert_eq!(
    ///     tm.offset(),
    ///     Some(Offset::from_seconds(-4 * 60 * 60 - 30 * 60).unwrap()),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn offset(&self) -> Option<Offset> {
        self.offset
    }

    /// Returns the parsed weekday, if available.
    ///
    /// # Example
    ///
    /// This shows a few different ways of parsing just a weekday:
    ///
    /// ```
    /// use jiff::{civil::Weekday, fmt::strtime::BrokenDownTime};
    ///
    /// let tm = BrokenDownTime::parse("%A", "Saturday")?;
    /// assert_eq!(tm.weekday(), Some(Weekday::Saturday));
    ///
    /// let tm = BrokenDownTime::parse("%a", "Sat")?;
    /// assert_eq!(tm.weekday(), Some(Weekday::Saturday));
    ///
    /// // A weekday is only available if it is explicitly parsed!
    /// let tm = BrokenDownTime::parse("%F", "2024-07-27")?;
    /// assert_eq!(tm.weekday(), None);
    /// // If you need a weekday derived from a parsed date, then:
    /// assert_eq!(tm.to_date()?.weekday(), Weekday::Saturday);
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// Note that this will return the parsed weekday even if
    /// it's inconsistent with a parsed date:
    ///
    /// ```
    /// use jiff::{civil::{Weekday, date}, fmt::strtime::BrokenDownTime};
    ///
    /// let mut tm = BrokenDownTime::parse("%a, %F", "Wed, 2024-07-27")?;
    /// // 2024-07-27 is a Saturday, but Wednesday was parsed:
    /// assert_eq!(tm.weekday(), Some(Weekday::Wednesday));
    /// // An error only occurs when extracting a date:
    /// assert!(tm.to_date().is_err());
    /// // To skip the weekday, error checking, zero it out first:
    /// tm.set_weekday(None);
    /// assert_eq!(tm.to_date()?, date(2024, 7, 27));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn weekday(&self) -> Option<Weekday> {
        self.weekday
    }

    /// Returns the parsed meridiem, if available.
    ///
    /// Note that unlike other fields, there is no
    /// `BrokenDownTime::set_meridiem`. Instead, when formatting, the meridiem
    /// label (if it's used in the formatting string) is determined purely as a
    /// function of the hour in a 24 hour clock.
    ///
    /// # Example
    ///
    /// This shows a how to parse the meridiem:
    ///
    /// ```
    /// use jiff::fmt::strtime::{BrokenDownTime, Meridiem};
    ///
    /// let tm = BrokenDownTime::parse("%p", "AM")?;
    /// assert_eq!(tm.meridiem(), Some(Meridiem::AM));
    /// let tm = BrokenDownTime::parse("%P", "pm")?;
    /// assert_eq!(tm.meridiem(), Some(Meridiem::PM));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn meridiem(&self) -> Option<Meridiem> {
        self.meridiem
    }

    /// Set the year on this broken down time.
    ///
    /// # Errors
    ///
    /// This returns an error if the given year is out of range.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::fmt::strtime::BrokenDownTime;
    ///
    /// let mut tm = BrokenDownTime::default();
    /// // out of range
    /// assert!(tm.set_year(Some(10_000)).is_err());
    /// tm.set_year(Some(2024))?;
    /// assert_eq!(tm.to_string("%Y")?, "2024");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn set_year(&mut self, year: Option<i16>) -> Result<(), Error> {
        self.year = match year {
            None => None,
            Some(year) => Some(t::Year::try_new("year", year)?),
        };
        Ok(())
    }

    /// Set the month on this broken down time.
    ///
    /// # Errors
    ///
    /// This returns an error if the given month is out of range.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::fmt::strtime::BrokenDownTime;
    ///
    /// let mut tm = BrokenDownTime::default();
    /// // out of range
    /// assert!(tm.set_month(Some(0)).is_err());
    /// tm.set_month(Some(12))?;
    /// assert_eq!(tm.to_string("%B")?, "December");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn set_month(&mut self, month: Option<i8>) -> Result<(), Error> {
        self.month = match month {
            None => None,
            Some(month) => Some(t::Month::try_new("month", month)?),
        };
        Ok(())
    }

    /// Set the day on this broken down time.
    ///
    /// # Errors
    ///
    /// This returns an error if the given day is out of range.
    ///
    /// Note that setting a day to a value that is legal in any context is
    /// always valid, even if it isn't valid for the year and month
    /// components already set.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::fmt::strtime::BrokenDownTime;
    ///
    /// let mut tm = BrokenDownTime::default();
    /// // out of range
    /// assert!(tm.set_day(Some(32)).is_err());
    /// tm.set_day(Some(31))?;
    /// assert_eq!(tm.to_string("%d")?, "31");
    ///
    /// // Works even if the resulting date is invalid.
    /// let mut tm = BrokenDownTime::default();
    /// tm.set_year(Some(2024))?;
    /// tm.set_month(Some(4))?;
    /// tm.set_day(Some(31))?; // April has 30 days, not 31
    /// assert_eq!(tm.to_string("%F")?, "2024-04-31");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn set_day(&mut self, day: Option<i8>) -> Result<(), Error> {
        self.day = match day {
            None => None,
            Some(day) => Some(t::Day::try_new("day", day)?),
        };
        Ok(())
    }

    /// Set the hour on this broken down time.
    ///
    /// # Errors
    ///
    /// This returns an error if the given hour is out of range.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::fmt::strtime::BrokenDownTime;
    ///
    /// let mut tm = BrokenDownTime::default();
    /// // out of range
    /// assert!(tm.set_hour(Some(24)).is_err());
    /// tm.set_hour(Some(0))?;
    /// assert_eq!(tm.to_string("%H")?, "00");
    /// assert_eq!(tm.to_string("%-H")?, "0");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn set_hour(&mut self, hour: Option<i8>) -> Result<(), Error> {
        self.hour = match hour {
            None => None,
            Some(hour) => Some(t::Hour::try_new("hour", hour)?),
        };
        Ok(())
    }

    /// Set the minute on this broken down time.
    ///
    /// # Errors
    ///
    /// This returns an error if the given minute is out of range.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::fmt::strtime::BrokenDownTime;
    ///
    /// let mut tm = BrokenDownTime::default();
    /// // out of range
    /// assert!(tm.set_minute(Some(60)).is_err());
    /// tm.set_minute(Some(59))?;
    /// assert_eq!(tm.to_string("%M")?, "59");
    /// assert_eq!(tm.to_string("%03M")?, "059");
    /// assert_eq!(tm.to_string("%_3M")?, " 59");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn set_minute(&mut self, minute: Option<i8>) -> Result<(), Error> {
        self.minute = match minute {
            None => None,
            Some(minute) => Some(t::Minute::try_new("minute", minute)?),
        };
        Ok(())
    }

    /// Set the second on this broken down time.
    ///
    /// # Errors
    ///
    /// This returns an error if the given second is out of range.
    ///
    /// Jiff does not support leap seconds, so the range of valid seconds is
    /// `0` to `59`, inclusive. Note though that when parsing, a parsed value
    /// of `60` is automatically constrained to `59`.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::fmt::strtime::BrokenDownTime;
    ///
    /// let mut tm = BrokenDownTime::default();
    /// // out of range
    /// assert!(tm.set_second(Some(60)).is_err());
    /// tm.set_second(Some(59))?;
    /// assert_eq!(tm.to_string("%S")?, "59");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn set_second(&mut self, second: Option<i8>) -> Result<(), Error> {
        self.second = match second {
            None => None,
            Some(second) => Some(t::Second::try_new("second", second)?),
        };
        Ok(())
    }

    /// Set the subsecond nanosecond on this broken down time.
    ///
    /// # Errors
    ///
    /// This returns an error if the given number of nanoseconds is out of
    /// range. It must be non-negative and less than 1 whole second.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::fmt::strtime::BrokenDownTime;
    ///
    /// let mut tm = BrokenDownTime::default();
    /// // out of range
    /// assert!(tm.set_subsec_nanosecond(Some(1_000_000_000)).is_err());
    /// tm.set_subsec_nanosecond(Some(123_000_000))?;
    /// assert_eq!(tm.to_string("%f")?, "123");
    /// assert_eq!(tm.to_string("%.6f")?, ".123000");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn set_subsec_nanosecond(
        &mut self,
        subsec_nanosecond: Option<i32>,
    ) -> Result<(), Error> {
        self.subsec = match subsec_nanosecond {
            None => None,
            Some(subsec_nanosecond) => Some(t::SubsecNanosecond::try_new(
                "subsecond-nanosecond",
                subsec_nanosecond,
            )?),
        };
        Ok(())
    }

    /// Set the weekday on this broken down time.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::{civil::Weekday, fmt::strtime::BrokenDownTime};
    ///
    /// let mut tm = BrokenDownTime::default();
    /// tm.set_weekday(Some(Weekday::Saturday));
    /// assert_eq!(tm.to_string("%A")?, "Saturday");
    /// assert_eq!(tm.to_string("%a")?, "Sat");
    /// assert_eq!(tm.to_string("%^a")?, "SAT");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// Note that one use case for this routine is to enable parsing of
    /// weekdays in datetime, but skip checking that the weekday is valid for
    /// the parsed date.
    ///
    /// ```
    /// use jiff::{civil::date, fmt::strtime::BrokenDownTime};
    ///
    /// let mut tm = BrokenDownTime::parse("%a, %F", "Wed, 2024-07-27")?;
    /// // 2024-07-27 was a Saturday, so asking for a date fails:
    /// assert!(tm.to_date().is_err());
    /// // But we can remove the weekday from our broken down time:
    /// tm.set_weekday(None);
    /// assert_eq!(tm.to_date()?, date(2024, 7, 27));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// The advantage of this approach is that it still ensures the parsed
    /// weekday is a valid weekday (for example, `Wat` will cause parsing to
    /// fail), but doesn't require it to be consistent with the date. This
    /// is useful for interacting with systems that don't do strict error
    /// checking.
    #[inline]
    pub fn set_weekday(&mut self, weekday: Option<Weekday>) {
        self.weekday = weekday;
    }
}

impl<'a> From<&'a Zoned> for BrokenDownTime {
    fn from(zdt: &'a Zoned) -> BrokenDownTime {
        let (_, _, tzabbrev) = zdt.time_zone().to_offset(zdt.timestamp());
        BrokenDownTime {
            offset: Some(zdt.offset()),
            tzabbrev: Some(tzabbrev.to_string()),
            ..BrokenDownTime::from(zdt.datetime())
        }
    }
}

impl From<Timestamp> for BrokenDownTime {
    fn from(ts: Timestamp) -> BrokenDownTime {
        let dt = TimeZone::UTC.to_datetime(ts);
        BrokenDownTime {
            offset: Some(Offset::UTC),
            ..BrokenDownTime::from(dt)
        }
    }
}

impl From<DateTime> for BrokenDownTime {
    fn from(dt: DateTime) -> BrokenDownTime {
        let (d, t) = (dt.date(), dt.time());
        BrokenDownTime {
            year: Some(d.year_ranged()),
            month: Some(d.month_ranged()),
            day: Some(d.day_ranged()),
            hour: Some(t.hour_ranged()),
            minute: Some(t.minute_ranged()),
            second: Some(t.second_ranged()),
            subsec: Some(t.subsec_nanosecond_ranged()),
            weekday: Some(d.weekday()),
            meridiem: Some(Meridiem::from(t)),
            ..BrokenDownTime::default()
        }
    }
}

impl From<Date> for BrokenDownTime {
    fn from(d: Date) -> BrokenDownTime {
        BrokenDownTime {
            year: Some(d.year_ranged()),
            month: Some(d.month_ranged()),
            day: Some(d.day_ranged()),
            weekday: Some(d.weekday()),
            ..BrokenDownTime::default()
        }
    }
}

impl From<Time> for BrokenDownTime {
    fn from(t: Time) -> BrokenDownTime {
        BrokenDownTime {
            hour: Some(t.hour_ranged()),
            minute: Some(t.minute_ranged()),
            second: Some(t.second_ranged()),
            subsec: Some(t.subsec_nanosecond_ranged()),
            meridiem: Some(Meridiem::from(t)),
            ..BrokenDownTime::default()
        }
    }
}

/// A "lazy" implementation of `std::fmt::Display` for `strftime`.
///
/// Values of this type are created by the `strftime` methods on the various
/// datetime types in this crate. For example, [`Zoned::strftime`].
///
/// A `Display` captures the information needed from the datetime and waits to
/// do the actual formatting when this type's `std::fmt::Display` trait
/// implementation is actually used.
///
/// # Errors and panics
///
/// This trait implementation returns an error when the underlying formatting
/// can fail. Formatting can fail either because of an invalid format string,
/// or if formatting requires a field in `BrokenDownTime` to be set that isn't.
/// For example, trying to format a [`DateTime`] with the `%z` specifier will
/// fail because a `DateTime` has no time zone or offset information associated
/// with it.
///
/// Note though that the `std::fmt::Display` API doesn't support surfacing
/// arbitrary errors. All errors collapse into the unit `std::fmt::Error`
/// struct. To see the actual error, use [`BrokenDownTime::format`],
/// [`BrokenDownTime::to_string`] or [`strtime::format`](format()).
/// Unfortunately, the `std::fmt::Display` trait is used in many places where
/// there is no way to report errors other than panicking.
///
/// Therefore, only use this type if you know your formatting string is valid
/// and that the datetime type being formatted has all of the information
/// required by the format string. For most conversion specifiers, this falls
/// in the category of things where "if it works, it works for all inputs."
/// Unfortunately, there are some exceptions to this. For example, the `%y`
/// modifier will only format a year if it falls in the range `1969-2068` and
/// will otherwise return an error.
///
/// # Example
///
/// This example shows how to format a zoned datetime using
/// [`Zoned::strftime`]:
///
/// ```
/// use jiff::{civil::date, fmt::strtime, tz};
///
/// let zdt = date(2024, 7, 15).at(16, 24, 59, 0).intz("America/New_York")?;
/// let string = zdt.strftime("%a, %-d %b %Y %T %z").to_string();
/// assert_eq!(string, "Mon, 15 Jul 2024 16:24:59 -0400");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// Or use it directly when writing to something:
///
/// ```
/// use jiff::{civil::date, fmt::strtime, tz};
///
/// let zdt = date(2024, 7, 15).at(16, 24, 59, 0).intz("America/New_York")?;
///
/// let string = format!("the date is: {}", zdt.strftime("%-m/%-d/%-Y"));
/// assert_eq!(string, "the date is: 7/15/2024");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
pub struct Display<'f> {
    pub(crate) fmt: &'f [u8],
    pub(crate) tm: BrokenDownTime,
}

impl<'f> core::fmt::Display for Display<'f> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        use crate::fmt::StdFmtWrite;

        self.tm.format(self.fmt, StdFmtWrite(f)).map_err(|_| core::fmt::Error)
    }
}

impl<'f> core::fmt::Debug for Display<'f> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("Display")
            .field("fmt", &escape::Bytes(self.fmt))
            .field("tm", &self.tm)
            .finish()
    }
}

/// A label to disambiguate hours on a 12-hour clock.
///
/// This can be accessed on a [`BrokenDownTime`] via
/// [`BrokenDownTime::meridiem`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Meridiem {
    /// "ante meridiem" or "before midday."
    ///
    /// Specifically, this describes hours less than 12 on a 24-hour clock.
    AM,
    /// "post meridiem" or "after midday."
    ///
    /// Specifically, this describes hours greater than 11 on a 24-hour clock.
    PM,
}

impl From<Time> for Meridiem {
    fn from(t: Time) -> Meridiem {
        if t.hour() < 12 {
            Meridiem::AM
        } else {
            Meridiem::PM
        }
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
    /// Parses an optional directive flag from the beginning of `fmt`. This
    /// assumes `fmt` is not empty and guarantees that the return unconsumed
    /// slice is also non-empty.
    #[inline(always)]
    fn parse_flag<'i>(
        fmt: &'i [u8],
    ) -> Result<(Option<Flag>, &'i [u8]), Error> {
        let byte = fmt[0];
        let flag = match byte {
            b'_' => Flag::PadSpace,
            b'0' => Flag::PadZero,
            b'-' => Flag::NoPad,
            b'^' => Flag::Uppercase,
            b'#' => Flag::Swapcase,
            _ => return Ok((None, fmt)),
        };
        let fmt = &fmt[1..];
        if fmt.is_empty() {
            return Err(err!(
                "expected to find specifier directive after flag \
                 {byte:?}, but found end of format string",
                byte = escape::Byte(byte),
            ));
        }
        Ok((Some(flag), fmt))
    }

    /// Parses an optional width that comes after a (possibly absent) flag and
    /// before the specifier directive itself. And if a width is parsed, the
    /// slice returned does not contain it. (If that slice is empty, then an
    /// error is returned.)
    ///
    /// Note that this is also used to parse precision settings for `%f`
    /// and `%.f`. In the former case, the width is just re-interpreted as
    /// a precision setting. In the latter case, something like `%5.9f` is
    /// technically valid, but the `5` is ignored.
    #[inline(always)]
    fn parse_width<'i>(
        fmt: &'i [u8],
    ) -> Result<(Option<u8>, &'i [u8]), Error> {
        let mut digits = 0;
        while digits < fmt.len() && fmt[digits].is_ascii_digit() {
            digits += 1;
        }
        if digits == 0 {
            return Ok((None, fmt));
        }
        let (digits, fmt) = util::parse::split(fmt, digits).unwrap();
        let width = util::parse::i64(digits)
            .context("failed to parse conversion specifier width")?;
        let width = u8::try_from(width).map_err(|_| {
            err!("{width} is too big, max is {max}", max = u8::MAX)
        })?;
        if fmt.is_empty() {
            return Err(err!(
                "expected to find specifier directive after width \
                 {width}, but found end of format string",
            ));
        }
        Ok((Some(width), fmt))
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

/// Returns the "full" weekday name.
fn weekday_name_full(wd: Weekday) -> &'static str {
    match wd {
        Weekday::Sunday => "Sunday",
        Weekday::Monday => "Monday",
        Weekday::Tuesday => "Tuesday",
        Weekday::Wednesday => "Wednesday",
        Weekday::Thursday => "Thursday",
        Weekday::Friday => "Friday",
        Weekday::Saturday => "Saturday",
    }
}

/// Returns an abbreviated weekday name.
fn weekday_name_abbrev(wd: Weekday) -> &'static str {
    match wd {
        Weekday::Sunday => "Sun",
        Weekday::Monday => "Mon",
        Weekday::Tuesday => "Tue",
        Weekday::Wednesday => "Wed",
        Weekday::Thursday => "Thu",
        Weekday::Friday => "Fri",
        Weekday::Saturday => "Sat",
    }
}

/// Returns the "full" month name.
fn month_name_full(month: t::Month) -> &'static str {
    match month.get() {
        1 => "January",
        2 => "February",
        3 => "March",
        4 => "April",
        5 => "May",
        6 => "June",
        7 => "July",
        8 => "August",
        9 => "September",
        10 => "October",
        11 => "November",
        12 => "December",
        unk => unreachable!("invalid month {unk}"),
    }
}

/// Returns the abbreviated month name.
fn month_name_abbrev(month: t::Month) -> &'static str {
    match month.get() {
        1 => "Jan",
        2 => "Feb",
        3 => "Mar",
        4 => "Apr",
        5 => "May",
        6 => "Jun",
        7 => "Jul",
        8 => "Aug",
        9 => "Sep",
        10 => "Oct",
        11 => "Nov",
        12 => "Dec",
        unk => unreachable!("invalid month {unk}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // See: https://github.com/BurntSushi/jiff/issues/62
    #[test]
    fn parse_non_delimited() {
        insta::assert_snapshot!(
            Timestamp::strptime("%Y%m%d-%H%M%S%z", "20240730-005625+0400").unwrap(),
            @"2024-07-29T20:56:25Z",
        );
        insta::assert_snapshot!(
            Zoned::strptime("%Y%m%d-%H%M%S%z", "20240730-005625+0400").unwrap(),
            @"2024-07-30T00:56:25+04:00[+04:00]",
        );
    }
}
