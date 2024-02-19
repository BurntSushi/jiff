/*!
Support for "printf" style parsing and formatting.

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
The pattern language is a simple sequence of greedy conversion specifiers
interspersed by literals and arbitrary whitespace. This means that you usually
need delimiters or spaces between components. For example, this is fine:

```
use jiff::fmt::strtime;

let date = strtime::parse("%Y %m %d", "2024 7 15")?.to_date()?;
assert_eq!(date.to_string(), "2024-07-15");
# Ok::<(), Box<dyn std::error::Error>>(())
```

But this is ambiguous:

```
use jiff::fmt::strtime;

assert_eq!(
    strtime::parse("%Y%m%d", "2024715").unwrap_err().to_string(),
    "strptime parsing failed: %Y failed: year number is invalid: \
     parameter 'year' with value 2024715 is not in the required range of -9999..=9999",
);
```

You can think of numerical conversion specifiers as regexes like `[0-9]+`.
The difference is that a regex like `([0-9]+)([0-9]+)([0-9]+)` would match the
above string, but even then, the specific values of each capture group wouldn't
be what you wanted. In a regex, you can control the number of digits, e.g.,
`([0-9]{4})([0-9]{1})([0-9]{2})`, but there is no such mechanism for the
parsing supported by `strptime`.

On top of all of that, the parsing and formatting in this module does not
currently support IANA time zone identifiers. This means that it isn't suitable
as an interchange format. And time zone abbreviations, i.e., `%Z` when
formatting, aren't supported when parsing because time zone abbreviations are
ambiguous.

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
formatting machinery will be improved. (Although it is plausible to add new
conversion specifiers.)

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
| `%Z` | `EDT` | A time zone abbreviation. Supporting when formatting only. |
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
absent) flag and before the directive. The number formed by these digits will
correspond to the minimum amount of padding (to the left).

The flags and padding amount above may be used when parsing as well, but they
are ignored since parsing supports all of the different flag modes all of the
time.

# Unsupported

The following things are currently unsupported:

* Parsing or formatting IANA time zone identifiers.
* Parsing or formatting fractional seconds in either the clock time or time
time zone offset.
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
        escape,
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
        let mut time = self.to_time_without_meridiem()?;
        if let Some(meridiem) = self.meridiem {
            let hour = time.hour_ranged();
            let hour = match meridiem {
                Meridiem::AM => hour % C(12),
                Meridiem::PM => (hour % C(12)) + C(12),
            };
            time = Time::new_ranged(
                hour,
                time.minute_ranged(),
                time.second_ranged(),
                time.subsec_nanosecond_ranged(),
            );
        }
        Ok(time)
    }

    #[inline]
    fn to_time_without_meridiem(&self) -> Result<Time, Error> {
        let Some(hour) = self.hour else {
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
            return Ok(Time::new_ranged(hour, C(0), C(0), C(0)));
        };
        let Some(second) = self.second else {
            return Ok(Time::new_ranged(hour, minute, C(0), C(0)));
        };
        Ok(Time::new_ranged(hour, minute, second, C(0)))
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
/// struct. To see the actual error, use [`BrokenDownTime::format`] or
/// [`strtime::format`](format()). And unfortunately, the `std::fmt::Display`
/// trait is used in many places where there is no way to report errors other
/// than panicking.
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

#[derive(Clone, Copy, Debug)]
enum Meridiem {
    AM,
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
