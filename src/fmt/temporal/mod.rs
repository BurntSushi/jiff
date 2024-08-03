/*!
A hybrid format derived from [RFC 3339], [RFC 9557] and [ISO 8601].

This module provides an implementation of the [Temporal ISO 8601 grammar]. The
API is spread out over parsers and printers for datetimes and spans.

Note that for most use cases, you should be using the corresponding
[`Display`](std::fmt::Display) or [`FromStr`](std::str::FromStr) trait
implementations for printing and parsing respectively. This module provides
a "lower level" API for configuring the behavior of printing and parsing,
including the ability to parse from byte strings (i.e., `&[u8]`).

# Date and time format

The specific format supported depends on what kind of type you're trying to
parse into. Here are some examples to give a general idea:

* `02:21:58` parses into a [`civil::Time`].
* `2020-08-21` parses into a [`civil::Date`].
* `2020-08-21T02:21:58` and `2020-08-21 02:21:58` both parse into a
  [`civil::DateTime`].
* `2020-08-21T02:21:58-04` parses into an [`Timestamp`].
* `2020-08-21T02:21:58-04[America/New_York]` parses into a [`Zoned`].

Smaller types can generally be parsed from strings representing a bigger type.
For example, a `civil::Date` can be parsed from `2020-08-21T02:21:58`.

As mentioned above, the datetime format supported by Jiff is a hybrid of the
"best" parts of [RFC 3339], [RFC 9557] and [ISO 8601]. Generally speaking, [RFC
3339] and [RFC 9557] are supported in their entirety, but not all of ISO 8601
is. For example, `2024-06-16T10.5` is a valid ISO 8601 datetime, but isn't
supported by Jiff. (Only fractional seconds are supported.)

Some additional details worth noting:

* Parsing `Zoned` values requires a datetime string with a time zone
annotation like `[America/New_York]` or `[-07:00]`. If you need to parse a
datetime without a time zone annotation (but with an offset), then you should
parse it as an [`Timestamp`]. From there, it can be converted to a `Zoned` via
[`Timestamp::to_zoned`].
* When parsing `Zoned` values, ambiguous datetimes are handled via the
[`DateTimeParser::disambiguation`] configuration. By default, a "compatible"
mode is used where the earlier time is selected in a backward transition, while
the later time is selected in a forward transition.
* When parsing `Zoned` values, conflicts between the offset and the time zone
in the datetime string are handled via the [`DateTimeParser::offset_conflict`]
configuration. By default, any inconsistency between the offset and the time
zone results in a parse error.
* When parsing civil types like `civil::DateTime`, it's always an error if the
datetime string has a `Z` (Zulu) offset. It's an error since interpreting such
strings as civil time is usually a bug.
* In all cases, the `T` designator separating the date and time may be an ASCII
space instead.

The complete datetime format supported is described by the
[Temporal ISO 8601 grammar].

# Span format

To a first approximation, the span format supported roughly corresponds to this
regular expression:

```text
P(\d+y)?(\d+m)?(\d+w)?(\d+d)?(T(\d+h)?(\d+m)?(\d+s)?)?
```

But there are some details not easily captured by a simple regular expression:

* At least one unit must be specified. To write a zero span, specify `0` for
any unit. For example, `P0d` and `PT0s` are equivalent.
* The format is case insensitive. The printer will by default capitalize the
`P` and `T` designators, but lowercase the unit designators.
* Hours, minutes or seconds may be fractional. And the only units that may be
fractional are the lowest units.
* A span like `P99999999999y` is invalid because it exceeds the allowable range
of time representable by a [`Span`].

This is, roughly speaking, a subset of what [ISO 8601] specifies. It isn't
strictly speaking a subset since Jiff (like Temporal) permits week units to be
mixed with other units.

Here are some examples:

```
use jiff::{Span, ToSpan};

let spans = [
    ("P40D", 40.days()),
    ("P1y1d", 1.year().days(1)),
    ("P3dT4h59m", 3.days().hours(4).minutes(59)),
    ("PT2H30M", 2.hours().minutes(30)),
    ("P1m", 1.month()),
    ("P1w", 1.week()),
    ("P1w4d", 1.week().days(4)),
    ("PT1m", 1.minute()),
    ("PT0.0021s", 2.milliseconds().microseconds(100)),
    ("PT0s", 0.seconds()),
    ("P0d", 0.seconds()),
    (
        "P1y1m1dT1h1m1.1s",
        1.year().months(1).days(1).hours(1).minutes(1).seconds(1).milliseconds(100),
    ),
];
for (string, span) in spans {
    let parsed: Span = string.parse()?;
    assert_eq!(span, parsed, "result of parsing {string:?}");
}

# Ok::<(), Box<dyn std::error::Error>>(())
```

The complete span format supported is described by the [Temporal ISO 8601
grammar].

# Differences with Temporal

Jiff implements Temporal's grammar pretty closely, but there are a few
differences at the time of writing. It is a specific goal that all differences
should be rooted in what Jiff itself supports, and not in the grammar itself.

* The maximum UTC offset value expressible is `25:59:59` in Jiff, where as in
Temporal it's `23:59:59.999999999`. Jiff supports a slightly bigger maximum
to account for all valid values of POSIX time zone strings. Jiff also lacks
nanosecond precision for UTC offsets, as it's not clear how useful that is in
practice.
* Jiff doesn't support a datetime range as big as Temporal. For example,
in Temporal, `+202024-06-14T17:30[America/New_York]` is valid. But in Jiff,
since the maximum supported year is `9999`, parsing will fail. Jiff's datetime
range may be expanded in the future, but it is a non-goal to match Temporal's
range precisely.
* Jiff doesn't support RFC 9557 calendar annotations because Jiff only supports
the Gregorian calendar.

There is some more [background on Temporal's format] available.

[Temporal ISO 8601 grammar]: https://tc39.es/proposal-temporal/#sec-temporal-iso8601grammar
[RFC 3339]: https://www.rfc-editor.org/rfc/rfc3339
[RFC 9557]: https://www.rfc-editor.org/rfc/rfc9557.html
[ISO 8601]: https://www.iso.org/iso-8601-date-and-time-format.html
[background on Temporal's format]: https://github.com/tc39/proposal-temporal/issues/2843
*/

use crate::{
    civil,
    error::Error,
    fmt::Write,
    span::Span,
    tz::{Disambiguation, OffsetConflict, TimeZoneDatabase},
    Timestamp, Zoned,
};

mod parser;
mod printer;

/// The default date time parser that we use throughout Jiff.
pub(crate) static DEFAULT_DATETIME_PARSER: DateTimeParser =
    DateTimeParser::new();

/// The default date time printer that we use throughout Jiff.
pub(crate) static DEFAULT_DATETIME_PRINTER: DateTimePrinter =
    DateTimePrinter::new();

/// The default date time parser that we use throughout Jiff.
pub(crate) static DEFAULT_SPAN_PARSER: SpanParser = SpanParser::new();

/// The default date time printer that we use throughout Jiff.
pub(crate) static DEFAULT_SPAN_PRINTER: SpanPrinter = SpanPrinter::new();

/// A parser for Temporal datetimes.
///
/// This parser converts a machine (but also human) readable format of a
/// datetime to the various types found in Jiff: [`Zoned`], [`Timestamp`],
/// [`civil::DateTime`], [`civil::Date`] or [`civil::Time`]. Note that all
/// of those types provide [`FromStr`](core::str::FromStr) implementations
/// that utilize the default configuration of this parser. However, this parser
/// can be configured to behave differently and can also parse directly from
/// a `&[u8]`.
///
/// See the [`fmt::temporal`](crate::fmt::temporal) module documentation for
/// more information on the specific format used.
///
/// # Example
///
/// This example shows how to parse a `Zoned` datetime from a byte string.
/// (That is, `&[u8]` and not a `&str`.)
///
/// ```
/// use jiff::{civil::date, fmt::temporal::DateTimeParser, tz};
///
/// // A parser can be created in a const context.
/// static PARSER: DateTimeParser = DateTimeParser::new();
///
/// let zdt = PARSER.parse_zoned(b"2024-06-15T07-04[America/New_York]")?;
/// assert_eq!(zdt.datetime(), date(2024, 6, 15).at(7, 0, 0, 0));
/// assert_eq!(zdt.time_zone(), &tz::db().get("America/New_York")?);
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// Note that an ASCII space instead of the `T` separator is automatically
/// supported too:
///
/// ```
/// use jiff::{civil::date, fmt::temporal::DateTimeParser, tz};
///
/// // A parser can be created in a const context.
/// static PARSER: DateTimeParser = DateTimeParser::new();
///
/// let zdt = PARSER.parse_zoned(b"2024-06-15 07-04[America/New_York]")?;
/// assert_eq!(zdt.datetime(), date(2024, 6, 15).at(7, 0, 0, 0));
/// assert_eq!(zdt.time_zone(), &tz::db().get("America/New_York")?);
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Debug)]
pub struct DateTimeParser {
    p: parser::DateTimeParser,
    offset_conflict: OffsetConflict,
    disambiguation: Disambiguation,
}

impl DateTimeParser {
    /// Create a new Temporal datetime parser with the default configuration.
    pub const fn new() -> DateTimeParser {
        DateTimeParser {
            p: parser::DateTimeParser::new(),
            offset_conflict: OffsetConflict::Reject,
            disambiguation: Disambiguation::Compatible,
        }
    }

    /// Set the conflict resolution strategy for when an offset in a datetime
    /// string is inconsistent with the time zone.
    ///
    /// See the documentation on [`OffsetConflict`] for more details about the
    /// different strategies one can choose.
    ///
    /// This only applies when parsing [`Zoned`] values.
    ///
    /// The default is [`OffsetConflict::Reject`], which results in an error
    /// whenever parsing a datetime with an offset that is inconsistent with
    /// the time zone.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::{civil::date, fmt::temporal::DateTimeParser, tz};
    ///
    /// static PARSER: DateTimeParser = DateTimeParser::new()
    ///     .offset_conflict(tz::OffsetConflict::AlwaysOffset);
    ///
    /// let zdt = PARSER.parse_zoned("2024-06-09T07:00-05[America/New_York]")?;
    /// // Notice that the time *and* offset have been corrected. The offset
    /// // given was invalid for `America/New_York` at the given time, so
    /// // it cannot be kept, but the instant returned is equivalent to
    /// // `2024-06-09T07:00-05`. It is just adjusted automatically to be
    /// // correct in the `America/New_York` time zone.
    /// assert_eq!(zdt.datetime(), date(2024, 6, 9).at(8, 0, 0, 0));
    /// assert_eq!(zdt.offset(), tz::offset(-4));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub const fn offset_conflict(
        self,
        strategy: OffsetConflict,
    ) -> DateTimeParser {
        DateTimeParser { offset_conflict: strategy, ..self }
    }

    /// Set the disambiguation strategy for when a datetime falls into a time
    /// zone transition "fold" or "gap."
    ///
    /// The most common manifestation of such time zone transitions is daylight
    /// saving time. In most cases, the transition into daylight saving time
    /// moves the civil time ("the time you see on the clock") ahead one hour.
    /// This is called a "gap" because an hour on the clock is skipped. While
    /// the transition out of daylight saving time moves the civil time back
    /// one hour. This is called a "fold" because an hour on the clock is
    /// repeated.
    ///
    /// In the case of a gap, an ambiguous datetime manifests as a time that
    /// never appears on a clock. (For example, `02:30` on `2024-03-10` in New
    /// York.) In the case of a fold, an ambiguous datetime manifests as a
    /// time that repeats itself. (For example, `01:30` on `2024-11-03` in New
    /// York.) So when a fold occurs, you don't know whether it's the "first"
    /// occurrence of that time or the "second."
    ///
    /// Time zone transitions are not just limited to daylight saving time,
    /// although those are the most common. In other cases, a transition occurs
    /// because of a change in the offset of the time zone itself. (See the
    /// examples below.)
    ///
    /// # Example
    ///
    /// This example shows how to set the disambiguation configuration while
    /// parsing a [`Zoned`] datetime. In this example, we always prefer the
    /// earlier time.
    ///
    /// ```
    /// use jiff::{civil::date, fmt::temporal::DateTimeParser, tz};
    ///
    /// static PARSER: DateTimeParser = DateTimeParser::new()
    ///     .disambiguation(tz::Disambiguation::Earlier);
    ///
    /// let zdt = PARSER.parse_zoned("2024-03-10T02:05[America/New_York]")?;
    /// assert_eq!(zdt.datetime(), date(2024, 3, 10).at(1, 5, 0, 0));
    /// assert_eq!(zdt.offset(), tz::offset(-5));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: time zone offset change
    ///
    /// In this example, we explore a time zone offset change in Hawaii that
    /// occurred on `1947-06-08`. Namely, Hawaii went from a `-10:30` offset
    /// to a `-10:00` offset at `02:00`. This results in a 30 minute gap in
    /// civil time.
    ///
    /// ```
    /// use jiff::{civil::date, fmt::temporal::DateTimeParser, tz, ToSpan};
    ///
    /// static PARSER: DateTimeParser = DateTimeParser::new()
    ///     .disambiguation(tz::Disambiguation::Later);
    ///
    /// // 02:05 didn't exist on clocks on 1947-06-08.
    /// let zdt = PARSER.parse_zoned(
    ///     "1947-06-08T02:05[Pacific/Honolulu]",
    /// )?;
    /// // Our parser is configured to select the later time, so we jump to
    /// // 02:35. But if we used `Disambiguation::Earlier`, then we'd get
    /// // 01:35.
    /// assert_eq!(zdt.datetime(), date(1947, 6, 8).at(2, 35, 0, 0));
    /// assert_eq!(zdt.offset(), tz::offset(-10));
    ///
    /// // If we subtract 10 minutes from 02:35, notice that we (correctly)
    /// // jump to 01:55 *and* our offset is corrected to -10:30.
    /// let zdt = zdt.checked_sub(10.minutes())?;
    /// assert_eq!(zdt.datetime(), date(1947, 6, 8).at(1, 55, 0, 0));
    /// assert_eq!(zdt.offset(), tz::offset(-10).saturating_sub(30.minutes()));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub const fn disambiguation(
        self,
        strategy: Disambiguation,
    ) -> DateTimeParser {
        DateTimeParser { disambiguation: strategy, ..self }
    }

    /// Parse a datetime string with a time zone annotation into a [`Zoned`]
    /// value using the system time zone database.
    ///
    /// # Errors
    ///
    /// This returns an error if the datetime string given is invalid or if it
    /// is valid but doesn't fit in the datetime range supported by Jiff.
    ///
    /// The [`DateTimeParser::offset_conflict`] and
    /// [`DateTimeParser::disambiguation`] settings can also influence
    /// whether an error occurs or not. Namely, if [`OffsetConflict::Reject`]
    /// is used (which is the default), then an error occurs when there
    /// is an inconsistency between the offset and the time zone. And if
    /// [`Disambiguation::Reject`] is used, then an error occurs when the civil
    /// time in the string is ambiguous.
    ///
    /// # Example: parsing without an IANA time zone
    ///
    /// Note that when parsing a `Zoned` value, it is required for the datetime
    /// string to contain a time zone annotation in brackets. For example,
    /// this fails to parse even though it refers to a precise instant in time:
    ///
    /// ```
    /// use jiff::fmt::temporal::DateTimeParser;
    ///
    /// static PARSER: DateTimeParser = DateTimeParser::new();
    ///
    /// assert!(PARSER.parse_zoned("2024-06-08T07:00-04").is_err());
    /// ```
    ///
    /// While it is better to include a time zone name, if the only thing
    /// that's available is an offset, the offset can be repeated as a time
    /// zone annotation:
    ///
    /// ```
    /// use jiff::{civil::date, fmt::temporal::DateTimeParser, tz};
    ///
    /// static PARSER: DateTimeParser = DateTimeParser::new();
    ///
    /// let zdt = PARSER.parse_zoned("2024-06-08T07:00-04[-04]")?;
    /// assert_eq!(zdt.datetime(), date(2024, 6, 8).at(7, 0, 0, 0));
    /// assert_eq!(zdt.offset(), tz::offset(-4));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// Otherwise, if you need to be able to parse something like
    /// `2024-06-08T07:00-04` as-is, you should parse it into an [`Timestamp`]:
    ///
    /// ```
    /// use jiff::{civil::date, fmt::temporal::DateTimeParser, tz};
    ///
    /// static PARSER: DateTimeParser = DateTimeParser::new();
    ///
    /// let timestamp = PARSER.parse_timestamp("2024-06-08T07:00-04")?;
    /// let zdt = timestamp.to_zoned(tz::TimeZone::UTC);
    /// assert_eq!(zdt.datetime(), date(2024, 6, 8).at(11, 0, 0, 0));
    /// assert_eq!(zdt.offset(), tz::offset(0));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub fn parse_zoned<I: AsRef<[u8]>>(
        &self,
        input: I,
    ) -> Result<Zoned, Error> {
        self.parse_zoned_with(crate::tz::db(), input)
    }

    /// Parse a datetime string with a time zone annotation into a [`Zoned`]
    /// value using the time zone database given.
    ///
    /// # Errors
    ///
    /// This returns an error if the datetime string given is invalid or if it
    /// is valid but doesn't fit in the datetime range supported by Jiff.
    ///
    /// The [`DateTimeParser::offset_conflict`] and
    /// [`DateTimeParser::disambiguation`] settings can also influence
    /// whether an error occurs or not. Namely, if [`OffsetConflict::Reject`]
    /// is used (which is the default), then an error occurs when there
    /// is an inconsistency between the offset and the time zone. And if
    /// [`Disambiguation::Reject`] is used, then an error occurs when the civil
    /// time in the string is ambiguous.
    ///
    /// # Example
    ///
    /// This example demonstrates the utility of this routine by parsing a
    /// datetime using an older copy of the IANA Time Zone Database. This
    /// example leverages the fact that the 2018 copy of `tzdb` preceded
    /// Brazil's announcement that daylight saving time would be abolished.
    /// This meant that datetimes in the future, when parsed with the older
    /// copy of `tzdb`, would still follow the old daylight saving time rules.
    /// But a mere update of `tzdb` would otherwise change the meaning of the
    /// datetime.
    ///
    /// This scenario can come up if one stores datetimes in the future.
    /// This is also why the default offset conflict resolution strategy
    /// is [`OffsetConflict::Reject`], which prevents one from silently
    /// re-interpreting datetimes to a different timestamp.
    ///
    /// ```no_run
    /// use jiff::{fmt::temporal::DateTimeParser, tz::{self, TimeZoneDatabase}};
    ///
    /// static PARSER: DateTimeParser = DateTimeParser::new();
    ///
    /// // Open a version of tzdb from before Brazil announced its abolition
    /// // of daylight saving time.
    /// let tzdb2018 = TimeZoneDatabase::from_dir("path/to/tzdb-2018b")?;
    /// // Open the system tzdb.
    /// let tzdb = tz::db();
    ///
    /// // Parse the same datetime string with the same parser, but using two
    /// // different versions of tzdb.
    /// let dt = "2020-01-15T12:00[America/Sao_Paulo]";
    /// let zdt2018 = PARSER.parse_zoned_with(&tzdb2018, dt)?;
    /// let zdt = PARSER.parse_zoned_with(tzdb, dt)?;
    ///
    /// // Before DST was abolished, 2020-01-15 was in DST, which corresponded
    /// // to UTC offset -02. Since DST rules applied to datetimes in the
    /// // future, the 2018 version of tzdb would lead one to interpret
    /// // 2020-01-15 as being in DST.
    /// assert_eq!(zdt2018.offset(), tz::offset(-2));
    /// // But DST was abolished in 2019, which means that 2020-01-15 was no
    /// // no longer in DST. So after a tzdb update, the same datetime as above
    /// // now has a different offset.
    /// assert_eq!(zdt.offset(), tz::offset(-3));
    ///
    /// // So if you try to parse a datetime serialized from an older copy of
    /// // tzdb, you'll get an error under the default configuration because
    /// // of `OffsetConflict::Reject`. This would succeed if you parsed it
    /// // using tzdb2018!
    /// assert!(PARSER.parse_zoned_with(tzdb, zdt2018.to_string()).is_err());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub fn parse_zoned_with<I: AsRef<[u8]>>(
        &self,
        db: &TimeZoneDatabase,
        input: I,
    ) -> Result<Zoned, Error> {
        let input = input.as_ref();
        let parsed = self.p.parse_temporal_datetime(input)?;
        let dt = parsed.into_full()?;
        let zoned =
            dt.to_zoned(db, self.offset_conflict, self.disambiguation)?;
        Ok(zoned)
    }

    /// Parse a datetime string into a [`Timestamp`].
    ///
    /// The datetime string must correspond to a specific instant in time. This
    /// requires an offset in the datetime string.
    ///
    /// # Errors
    ///
    /// This returns an error if the datetime string given is invalid or if it
    /// is valid but doesn't fit in the datetime range supported by Jiff.
    ///
    /// # Example
    ///
    /// This shows a basic example of parsing an `Timestamp`.
    ///
    /// ```
    /// use jiff::fmt::temporal::DateTimeParser;
    ///
    /// static PARSER: DateTimeParser = DateTimeParser::new();
    ///
    /// let timestamp = PARSER.parse_timestamp("2024-03-10T02:05-04")?;
    /// assert_eq!(timestamp.to_string(), "2024-03-10T06:05:00Z");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: parsing a timestamp from a datetime with a time zone
    ///
    /// A timestamp can also be parsed fron a time zone aware datetime string.
    /// The time zone is ignored and the offset is always used.
    ///
    /// ```
    /// use jiff::fmt::temporal::DateTimeParser;
    ///
    /// static PARSER: DateTimeParser = DateTimeParser::new();
    ///
    /// let timestamp = PARSER.parse_timestamp(
    ///     "2024-03-10T02:05-04[America/New_York]",
    /// )?;
    /// assert_eq!(timestamp.to_string(), "2024-03-10T06:05:00Z");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub fn parse_timestamp<I: AsRef<[u8]>>(
        &self,
        input: I,
    ) -> Result<Timestamp, Error> {
        let input = input.as_ref();
        let parsed = self.p.parse_temporal_datetime(input)?;
        let dt = parsed.into_full()?;
        let timestamp = dt.to_timestamp()?;
        Ok(timestamp)
    }

    /// Parse a civil datetime string into a [`civil::DateTime`].
    ///
    /// A civil datetime can be parsed from anything that contains a datetime.
    /// For example, a time zone aware string.
    ///
    /// # Errors
    ///
    /// This returns an error if the datetime string given is invalid or if it
    /// is valid but doesn't fit in the datetime range supported by Jiff.
    ///
    /// This also returns an error if a `Z` (Zulu) offset is found, since
    /// interpreting such strings as civil time is usually a bug.
    ///
    /// # Example
    ///
    /// This shows a basic example of parsing a `civil::DateTime`.
    ///
    /// ```
    /// use jiff::{civil::date, fmt::temporal::DateTimeParser};
    ///
    /// static PARSER: DateTimeParser = DateTimeParser::new();
    ///
    /// let datetime = PARSER.parse_datetime("2024-03-10T02:05")?;
    /// assert_eq!(datetime, date(2024, 3, 10).at(2, 5, 0, 0));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: parsing fails if a `Z` (Zulu) offset is encountered
    ///
    /// Because parsing a datetime with a `Z` offset and interpreting it as
    /// a civil time is usually a bug, it is forbidden:
    ///
    /// ```
    /// use jiff::{civil::date, fmt::temporal::DateTimeParser};
    ///
    /// static PARSER: DateTimeParser = DateTimeParser::new();
    ///
    /// assert!(PARSER.parse_datetime("2024-03-10T02:05Z").is_err());
    ///
    /// // Note though that -00 and +00 offsets parse successfully.
    /// let datetime = PARSER.parse_datetime("2024-03-10T02:05+00")?;
    /// assert_eq!(datetime, date(2024, 3, 10).at(2, 5, 0, 0));
    /// let datetime = PARSER.parse_datetime("2024-03-10T02:05-00")?;
    /// assert_eq!(datetime, date(2024, 3, 10).at(2, 5, 0, 0));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub fn parse_datetime<I: AsRef<[u8]>>(
        &self,
        input: I,
    ) -> Result<civil::DateTime, Error> {
        let input = input.as_ref();
        let parsed = self.p.parse_temporal_datetime(input)?;
        let dt = parsed.into_full()?;
        let datetime = dt.to_datetime()?;
        Ok(datetime)
    }

    /// Parse a civil date string into a [`civil::Date`].
    ///
    /// A civil date can be parsed from anything that contains a date. For
    /// example, a time zone aware string.
    ///
    /// # Errors
    ///
    /// This returns an error if the date string given is invalid or if it
    /// is valid but doesn't fit in the date range supported by Jiff.
    ///
    /// This also returns an error if a `Z` (Zulu) offset is found, since
    /// interpreting such strings as civil date or time is usually a bug.
    ///
    /// # Example
    ///
    /// This shows a basic example of parsing a `civil::Date`.
    ///
    /// ```
    /// use jiff::{civil::date, fmt::temporal::DateTimeParser};
    ///
    /// static PARSER: DateTimeParser = DateTimeParser::new();
    ///
    /// let d = PARSER.parse_date("2024-03-10")?;
    /// assert_eq!(d, date(2024, 3, 10));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: parsing fails if a `Z` (Zulu) offset is encountered
    ///
    /// Because parsing a date with a `Z` offset and interpreting it as
    /// a civil date or time is usually a bug, it is forbidden:
    ///
    /// ```
    /// use jiff::{civil::date, fmt::temporal::DateTimeParser};
    ///
    /// static PARSER: DateTimeParser = DateTimeParser::new();
    ///
    /// assert!(PARSER.parse_date("2024-03-10T00:00:00Z").is_err());
    ///
    /// // Note though that -00 and +00 offsets parse successfully.
    /// let d = PARSER.parse_date("2024-03-10T00:00:00+00")?;
    /// assert_eq!(d, date(2024, 3, 10));
    /// let d = PARSER.parse_date("2024-03-10T00:00:00-00")?;
    /// assert_eq!(d, date(2024, 3, 10));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub fn parse_date<I: AsRef<[u8]>>(
        &self,
        input: I,
    ) -> Result<civil::Date, Error> {
        let input = input.as_ref();
        let parsed = self.p.parse_temporal_datetime(input)?;
        let dt = parsed.into_full()?;
        let date = dt.to_date()?;
        Ok(date)
    }

    /// Parse a civil time string into a [`civil::Time`].
    ///
    /// A civil time can be parsed from anything that contains a time.
    /// For example, a time zone aware string.
    ///
    /// # Errors
    ///
    /// This returns an error if the time string given is invalid or if it
    /// is valid but doesn't fit in the time range supported by Jiff.
    ///
    /// This also returns an error if a `Z` (Zulu) offset is found, since
    /// interpreting such strings as civil time is usually a bug.
    ///
    /// # Example
    ///
    /// This shows a basic example of parsing a `civil::Time`.
    ///
    /// ```
    /// use jiff::{civil::time, fmt::temporal::DateTimeParser};
    ///
    /// static PARSER: DateTimeParser = DateTimeParser::new();
    ///
    /// let t = PARSER.parse_time("02:05")?;
    /// assert_eq!(t, time(2, 5, 0, 0));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// # Example: parsing fails if a `Z` (Zulu) offset is encountered
    ///
    /// Because parsing a time with a `Z` offset and interpreting it as
    /// a civil time is usually a bug, it is forbidden:
    ///
    /// ```
    /// use jiff::{civil::time, fmt::temporal::DateTimeParser};
    ///
    /// static PARSER: DateTimeParser = DateTimeParser::new();
    ///
    /// assert!(PARSER.parse_time("02:05Z").is_err());
    ///
    /// // Note though that -00 and +00 offsets parse successfully.
    /// let t = PARSER.parse_time("02:05+00")?;
    /// assert_eq!(t, time(2, 5, 0, 0));
    /// let t = PARSER.parse_time("02:05-00")?;
    /// assert_eq!(t, time(2, 5, 0, 0));
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub fn parse_time<I: AsRef<[u8]>>(
        &self,
        input: I,
    ) -> Result<civil::Time, Error> {
        let input = input.as_ref();
        let parsed = self.p.parse_temporal_time(input)?;
        let parsed_time = parsed.into_full()?;
        let time = parsed_time.to_time();
        Ok(time)
    }
}

/// A printer for Temporal datetimes.
///
/// This printer converts an in memory representation of a datetime related
/// type to a machine (but also human) readable format. Using this printer, one
/// can convert [`Zoned`], [`Timestamp`], [`civil::DateTime`], [`civil::Date`]
/// or [`civil::Time`] values to a string. Note that all of those types provide
/// [`Diplay`](core::fmt::Display) implementations that utilize the default
/// configuration of this printer. However, this printer can be configured to
/// behave differently and can also print directly to anything that implements
/// the [`fmt::Write`](Write) trait.
///
/// See the [`fmt::temporal`](crate::fmt::temporal) module documentation for
/// more information on the specific format used. Note that the Temporal
/// datetime parser is strictly more flexible than what is supported by this
/// printer. For example, parsing `2024-06-15T07:00-04[America/New_York]` will
/// work just fine, even though the seconds are omitted. However, this printer
/// provides no way to write a datetime without the second component.
///
/// # Example
///
/// This example shows how to print a `Zoned` value with a space separating
/// the date and time instead of the more standard `T` separator.
///
/// ```
/// use jiff::{civil::date, fmt::temporal::DateTimePrinter};
///
/// // A printer can be created in a const context.
/// const PRINTER: DateTimePrinter = DateTimePrinter::new().separator(b' ');
///
/// let zdt = date(2024, 6, 15).at(7, 0, 0, 123456789).intz("America/New_York")?;
///
/// let mut buf = String::new();
/// // Printing to a `String` can never fail.
/// PRINTER.print_zoned(&zdt, &mut buf).unwrap();
/// assert_eq!(buf, "2024-06-15 07:00:00.123456789-04:00[America/New_York]");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Example: using adapters with `std::io::Write` and `std::fmt::Write`
///
/// By using the [`StdIoWrite`](super::StdIoWrite) and
/// [`StdFmtWrite`](super::StdFmtWrite) adapters, one can print datetimes
/// directly to implementations of `std::io::Write` and `std::fmt::Write`,
/// respectively. The example below demonstrates writing to anything
/// that implements `std::io::Write`. Similar code can be written for
/// `std::fmt::Write`.
///
/// ```no_run
/// use std::{fs::File, io::{BufWriter, Write}, path::Path};
///
/// use jiff::{civil::date, fmt::{StdIoWrite, temporal::DateTimePrinter}};
///
/// let zdt = date(2024, 6, 15).at(7, 0, 0, 0).intz("America/New_York")?;
///
/// let path = Path::new("/tmp/output");
/// let mut file = BufWriter::new(File::create(path)?);
/// DateTimePrinter::new().print_zoned(&zdt, StdIoWrite(&mut file)).unwrap();
/// file.flush()?;
/// assert_eq!(
///     std::fs::read_to_string(path)?,
///     "2024-06-15T07:00:00-04:00[America/New_York]",
/// );
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Debug)]
pub struct DateTimePrinter {
    p: printer::DateTimePrinter,
}

impl DateTimePrinter {
    /// Create a new Temporal datetime printer with the default configuration.
    pub const fn new() -> DateTimePrinter {
        DateTimePrinter { p: printer::DateTimePrinter::new() }
    }

    /// Use lowercase for the datetime separator and the `Z` (Zulu) UTC offset.
    ///
    /// This is disabled by default.
    ///
    /// # Example
    ///
    /// This example shows how to print a `Zoned` value with a lowercase
    /// datetime separator.
    ///
    /// ```
    /// use jiff::{civil::date, fmt::temporal::DateTimePrinter};
    ///
    /// const PRINTER: DateTimePrinter = DateTimePrinter::new().lowercase(true);
    ///
    /// let zdt = date(2024, 6, 15).at(7, 0, 0, 0).intz("America/New_York")?;
    ///
    /// let mut buf = String::new();
    /// // Printing to a `String` can never fail.
    /// PRINTER.print_zoned(&zdt, &mut buf).unwrap();
    /// assert_eq!(buf, "2024-06-15t07:00:00-04:00[America/New_York]");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub const fn lowercase(mut self, yes: bool) -> DateTimePrinter {
        self.p = self.p.lowercase(yes);
        self
    }

    /// Use the given ASCII character to separate the date and time when
    /// printing [`Zoned`], [`Timestamp`] or [`civil::DateTime`] values.
    ///
    /// This is set to `T` by default.
    ///
    /// # Example
    ///
    /// This example shows how to print a `Zoned` value with a different
    /// datetime separator.
    ///
    /// ```
    /// use jiff::{civil::date, fmt::temporal::DateTimePrinter};
    ///
    /// // We use a weird non-standard character here, but typically one would
    /// // use this method with an ASCII space.
    /// const PRINTER: DateTimePrinter = DateTimePrinter::new().separator(b'~');
    ///
    /// let zdt = date(2024, 6, 15).at(7, 0, 0, 0).intz("America/New_York")?;
    ///
    /// let mut buf = String::new();
    /// // Printing to a `String` can never fail.
    /// PRINTER.print_zoned(&zdt, &mut buf).unwrap();
    /// assert_eq!(buf, "2024-06-15~07:00:00-04:00[America/New_York]");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub const fn separator(mut self, ascii_char: u8) -> DateTimePrinter {
        self.p = self.p.separator(ascii_char);
        self
    }

    /// Print a `Zoned` datetime to the given writer.
    ///
    /// # Errors
    ///
    /// This only returns an error when writing to the given [`Write`]
    /// implementation would fail. Some such implementations, like for `String`
    /// and `Vec<u8>`, never fail (unless memory allocation fails). In such
    /// cases, it would be appropriate to call `unwrap()` on the result.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::{civil::date, fmt::temporal::DateTimePrinter};
    ///
    /// const PRINTER: DateTimePrinter = DateTimePrinter::new();
    ///
    /// let zdt = date(2024, 6, 15).at(7, 0, 0, 0).intz("America/New_York")?;
    ///
    /// let mut buf = String::new();
    /// // Printing to a `String` can never fail.
    /// PRINTER.print_zoned(&zdt, &mut buf).unwrap();
    /// assert_eq!(buf, "2024-06-15T07:00:00-04:00[America/New_York]");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub fn print_zoned<W: Write>(
        &self,
        zdt: &Zoned,
        wtr: W,
    ) -> Result<(), Error> {
        self.p.print_zoned(zdt, wtr)
    }

    /// Print a `Timestamp` datetime to the given writer.
    ///
    /// # Errors
    ///
    /// This only returns an error when writing to the given [`Write`]
    /// implementation would fail. Some such implementations, like for `String`
    /// and `Vec<u8>`, never fail (unless memory allocation fails). In such
    /// cases, it would be appropriate to call `unwrap()` on the result.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::{fmt::temporal::DateTimePrinter, Timestamp};
    ///
    /// let timestamp = Timestamp::new(0, 1)
    ///     .expect("one nanosecond after Unix epoch is always valid");
    ///
    /// let mut buf = String::new();
    /// // Printing to a `String` can never fail.
    /// DateTimePrinter::new().print_timestamp(&timestamp, &mut buf).unwrap();
    /// assert_eq!(buf, "1970-01-01T00:00:00.000000001Z");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub fn print_timestamp<W: Write>(
        &self,
        timestamp: &Timestamp,
        wtr: W,
    ) -> Result<(), Error> {
        self.p.print_timestamp(timestamp, wtr)
    }

    /// Print a `civil::DateTime` to the given writer.
    ///
    /// # Errors
    ///
    /// This only returns an error when writing to the given [`Write`]
    /// implementation would fail. Some such implementations, like for `String`
    /// and `Vec<u8>`, never fail (unless memory allocation fails). In such
    /// cases, it would be appropriate to call `unwrap()` on the result.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::{civil::date, fmt::temporal::DateTimePrinter};
    ///
    /// const PRINTER: DateTimePrinter = DateTimePrinter::new();
    ///
    /// let dt = date(2024, 6, 15).at(7, 0, 0, 0);
    ///
    /// let mut buf = String::new();
    /// // Printing to a `String` can never fail.
    /// PRINTER.print_datetime(&dt, &mut buf).unwrap();
    /// assert_eq!(buf, "2024-06-15T07:00:00");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub fn print_datetime<W: Write>(
        &self,
        dt: &civil::DateTime,
        wtr: W,
    ) -> Result<(), Error> {
        self.p.print_datetime(dt, wtr)
    }

    /// Print a `civil::Date` to the given writer.
    ///
    /// # Errors
    ///
    /// This only returns an error when writing to the given [`Write`]
    /// implementation would fail. Some such implementations, like for `String`
    /// and `Vec<u8>`, never fail (unless memory allocation fails). In such
    /// cases, it would be appropriate to call `unwrap()` on the result.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::{civil::date, fmt::temporal::DateTimePrinter};
    ///
    /// const PRINTER: DateTimePrinter = DateTimePrinter::new();
    ///
    /// let dt = date(2024, 6, 15);
    ///
    /// let mut buf = String::new();
    /// // Printing to a `String` can never fail.
    /// PRINTER.print_date(&dt, &mut buf).unwrap();
    /// assert_eq!(buf, "2024-06-15");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub fn print_date<W: Write>(
        &self,
        date: &civil::Date,
        wtr: W,
    ) -> Result<(), Error> {
        self.p.print_date(date, wtr)
    }

    /// Print a `civil::Time` to the given writer.
    ///
    /// # Errors
    ///
    /// This only returns an error when writing to the given [`Write`]
    /// implementation would fail. Some such implementations, like for `String`
    /// and `Vec<u8>`, never fail (unless memory allocation fails). In such
    /// cases, it would be appropriate to call `unwrap()` on the result.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::{civil::time, fmt::temporal::DateTimePrinter};
    ///
    /// const PRINTER: DateTimePrinter = DateTimePrinter::new();
    ///
    /// let dt = time(7, 0, 0, 0);
    ///
    /// let mut buf = String::new();
    /// // Printing to a `String` can never fail.
    /// PRINTER.print_time(&dt, &mut buf).unwrap();
    /// assert_eq!(buf, "07:00:00");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub fn print_time<W: Write>(
        &self,
        time: &civil::Time,
        wtr: W,
    ) -> Result<(), Error> {
        self.p.print_time(time, wtr)
    }
}

/// A parser for Temporal durations.
///
/// Note that in Jiff, a "Temporal duration" is called a "span."
///
/// See the [`fmt::temporal`](crate::fmt::temporal) module documentation for
/// more information on the specific format used.
///
/// # Example
///
/// This example shows how to parse a [`Span`] from a byte string. (That is,
/// `&[u8]` and not a `&str`.)
///
/// ```
/// use jiff::{fmt::temporal::SpanParser, ToSpan};
///
/// // A parser can be created in a const context.
/// static PARSER: SpanParser = SpanParser::new();
///
/// let span = PARSER.parse_span(b"P3y7m25dT7h36m")?;
/// assert_eq!(span, 3.years().months(7).days(25).hours(7).minutes(36));
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Debug)]
pub struct SpanParser {
    p: parser::SpanParser,
}

impl SpanParser {
    /// Create a new Temporal datetime printer with the default configuration.
    pub const fn new() -> SpanParser {
        SpanParser { p: parser::SpanParser::new() }
    }

    /// Parse a span string into a [`Span`] value.
    ///
    /// # Errors
    ///
    /// This returns an error if the span string given is invalid or if it
    /// is valid but doesn't fit in the span range supported by Jiff.
    ///
    /// # Example
    ///
    /// This shows a basic example of using this routine.
    ///
    /// ```
    /// use jiff::{fmt::temporal::SpanParser, ToSpan};
    ///
    /// static PARSER: SpanParser = SpanParser::new();
    ///
    /// let span = PARSER.parse_span(b"PT48m")?;
    /// assert_eq!(span, 48.minutes());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// Note that unless you need to parse a span from a byte string,
    /// at time of writing, there is no other advantage to using this
    /// parser directly. It is likely more convenient to just use the
    /// [`FromStr`](std::str::FromStr) trait implementation on [`Span`]:
    ///
    /// ```
    /// use jiff::{Span, ToSpan};
    ///
    /// let span = "PT48m".parse::<Span>()?;
    /// assert_eq!(span, 48.minutes());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub fn parse_span<I: AsRef<[u8]>>(&self, input: I) -> Result<Span, Error> {
        let input = input.as_ref();
        let parsed = self.p.parse_temporal_duration(input)?;
        let span = parsed.into_full()?;
        Ok(span)
    }
}

/// A printer for Temporal durations.
///
/// Note that in Jiff, a "Temporal duration" is called a "span."
///
/// This printer converts an in memory representation of a duration of time
/// to a machine (but also human) readable format. Using this printer,
/// one can convert a [`Span`] to a string. Note that a `Span` provides a
/// [`Display`](std::fmt::Display) trait implementation that utilize the
/// default configuration of this printer. However, this printer can print
/// directly to anything that implements the [`fmt::Write`](Write) trait.
///
/// See the [`fmt::temporal`](crate::fmt::temporal) module documentation for
/// more information on the specific format used.
///
/// # Example
///
/// This is a basic example showing how to print a [`Span`] directly to a
/// `Vec<u8>`.
///
/// ```
/// use jiff::{fmt::temporal::SpanPrinter, ToSpan};
///
/// // A printer can be created in a const context.
/// const PRINTER: SpanPrinter = SpanPrinter::new();
///
/// let span = 48.minutes();
/// let mut buf = vec![];
/// // Printing to a `Vec<u8>` can never fail.
/// PRINTER.print_span(&span, &mut buf).unwrap();
/// assert_eq!(buf, "PT48m".as_bytes());
/// ```
///
/// # Example: using adapters with `std::io::Write` and `std::fmt::Write`
///
/// By using the [`StdIoWrite`](super::StdIoWrite) and
/// [`StdFmtWrite`](super::StdFmtWrite) adapters, one can print spans
/// directly to implementations of `std::io::Write` and `std::fmt::Write`,
/// respectively. The example below demonstrates writing to anything
/// that implements `std::io::Write`. Similar code can be written for
/// `std::fmt::Write`.
///
/// ```no_run
/// use std::{fs::File, io::{BufWriter, Write}, path::Path};
///
/// use jiff::{fmt::{StdIoWrite, temporal::SpanPrinter}, ToSpan};
///
/// let span = 48.minutes();
///
/// let path = Path::new("/tmp/output");
/// let mut file = BufWriter::new(File::create(path)?);
/// SpanPrinter::new().print_span(&span, StdIoWrite(&mut file)).unwrap();
/// file.flush()?;
/// assert_eq!(std::fs::read_to_string(path)?, "PT48m");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Debug)]
pub struct SpanPrinter {
    p: printer::SpanPrinter,
}

impl SpanPrinter {
    /// Create a new Temporal span printer with the default configuration.
    pub const fn new() -> SpanPrinter {
        SpanPrinter { p: printer::SpanPrinter::new() }
    }

    /// Print a `Span` to the given writer.
    ///
    /// # Errors
    ///
    /// This only returns an error when writing to the given [`Write`]
    /// implementation would fail. Some such implementations, like for `String`
    /// and `Vec<u8>`, never fail (unless memory allocation fails). In such
    /// cases, it would be appropriate to call `unwrap()` on the result.
    ///
    /// # Example
    ///
    /// ```
    /// use jiff::{fmt::temporal::SpanPrinter, ToSpan};
    ///
    /// const PRINTER: SpanPrinter = SpanPrinter::new();
    ///
    /// let span = 3.years().months(5);
    ///
    /// let mut buf = String::new();
    /// // Printing to a `String` can never fail.
    /// PRINTER.print_span(&span, &mut buf).unwrap();
    /// assert_eq!(buf, "P3y5m");
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub fn print_span<W: Write>(
        &self,
        span: &Span,
        wtr: W,
    ) -> Result<(), Error> {
        self.p.print_span(span, wtr)
    }
}

#[cfg(test)]
mod tests {
    use alloc::string::ToString;

    use crate::Unit;

    use super::*;

    // This test ensures that strings like `2024-07-15+02` fail to parse.
    // Note though that `2024-07-15[America/New_York]` is okay!
    #[test]
    fn err_temporal_datetime_offset() {
        insta::assert_snapshot!(
            DateTimeParser::new().parse_date(b"2024-07-15+02").unwrap_err(),
            @r###"parsed value '2024-07-15', but unparsed input "+02" remains (expected no unparsed input)"###,
        );
        insta::assert_snapshot!(
            DateTimeParser::new().parse_date(b"2024-07-15-02").unwrap_err(),
            @r###"parsed value '2024-07-15', but unparsed input "-02" remains (expected no unparsed input)"###,
        );
    }

    #[test]
    fn year_zero() {
        insta::assert_snapshot!(
            DateTimeParser::new().parse_date("0000-01-01").unwrap(),
            @"0000-01-01",
        );
        insta::assert_snapshot!(
            DateTimeParser::new().parse_date("+000000-01-01").unwrap(),
            @"0000-01-01",
        );
        insta::assert_snapshot!(
            DateTimeParser::new().parse_date("-000000-01-01").unwrap_err(),
            @r###"failed to parse year in date "-000000-01-01": year zero must be written without a sign or a positive sign, but not a negative sign"###,
        );
    }

    // Regression test for: https://github.com/BurntSushi/jiff/issues/59
    #[test]
    fn fractional_duration_roundtrip() {
        let span1: Span = "Pt843517081,1H".parse().unwrap();
        let span2: Span = span1.to_string().parse().unwrap();
        assert_eq!(
            span1.total(Unit::Hour).unwrap(),
            span2.total(Unit::Hour).unwrap()
        );
    }
}
