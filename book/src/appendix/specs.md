# RFCs and Other Specifications

As a datetime library, Jiff implements or conforms to a number of
specifications, most of which are defined and maintained by others. This
allows Jiff to inter-operate with other systems seamlessly, and to make use of
existing standards and conventions.

This appendix contextualizes each of the specifications that Jiff supports
in terms of its behavior and API. This provides a "one stop shop" for finding
precisely how Jiff interoperates with other systems.

## RFC 3339

[RFC 3339] specifies a simple interchange format for human readable timestamps.
It is widely used on the Internet and as a means for transmitting precise
instants in time across systems. It also permits specifying an offset from
UTC, albeit not a time zone, as a way to _hint_ at the local time of the event
being timed.

RFC 3339 is, very loosely speaking, a subset of an older standard called
[ISO 8601]. (It is _not_ a strict subset, as noted in the table below.)

This table shows some examples:

| Timestamp | Description | ISO 8601? |
| --------- | ----------- | --------- |
| `2025-03-07T15:27:00-05:00` | Local time at UTC offset `-05` | Yes |
| `2025-03-07T20:27:00+00:00` | Local time at UTC | Yes |
| `2025-03-07T20:27:00-00:00` | Precise time, offset from UTC unknown | No |
| `2025-03-07T20:27:00Z` | Local time at UTC (changed in [RFC 9557]) | Yes |
| `2025-03-07 20:27:00Z` | Space separated | No |
| `2025-03-07T20:27:00.123Z` | Fractional seconds | Yes |

In Jiff, the primary way to get an RFC 3339 timestamp is with Jiff's
[`Timestamp`](jiff::Timestamp) type:

```rust
use jiff::Timestamp;

// Parse an RFC 3339 timestamp
let ts: Timestamp = "2025-03-07 15:27:00-05:00".parse()?;
// Print an RFC 3339 timestamp
assert_eq!(ts.to_string(), "2025-03-07T20:27:00Z");
# Ok::<(), Box<dyn std::error::Error>>(())
```

(Jiff inserts a `T` by default for purposes of compatibility, but one can tweak
this via [`jiff::fmt::temporal::DateTimePrinter::separator`].)

A `Timestamp` in Jiff very specifically does not have an offset, so
it will always format in Zulu time using `Z`. This is functionally
equivalent to an offset of `+00:00`, but it indicates that the
offset from UTC to local time is unknown. In order to print an
RFC 3339 timestamp with a particular offset, you can use the
[`Timestamp::display_with_offset`](jiff::Timestamp::display_with_offset)
API:

```rust
use jiff::{tz, Timestamp};

// Parse an RFC 3339 timestamp
let ts: Timestamp = "2025-03-07 15:27:00-05:00".parse()?;
// Print an RFC 3339 timestamp with a specific offset
assert_eq!(
    ts.display_with_offset(tz::offset(-4)).to_string(),
    "2025-03-07T16:27:00-04:00",
);
// Using an offset of `0` formats as `+00:00` instead of `Z`
assert_eq!(
    ts.display_with_offset(tz::offset(0)).to_string(),
    "2025-03-07T20:27:00+00:00",
);
# Ok::<(), Box<dyn std::error::Error>>(())
```

Moreover, Jiff's parsing is quite a bit more flexible than what is prescribed
by RFC 3339. Notably, Jiff supports parts of [ISO 8601] as well. Here are some
more examples:

```rust
use jiff::Timestamp;

let examples = [
    "1970-01-01 00:00:00Z",
    "1970-01-01t00:00:00z",
    "1970-01-01T00:00Z",
    "1970-01-01T00Z",
    "1970-01-01T00+00",
];
for example in examples {
    let ts: Timestamp = example.parse()?;
    assert_eq!(ts, Timestamp::UNIX_EPOCH);
}
# Ok::<(), Box<dyn std::error::Error>>(())
```

Finally, this parsing is automatically available via [Serde]'s `Serialize`
and `Deserialize` trait implementations. You just need to enable Jiff's
`serde` crate feature:

```rust
use jiff::Timestamp;

#[derive(Debug, Eq, PartialEq, serde::Serialize, serde::Deserialize)]
struct Data {
    timestamp: Timestamp,
}

let data = Data {
    timestamp: Timestamp::from_second(1_123_456_789)?,
};
let serialized = serde_json::to_string_pretty(&data)?;
assert_eq!(serialized, r#"{
  "timestamp": "2005-08-07T23:19:49Z"
}"#);
let got: Data = serde_json::from_str(&serialized)?;
assert_eq!(got, data);

# Ok::<(), Box<dyn std::error::Error>>(())
```

## RFC 9557

[RFC 9557] extends [RFC 3339] to tag timestamps with additional information,
such as time zones. RFC 9557 is backwards compatible with RFC 3339 in that the
extensions are completely optional.

One thing worth mentioning is that RFC 9557 changes the semantic meaning of
Zulu time, i.e., the `Z` offset, to mean the same as `-00:00` does in RFC 3339.
That is, `Z` is to be used when the timestamp itself is known, but the offset
from UTC to get local time is _not_ known. While this is effectively the same
as `+00:00` in terms of offset math, the `+00:00` offset is used when the
preferred offset for local time is `+00:00`. For example, during winter
in London.

BREADCRUMBS: Talk about time zone annotations...

## ISO 8601

## Temporal ISO 8601 grammar

## The "friendly" duration format

The [friendly duration grammar] blah blah.

## RFC 2822 & RFC 9110

## `strptime` & `strftime`

## RFC 9636

[RFC 9636] specifies the Time Zone Information Format (TZif) for representing
and exchanging time zone information. It replaced [RFC 8536] in 2024, which
specified an older version of the TZif format.

The TZif format is used to represent the rules that describe transitions in
time zones. A "transition" refers to a change in how civil time is displayed
on clocks in a particular geographic region. Typically, this corresponds to
a change in the offset from UTC used to compute civil time. For example, as
of 2025, New York enters [daylight saving time] at 2am local time on the second
Sunday of March (switches to UTC offset `-04`), and leaves daylight saving time
at 2am local time on the first Sunday of November (switches back to UTC offset
`-05`). We can observe this with Jiff:

```rust
use jiff::{tz::{self, TimeZone}, Timestamp};

let tz = TimeZone::get("America/New_York")?;

let start: Timestamp = "2025-01-01T00:00Z".parse()?;
// Gives an iterator for all time zone transitions following `start`.
let mut following = tz.following(start);

// The first transition is in the Spring,
// and corresponds to when New York enters DST.
let Some(enter_dst) = following.next() else {
    return Err("missing following transition".into());
};
assert_eq!(enter_dst.offset(), tz::offset(-4));
assert_eq!(enter_dst.abbreviation(), "EDT");
// The time in UTC at which the transition occurs.
assert_eq!(
    enter_dst.timestamp().to_string(),
    "2025-03-09T07:00:00Z",
);
// We skip an hour, so the 2 o'clock hour never appears
// on clocks this day in New York.
//
// The local time here says 3am despite the fact that
// I said 2am above. The actual TZ transition rule is
// defined to be 2am, or what *would* be 2am in standard
// time. Standard time in New York is `-05:00` from UTC,
// which means `2025-03-09T07:00Z`. That same instant at
// `-04:00` from UTC is `2025-03-09T03:00-04:00`. And
// that's how the 3am local time is derived.
assert_eq!(
    enter_dst.timestamp().to_zoned(tz.clone()).to_string(),
    "2025-03-09T03:00:00-04:00[America/New_York]",
);

// The second transition is in the Fall,
// and corresponds to when New York leaves DST
// and reverts to "standard" time. That is, 5
// hours behind GMT.
let Some(leave_dst) = following.next() else {
    return Err("missing second following transition".into());
};
assert_eq!(leave_dst.offset(), tz::offset(-5));
assert_eq!(leave_dst.abbreviation(), "EST");
// The time in UTC at which the transition occurs.
assert_eq!(
    leave_dst.timestamp().to_string(),
    "2025-11-02T06:00:00Z",
);
// We repeat an hour, so the 1 o'clock hour appears
// twice on clocks this day in New York.
//
// As with entering DST, leaving DST is also defined
// to be at 2am, even though the actual local time
// rendered is 1am. Since we're leaving DST, the TZ
// rule is 2am in DST time, which is `-04:00` from
// UTC. That is, `2025-11-02T06:00Z`. That same instant
// at `-05:00` from UTC is `2025-11-02T01:00-05:00`.
// And that's how the 1am local time is derived.
assert_eq!(
    leave_dst.timestamp().to_zoned(tz.clone()).to_string(),
    "2025-11-02T01:00:00-05:00[America/New_York]",
);
# Ok::<(), Box<dyn std::error::Error>>(())
```

It is _very_ uncommon to need to look at the explicit time zone transitions
as is done in the code above. However, it may be useful to see it written out
at its lowest layer. Behind the scenes, the `TimeZone::get("...")` call in
the code above is looking for and parsing TZif data on your system.

TZif data is commonly found on Unix systems in `/usr/share/zoneinfo`. Each
time zone gets its own file, and they are organized, roughly, according to
geographic region. For example, the time zone for Sydney, Australia can be
found at `/usr/share/zoneinfo/Australia/Sydney` on my Linux system. On non-Unix
systems, there is no canonical location for where TZif data is stored.

The collection of TZif data in `/usr/share/zoneinfo` is known as the
[IANA Time Zone Database]. The maintainers of this database keep it updated
based on real world events. For example, when new laws are passed that change
a region's offset or daylight saving time rules, those rules get updated in
the database. This database is then propagated out to systems everywhere. This
database is usually updated a couple times every year, but some years contain
more updates.

The recommended practice is to read this database at runtime at
`/usr/share/zoneinfo`. Applications doing this will automatically benefit from
updates to the database without needing to be re-compiled. However, it is
also very common to embed the IANA Time Zone Database into compiled binaries,
especially for systems that have no canonical storage for TZif data (like
Windows).

In the default configuration, Jiff will read from `/usr/share/zoneinfo` on
Unix systems. When Jiff is compiled for Windows targets, it will automatically
embed the full IANA Time Zone Database into the binary.

Some more specifics:

* Jiff automatically supports all 4 versions of TZif data, as described in
[RFC 9636].
* Jiff's [platform documentation](jiff::_documentation::platform) goes into
more detail about how the IANA Time Zone Database is discovered on your
specific system.
* Jiff's [crate features](jiff#time-zone-features) provide a number of
different compile-time options for tweaking how Jiff interacts with the IANA
Time Zone Database.

## POSIX `TZ` environment variable

## `/etc/localtime`

[daylight saving time]: https://en.wikipedia.org/wiki/Daylight_saving_time
[IANA Time Zone Database]: https://www.iana.org/time-zones
[Serde]: https://serde.rs
[ISO 8601]: https://www.iso.org/iso-8601-date-and-time-format.html
[RFC 2822]: https://datatracker.ietf.org/doc/html/rfc2822
[RFC 3339]: https://datatracker.ietf.org/doc/html/rfc3339
[RFC 8536]: https://datatracker.ietf.org/doc/html/rfc8536
[RFC 9110]: https://www.rfc-editor.org/rfc/rfc9110.html
[RFC 9557]: https://datatracker.ietf.org/doc/rfc9557/
[RFC 9636]: https://datatracker.ietf.org/doc/rfc9636/
[Temporal ISO 8601 grammar]: https://tc39.es/proposal-temporal/#sec-temporal-iso8601grammar
[strftime]: https://pubs.opengroup.org/onlinepubs/009696799/functions/strftime.html
[strptime]: https://pubs.opengroup.org/onlinepubs/007904875/functions/strptime.html
[friendly duration grammar]: jiff::fmt::friendly#grammar
[POSIX `TZ` environment variable]: https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap08.html
