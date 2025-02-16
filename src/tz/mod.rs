/*!
Routines for interacting with time zones and the zoneinfo database.

The main type in this module is [`TimeZone`]. For most use cases, you may not
even need to interact with this type at all. For example, this code snippet
converts a civil datetime to a zone aware datetime:

```
use jiff::civil::date;

let zdt = date(2024, 7, 10).at(20, 48, 0, 0).in_tz("America/New_York")?;
assert_eq!(zdt.to_string(), "2024-07-10T20:48:00-04:00[America/New_York]");

# Ok::<(), Box<dyn std::error::Error>>(())
```

And this example parses a zone aware datetime from a string:

```
use jiff::Zoned;

let zdt: Zoned = "2024-07-10 20:48[america/new_york]".parse()?;
assert_eq!(zdt.year(), 2024);
assert_eq!(zdt.month(), 7);
assert_eq!(zdt.day(), 10);
assert_eq!(zdt.hour(), 20);
assert_eq!(zdt.minute(), 48);
assert_eq!(zdt.offset().seconds(), -4 * 60 * 60);
assert_eq!(zdt.time_zone().iana_name(), Some("America/New_York"));

# Ok::<(), Box<dyn std::error::Error>>(())
```

Yet, neither of the above examples require uttering [`TimeZone`]. This is
because the datetime types in this crate provide higher level abstractions for
working with time zone identifiers. Nevertheless, sometimes it is useful to
work with a `TimeZone` directly. For example, if one has a `TimeZone`, then
conversion from a [`Timestamp`](crate::Timestamp) to a [`Zoned`](crate::Zoned)
is infallible:

```
use jiff::{tz::TimeZone, Timestamp, Zoned};

let tz = TimeZone::get("America/New_York")?;
let ts = Timestamp::UNIX_EPOCH;
let zdt = ts.to_zoned(tz);
assert_eq!(zdt.to_string(), "1969-12-31T19:00:00-05:00[America/New_York]");

# Ok::<(), Box<dyn std::error::Error>>(())
```

# The [IANA Time Zone Database]

Since a time zone is a set of rules for determining the civil time, via an
offset from UTC, in a particular geographic region, a database is required to
represent the full complexity of these rules in practice. The standard database
is widespread use is the [IANA Time Zone Database]. On Unix systems, this is
typically found at `/usr/share/zoneinfo`, and Jiff will read it automatically.
On Windows systems, there is no canonical Time Zone Database installation, and
so Jiff embeds it into the compiled artifact. (This does not happen on Unix
by default.)

See the [`TimeZoneDatabase`] for more information.

# The system or "local" time zone

In many cases, the operating system manages a "default" time zone. It might,
for example, be how the `date` program converts a Unix timestamp to a time that
is "local" to you.

Unfortunately, there is no universal approach to discovering a system's default
time zone. Instead, Jiff uses heuristics like reading `/etc/localtime` on Unix,
and calling [`GetDynamicTimeZoneInformation`] on Windows. But in all cases,
Jiff will always use the IANA Time Zone Database for implementing time zone
transition rules. (For example, Windows specific APIs for time zone transitions
are not supported by Jiff.)

Moreover, Jiff supports reading the `TZ` environment variable, as specified
by POSIX, on all systems.

TO get the system's default time zone, use [`TimeZone::system`].

[IANA Time Zone Database]: https://en.wikipedia.org/wiki/Tz_database
[`GetDynamicTimeZoneInformation`]: https://learn.microsoft.com/en-us/windows/win32/api/timezoneapi/nf-timezoneapi-getdynamictimezoneinformation
*/

pub use self::{
    ambiguous::{
        AmbiguousOffset, AmbiguousTimestamp, AmbiguousZoned, Disambiguation,
    },
    db::{db, TimeZoneDatabase, TimeZoneName, TimeZoneNameIter},
    offset::{Dst, Offset, OffsetArithmetic, OffsetConflict, OffsetRound},
    timezone::{
        TimeZone, TimeZoneFollowingTransitions, TimeZoneOffsetInfo,
        TimeZonePrecedingTransitions, TimeZoneTransition,
    },
};

mod ambiguous;
#[cfg(feature = "tzdb-concatenated")]
mod concatenated;
mod db;
mod offset;
#[cfg(feature = "alloc")]
pub(crate) mod posix;
#[cfg(feature = "tz-system")]
mod system;
#[cfg(all(test, feature = "alloc"))]
mod testdata;
mod timezone;
#[cfg(feature = "alloc")]
mod tzif;
// See module comment for WIP status. :-(
#[cfg(test)]
mod zic;

/// Creates a new time zone offset in a `const` context from a given number
/// of hours.
///
/// Negative offsets correspond to time zones west of the prime meridian,
/// while positive offsets correspond to time zones east of the prime
/// meridian. Equivalently, in all cases, `civil-time - offset = UTC`.
///
/// The fallible non-const version of this constructor is
/// [`Offset::from_hours`].
///
/// This is a convenience free function for [`Offset::constant`]. It is
/// intended to provide a terse syntax for constructing `Offset` values from
/// a value that is known to be valid.
///
/// # Panics
///
/// This routine panics when the given number of hours is out of range.
/// Namely, `hours` must be in the range `-25..=25`.
///
/// Similarly, when used in a const context, an out of bounds hour will prevent
/// your Rust program from compiling.
///
/// # Example
///
/// ```
/// use jiff::tz::offset;
///
/// let o = offset(-5);
/// assert_eq!(o.seconds(), -18_000);
/// let o = offset(5);
/// assert_eq!(o.seconds(), 18_000);
/// ```
#[inline]
pub const fn offset(hours: i8) -> Offset {
    Offset::constant(hours)
}
