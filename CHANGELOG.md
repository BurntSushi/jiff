# CHANGELOG

0.1.14 (TBD)
============
This release introduces new APIs to the RFC 2822 printer that explicitly
print timestamps in a format strictly compatible with [RFC 9110].

Enhancements:

* [#151](https://github.com/BurntSushi/jiff/issues/151):
Add `rfc2822::DateTimePrinter::timestamp_to_rfc9110_string` method.


0.1.13 (2024-09-07)
===================
This release introduces a new `jiff::tz::TimeZone::try_system` API. It is like
`TimeZone::system`, but returns an error instead of an automatic fall back to
UTC when the system time zone could not be discovered.

This also includes an update to the bundled [IANA Time Zone Database] to the
`2024b` release in the `jiff-tzdb` crate. As a reminder, the bundled database
is not used or included on Unix platforms by default. See [PLATFORM] for more
details.

Enhancements:

* [#65](https://github.com/BurntSushi/jiff/issues/65):
Add `TimeZone::try_system` for fallibly determining the system's time zone.
* [#125](https://github.com/BurntSushi/jiff/pull/125):
Update to the `2024b` release of the [IANA Time Zone Database].


0.1.12 (2024-08-31)
===================
This release introduces some new minor APIs that support formatting
`Timestamp` values as RFC 3339 strings with a specific offset.

Previously, using the standard formatting routines that Jiff provides, it was
only possible to format a `Timestamp` using Zulu time. For example:

```rust
use jiff::Timestamp;

assert_eq!(
    Timestamp::UNIX_EPOCH.to_string(),
    "1970-01-01T00:00:00Z",
);
```

This is fine most use cases, but it can be useful on occasion to format
a `Timestamp` with a specific offset. While this isn't as expressive
as formatting a datetime with a time zone (e.g., with an IANA time
zone identifier), it may be useful in contexts where you just want to
"hint" at what a user's local time is. To that end, there is a new
`Timestamp::display_with_offset` method that makes this possible:

```rust
use jiff::{tz, Timestamp};

assert_eq!(
    Timestamp::UNIX_EPOCH.display_with_offset(tz::offset(-5)).to_string(),
    "1969-12-31T19:00:00-05:00",
);
```

A corresponding API was added to `jiff::fmt::temporal::DateTimePrinter` for
lower level use.

Moreover, this release also includes new convenience APIs on the Temporal and
RFC 2822 printer types for returning strings. For example, previously, if you
were using the RFC 2822 printer to format a `Timestamp`, you had to do this:

```rust
use jiff::{fmt::rfc2822::DateTimePrinter, Timestamp};

let mut buf = String::new();
DateTimePrinter::new().print_timestamp(&Timestamp::UNIX_EPOCH, &mut buf).unwrap();
assert_eq!(buf, "Thu, 1 Jan 1970 00:00:00 -0000");
```

But now you can just do this:

```rust
use jiff::{fmt::rfc2822::DateTimePrinter, Timestamp};

assert_eq!(
    DateTimePrinter::new().timestamp_to_string(&Timestamp::UNIX_EPOCH).unwrap(),
    "Thu, 1 Jan 1970 00:00:00 -0000",
);
```

Enhancements:

* [#122](https://github.com/BurntSushi/jiff/pull/122):
Support formatting `Timestamp` to an RFC 3339 string with a specific offset.


0.1.11 (2024-08-28)
===================
This release includes a few small enhancements that have been requested over
the last several weeks. The biggest enhancement is a new `jiff::fmt::serde`
sub-module. It provides convenience routines similar to Chrono's
`chrono::serde` sub-module for serializing and deserializing between a
`jiff::Timestamp` and an integer number of seconds, milliseconds, microseconds
or nanoseconds. For example:

```rust
use jiff::Timestamp;

#[derive(serde::Serialize, serde::Deserialize)]
struct Record {
    #[serde(with = "jiff::fmt::serde::timestamp::second::required")]
    timestamp: Timestamp,
}

let json = r#"{"timestamp":1517644800}"#;
let got: Record = serde_json::from_str(&json).unwrap();
assert_eq!(got.timestamp, Timestamp::from_second(1517644800).unwrap());
assert_eq!(serde_json::to_string(&got).unwrap(), json);
```

If you need to support optional timestamps via `Option<Timestamp>`, then use
`jiff::fmt::serde::timestamp::second::optional` instead. Similarly, if you
need to support milliseconds instead of seconds, then replace `second` with
`millisecond` in the module path.

Enhancements:

* [#78](https://github.com/BurntSushi/jiff/issues/78):
Add `BrokenDownTime::set_{offset,iana_time_zone}` APIs.
* [#93](https://github.com/BurntSushi/jiff/issues/93):
Add note about using `Timestamp::now().to_zoned()` instead of
`Zoned::now().with_time_zone()`.
* [#101](https://github.com/BurntSushi/jiff/issues/101):
Add new `jiff::fmt::serde` module for integration with integer timestamps.
* [#117](https://github.com/BurntSushi/jiff/pull/117):
Remove `unsafe` usage in `libm` functions (applicable only to no-std users).


0.1.10 (2024-08-23)
===================
This release features a small bug fix where Jiff will detect an IANA time
zone identifier in some cases where it wouldn't before. While Jiff would
previously read the symlink metadata on `/etc/localtime` by default to discover
the system configured time zone on Unix systems, it *wouldn't* do so when
`TZ=/etc/localtime`. There's really no reason not to, so this release of Jiff
is fixed to use symlink sniffing on file paths provided by thw `TZ` environment
variable.

Bug fixes:

* [#113](https://github.com/BurntSushi/jiff/issues/113):
When `TZ=/etc/localtime`, use symlink metadata to detect IANA identifier.


0.1.9 (2024-08-23)
==================
This release introduces new options for controlling the precision
of fractional seconds when printing `Zoned`, `Timestamp`,
`civil::DateTime` or `civil::Time` values. This is principally exposed
via `jiff::fmt::temporal::DateTimePrinter::precision`, but it's also
available via the standard library's formatting machinery. For example,
if `zdt` is a `jiff::Zoned`, then `format!("{zdt:.6}")` will format
it into a string with microsecond precision, even if its fractional
component is zero.

Enhancements:

* [#92](https://github.com/BurntSushi/jiff/issues/92):
Support setting the precision of fractional seconds when printing datetimes.


0.1.8 (2024-08-19)
==================
This releases fixes a build error in Jiff's `alloc`-only configuration. This
regression was introduced in `jiff 0.1.6`.

Bug fixes:

* [#108](https://github.com/BurntSushi/jiff/issues/108):
Use `core::time::Duration` everywhere instead of `std::time::Duration`.


0.1.7 (2024-08-18)
==================
This release relaxes Jiff's dependency on `windows-sys` to include multiple
semver incompatible releases. The purpose of this relaxation is to enable
Jiff to work with different versions of `windows-sys` in the hopes that this
reduces the likelihood that multiple copies of `windows-sys` are included in
your dependency tree.

Dependencies:

* [#106](https://github.com/BurntSushi/jiff/pull/106):
Relax `windows-sys` dependency constraint to `>=0.52.0, <=0.59.*`.


0.1.6 (2024-08-18)
==================
This release includes a new top-level type, `SignedDuration`, that provides a
near exact replica of `std::time::Duration`, but signed. It is meant to provide
alternative APIs for working with durations at a lower level than what `Span`
provides, and to facilitate better integration with the standard library.

A `SignedDuration` has also been integrated with all of Jiff's datetime types.
For example, previously, `Zoned::checked_add` only accepted a concrete
`jiff::Span`. But now it accepts a `jiff::Span`, `jiff::SignedDuration` or even
a `std::time::Duration`. Moreover, all of the `until` and `since` APIs on
datetime types have been ported and copied to return `SignedDuration` under the
`duration_until` and `duration_since` names.

This marks an initial integration phase with `SignedDuration`. It is planned
to integrate it more with the datetime types. Currently, there are integrations
on `Timestamp` and `Span`, but more will be added in the future.

Overall, folks should still use `Span`. That is the intended default duration
type in Jiff and will continue to be. Users of Jiff may find `SignedDuration`
useful in contexts where speed is important or when one needs to integrate
with the standard library.

This release also includes a few related deprecations as the APIs involving
`std::time::Duration` are phased out in favor of `SignedDuration`.

Deprecations:

* `Timestamp::as_duration`: replaced with `as_jiff_duration`, which will be
renamed to `as_duration` in `jiff 0.2`.
* `Timestamp::from_duration`: replaced with `from_jiff_duration`, which will be
renamed to `from_duration` in `jiff 0.2`.
* `Timestamp::from_signed_duration`: replaced with `from_jiff_duration`.
* `Span::to_duration`: replaced with `to_jiff_duration`, which will be renamed
to `to_duration` in `jiff 0.2`.

Basically, all of the above APIs either accept or return a
`std::time::Duration`. To avoid breaking chnages at this point, new methods
for `SignedDuration` were added. For example, `Timestamp::as_jiff_duration`.
In `jiff 0.2`, the above deprecated methods will be removed and replaced with
equivalent methods that accept or return a `SignedDuration` instead. Callers
can then convert between a `SignedDuration` and a `std::time::Duration` using
appropriate `TryFrom` trait implementations.

Enhancements:

* [#21](https://github.com/BurntSushi/jiff/issues/21):
Add new top-level `SignedDuration` type.
* [#90](https://github.com/BurntSushi/jiff/issues/90):
Improve error message when using `Span` with >=day units with a `Timestamp`.

Performance:

* [#104](https://github.com/BurntSushi/jiff/pull/104)
Optimize offset calculations in time zones without DST.
* [#105](https://github.com/BurntSushi/jiff/pull/105)
Optimize offset calculations for timestamps after last DST rule change.


0.1.5 (2024-08-09)
==================
This release includes some improvements and bug fixes, particularly for Jiff's
`strtime` APIs.

Enhancements:

* [#63](https://github.com/BurntSushi/jiff/issues/63):
Add link to original Chrono maintainer's commentary in `DESIGN.md`.
* [#75](https://github.com/BurntSushi/jiff/issues/75):
Add support for `%V` for formatting _and_ parsing IANA time zone identifiers.
* [#79](https://github.com/BurntSushi/jiff/pull/79):
Add `devcontainer.json` to support GitHub Codespaces.
* [#85](https://github.com/BurntSushi/jiff/pull/85):
Set correct ranges for internal tracking in return value of `days_in_month`.

Bug fixes:

* [#59](https://github.com/BurntSushi/jiff/issues/59):
Fixes a bug where some `Span`s could not be roundtripped through ISO 8601.
* [#71](https://github.com/BurntSushi/jiff/issues/71):
Tweak wording in documentation of "printf"-style API.
* [#73](https://github.com/BurntSushi/jiff/issues/73):
Make it so `%.Nf` only formats to `N` decimal places.
* [#77](https://github.com/BurntSushi/jiff/pull/77):
Disable optimizations when running tests.


0.1.4 (2024-08-01)
==================
This release includes a small improvement for `strptime` that permits
`%Y%m%d` to parse `20240730` correctly.

Enhancements:

* [#62](https://github.com/BurntSushi/jiff/issues/62):
Tweak `strptime` so that things like `%Y` aren't unceremoniously greedy.


0.1.3 (2024-07-30)
==================
This release features support for `wasm32-unknown-unknown`. That is, when
Jiff's new `js` crate feature is enabled, Jiff will automatically use
JavaScript APIs to determine the current time and time zone.

Enhancements:

* [#58](https://github.com/BurntSushi/jiff/pull/58):
Add WASM support and a new `PLATFORM.md` guide.


0.1.2 (2024-07-28)
==================
This release features a few new APIs that a need for arose while experimenting
with actually using Jiff in real projects. Namely, the `jiff::fmt::strtime`
module now has `%f` and `%.f` directives for parsing and formatting fractional
seconds. And both `jiff::fmt::rfc2822` and `jiff::fmt::strtime` now have
support for skipping weekday checks during parsing. (Previously, Jiff required
that an English weekday be consistent with the date parsed, and there was no
way to opt out. While this is still the default behavior, callers can disable
this check.)

Enhancements:

* [#52](https://github.com/BurntSushi/jiff/pull/52):
Improve documentation for `Span` getter methods.
* [#53](https://github.com/BurntSushi/jiff/pull/53):
Add support for skipping weekday checking when parsing datetimes.
* [#55](https://github.com/BurntSushi/jiff/pull/55):
Add support for fractional seconds in `jiff::fmt::strtime`.

Bug fixes:

* [#49](https://github.com/BurntSushi/jiff/pull/49):
Fix informational regex describing ISO 8601 format.
* [#51](https://github.com/BurntSushi/jiff/pull/51):
Explicitly allow new deny-by-default lint `ambiguous_negative_literals`.


0.1.1 (2024-07-25)
==================
This is a new semver compatible release. The principle addition are APIs for
converting between a `jiff::Span` and a `std::time::Duration`. Specifically,
there are now `TryFrom<Span> for Duration` and `TryFrom<Duration> for Span`
trait implementations. There is also a `Span::to_duration`, which requires a
relative date, for converting spans with non-uniform units (like months) to a
`Duration`.

Enhancements:

* [#21](https://github.com/BurntSushi/jiff/issues/21),
  [#40](https://github.com/BurntSushi/jiff/issues/40):
Adds APIs for converting between `Span` and `std::time::Duration`.

Bug fixes:

* [#36](https://github.com/BurntSushi/jiff/issues/36):
Saturating arithmetic for `Timestamp` panics with day-or-greater units.
* [#38](https://github.com/BurntSushi/jiff/issues/38):
Fix some bugs in the micro-benchmarks.
* [#39](https://github.com/BurntSushi/jiff/issues/39):
Document that the RFC 2822 parser is not technically fully spec compliant.


0.1.0 (2024-07-21)
==================
The initial release of Jiff.

[IANA Time Zone Database]: https://www.iana.org/time-zones
[PLATFORM]: PLATFORM.md
[RFC 9110]: https://datatracker.ietf.org/doc/html/rfc9110#section-5.6.7-15
