0.1.6 (TBD)
===========
This release includes a new top-level type, `SignedDuration`, that provides a
near exact replica of `std::time::Duration`, but signed. It is meant to provide
alternative APIs for working with durations at a lower level than what `Span`
provides, and to facilitate better integration with the standard library.

This marks an initial integration phase with `SignedDuration`. It is planned
to integrate it more with the datetime types. Currently, there are integrations
on `Timestamp` and `Span`, but more will be added in the future.

This release also includes a few deprecations.

Deprecations:

* `Timestamp::as_duration`: to be replaced with `SignedDuration` in `jiff 0.2`.
* `Timestamp::from_duration`: to be replaced with `SignedDuration` in
`jiff 0.2`.
* `Timestamp::from_signed_duration`: to be replaced with `SignedDuration` in
`jiff 0.2`.
* `Span::to_duration`: to be replaced with `SignedDuration` in `jiff 0.2`.

Basically, all of the above APIs either accept or return a
`std::time::Duration`. To avoid breaking chnages at this point, new methods
for `SignedDuration` were added. For example, `Timestamp::as_jiff_duration`.
In `jiff 0.2`, the above deprecated methods will be removed and replaced with
equivalent methods that accept or return a `SignedDuration` instead. Callers
can then convert between a `SignedDuration` and a `std::time::Duration` using
appropriate `TryFrom` trait implementations.

Enhancements:

* [#XXX](https://github.com/BurntSushi/jiff/issues/XXX):
Add new top-level `SignedDuration` type.


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
