0.1.1 (2024-07-25)
==================
This is a new semver compatible release. The principle addition are APIs for
converting between a `jiff::Span` and a `std::time::Duration`. Specifically,
there are now `TryFrom<Span> for Duration` and `TryFrom<Duration> for Span`
trait implementations. There is also a `Span::to_duration`, which requires a
relative date, for converting spans with non-uniform units (like months) to a
`Duration`.

New features:

* [FEATURE #21](https://github.com/BurntSushi/jiff/issues/21),
  [FEATURE #40](https://github.com/BurntSushi/jiff/issues/40):
Adds APIs for converting between `Span` and `std::time::Duration`.

Bug fixes:

* [BUG #36](https://github.com/BurntSushi/jiff/issues/36):
Saturating arithmetic for `Timestamp` panics with day-or-greater units.
* [BUG #38](https://github.com/BurntSushi/jiff/issues/38):
Fix some bugs in the micro-benchmarks.
* [BUG #39](https://github.com/BurntSushi/jiff/issues/39):
Document that the RFC 2822 parser is not technically fully spec compliant.


0.1.0 (2024-07-21)
==================
The initial release of Jiff.
