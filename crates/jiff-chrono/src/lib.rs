/*!
This crate provides conversion routines between [`jiff`] and
[`chrono`](https://docs.rs/chrono).

The conversion routines are implemented via the conversion traits defined
in this crate. These traits mirror [`From`], [`Into`], [`TryFrom`] and
[`TryInto`] from the standard library. They exist here (rather than being
`From`/`TryFrom` impls) because Rust's orphan rule forbids `From` impls
between types that both live in foreign crates.

[`jiff`]: https://docs.rs/jiff/0.2

# Available conversions

Infallible (use [`ConvertFrom`] / [`ConvertInto`]):

* [`jiff::civil::Date`] → [`chrono::NaiveDate`]
* [`jiff::civil::Time`] → [`chrono::NaiveTime`]
* [`jiff::civil::DateTime`] → [`chrono::NaiveDateTime`]
* [`jiff::civil::Weekday`] ↔ [`chrono::Weekday`]
* [`jiff::Timestamp`] → [`chrono::DateTime<Utc>`](chrono::DateTime)
* [`chrono::FixedOffset`] → [`jiff::tz::Offset`]
* [`chrono::TimeDelta`] → [`jiff::SignedDuration`]
* [`chrono::TimeDelta`] → [`jiff::Span`]

Infallible (use [`ConvertFrom`] / [`ConvertInto`]):

* [`chrono::Months`] → [`jiff::Span`]

Fallible (use [`ConvertTryFrom`] / [`ConvertTryInto`]):

* [`chrono::NaiveDate`] → [`jiff::civil::Date`]
  (fails when outside Jiff's year range of `-9999..=9999`)
* [`chrono::NaiveTime`] → [`jiff::civil::Time`]
  (fails on leap-second values)
* [`chrono::NaiveDateTime`] → [`jiff::civil::DateTime`]
* [`chrono::DateTime<Tz>`](chrono::DateTime) → [`jiff::Timestamp`]
  (generic over any chrono time zone; fails on leap-second values)
* [`chrono::DateTime<Utc>`](chrono::DateTime) → [`jiff::Zoned`]
* [`chrono::DateTime<FixedOffset>`](chrono::DateTime) ↔ [`jiff::Zoned`]
* [`jiff::tz::Offset`] → [`chrono::FixedOffset`]
  (fails outside chrono's `±23:59:59` range)
* [`jiff::SignedDuration`] → [`chrono::TimeDelta`]
  (fails outside chrono's ~`±2.9 × 10^11` second range)
* [`jiff::Span`] → [`chrono::TimeDelta`]
  (fails if the span contains calendar units or overflows)

With the `chrono-tz` feature enabled:

* [`jiff::Zoned`] ↔ `chrono::DateTime<chrono_tz::Tz>`
* [`jiff::tz::TimeZone`] ↔ `chrono_tz::Tz`

# Semantics caveats

A value can be convertible without being *equivalent*. This section
summarizes what is silently dropped by each non-trivial conversion and
where the two libraries disagree on meaning. Read it before migrating
production code.

## Time-zone identity is lost when converting to `FixedOffset`

A [`jiff::Zoned`] carries an IANA time zone (e.g. `America/New_York`) and
the DST rule set that goes with it. A [`chrono::DateTime<FixedOffset>`](chrono::DateTime)
only carries a fixed numeric offset. Converting `Zoned → DateTime<FixedOffset>`
preserves the instant and the current offset but **discards the zone's
identity and its DST rule**. A round trip back to `Zoned` yields a
fixed-offset zone — subsequent calendar arithmetic will no longer follow
DST.

To preserve zone identity across a round trip, enable the `chrono-tz`
feature and convert to [`chrono::DateTime<chrono_tz::Tz>`](chrono::DateTime) instead.

## Leap seconds are rejected by default

`chrono` can represent a leap-second reading by storing a subsecond value
in `1_000_000_000..2_000_000_000`. Jiff cannot. The strict conversions
reject such values with an error. If you have data that genuinely
contains leap-second readings, use the helpers in the [`lossy`] module to
clamp them to `:59.999999999` instead.

## `Span` is calendar-aware; `TimeDelta` is not

[`jiff::Span`] can carry `years`, `months`, `weeks`, and `days`, whose
length depends on a reference date. [`chrono::TimeDelta`] is an absolute
number of nanoseconds. The strict `Span → TimeDelta` conversion rejects
any span with nonzero calendar units. If you have decided that days are
exactly 24 hours (a civil-day interpretation that ignores DST), use
[`lossy::span_to_timedelta_days_are_24h`]. For spans that should respect
DST, resolve them first with [`jiff::Span::to_duration`] and an explicit
reference date.

## `NaiveDateTime` has no intrinsic meaning

A [`chrono::NaiveDateTime`] could be a UTC instant, a local wall-clock
reading, or a timezone-less civil datetime — the type does not say.
Because of this ambiguity, this crate deliberately **does not** provide
`NaiveDateTime → Timestamp` or `NaiveDateTime → Zoned`. Only the civil
conversion `NaiveDateTime → jiff::civil::DateTime` is offered.
If your naive value is meant to be a UTC instant, call `.and_utc()` on
the chrono side first:
```
use jiff_chrono::ConvertTryFrom as _;
let naive = chrono::NaiveDate::from_ymd_opt(2025, 1, 30)
    .unwrap()
    .and_hms_opt(17, 58, 30)
    .unwrap();
let ts = jiff::Timestamp::convert_try_from(naive.and_utc())?;
# Ok::<(), Box<dyn std::error::Error>>(())
```
If it is local to a specific zone, use chrono's
`.and_local_timezone(tz).single()` (or the appropriate `LocalResult`
branch) first, so the disambiguation decision is made at the chrono call
site rather than buried inside a conversion.

## DST-gap / DST-fold disambiguation policy

This crate never constructs a zoned datetime from a naive local datetime,
so DST ambiguity is not introduced on the conversion boundary. When you
later build `jiff::Zoned` values from civil datetimes using Jiff's own
API, note that Jiff defaults to `Disambiguation::Compatible` (gap →
shift forward, fold → first occurrence), which may differ from how your
old chrono code resolved `LocalResult::Ambiguous`/`::None`. Audit those
call sites during migration.

## `Timestamp`/`Zoned` vs `DateTime<Utc>`/`DateTime<Tz>`

chrono code often uses `DateTime<Utc>` as a catch-all "timestamp" type.
Jiff splits the concept: [`jiff::Timestamp`] is an absolute instant with
no zone, and [`jiff::Zoned`] is an instant plus a zone. The conversion
traits in this crate preserve that split — `DateTime<Utc> → Timestamp`
discards nothing, but `Zoned ↔ DateTime<Tz>` moves the whole
instant-plus-zone pair. Use the split to audit which variables in your
migrated code are actually instants and which are zone-aware.

# Known gaps

* No conversions involving [`chrono::Local`]. Call
  `.with_timezone(&Utc)` on chrono's side first.
* No conversions from [`jiff::tz::TimeZone`] to a chrono zone type on its
  own; time-zone identity only travels as part of a [`jiff::Zoned`] /
  `chrono::DateTime<Tz>` pair.
* No conversions involving [`std::time::Duration`] — Jiff already provides
  those via [`jiff::SignedDuration`].
* No `NaiveDateTime → Timestamp` / `NaiveDateTime → Zoned`. See the
  "`NaiveDateTime` has no intrinsic meaning" caveat above.
* No [`chrono::Days`] → [`jiff::Span`]. As of `chrono` 0.4.44, the inner
  `u64` of `chrono::Days` is not exposed through any public accessor,
  so we cannot read it out. Reconstruct on the Jiff side via
  [`jiff::ToSpan::days`](jiff::ToSpan::days) instead.

# Crate features

* `std` (default) — enables the standard library. Required by most impls.
* `alloc` — enables heap-allocated error messages in `no_std` builds.
* `chrono-tz` — enables conversions between [`jiff::Zoned`] and
  `chrono::DateTime<chrono_tz::Tz>`. Implies `std`.
* `serde` — enables the `serde` feature on both `jiff` and `chrono`. This
  crate defines no `serde` impls itself.

# Example: migrating a value between the two ecosystems

```
use jiff_chrono::{ConvertFrom as _, ConvertTryFrom as _};

let jiff_ts: jiff::Timestamp = "2025-01-30T17:58:30Z".parse()?;

// Jiff → chrono (infallible for this pair).
let chrono_dt = chrono::DateTime::<chrono::Utc>::convert_from(jiff_ts);
assert_eq!(chrono_dt.to_rfc3339(), "2025-01-30T17:58:30+00:00");

// chrono → Jiff (fallible because chrono's range is wider).
let round_trip = jiff::Timestamp::convert_try_from(chrono_dt)?;
assert_eq!(round_trip, jiff_ts);

# Ok::<(), Box<dyn std::error::Error>>(())
```
*/

#![no_std]
#![deny(missing_docs)]
#![cfg_attr(docsrs_jiff, feature(doc_cfg))]

#[cfg(any(test, feature = "std"))]
extern crate std;

#[cfg(any(test, feature = "alloc"))]
extern crate alloc;

mod civil;
mod duration;
mod error;
pub mod lossy;
mod offset;
mod timestamp;
mod traits;
mod zoned;

pub use self::{
    error::Error,
    traits::{ConvertFrom, ConvertInto, ConvertTryFrom, ConvertTryInto},
};
