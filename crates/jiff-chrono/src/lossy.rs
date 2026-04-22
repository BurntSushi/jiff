/*!
Opt-in conversions that change the **meaning** of a value, not just its
representation.

Every function in this module makes a semantic choice that the default,
strict conversion traits refuse to make for you. Calling one of these
functions is an explicit acknowledgment of that choice.

None of these helpers are traits — they are plainly named functions so
that each call site makes the trade-off visible.

# When to use these

* [`naive_time_saturating`] / [`naive_datetime_saturating`] /
  [`utc_datetime_saturating`] — when you have chrono data that genuinely
  contains leap-second readings (nanoseconds `>= 1_000_000_000`) and you
  prefer clamping them to `:59.999999999` over rejecting them.
* [`span_to_timedelta_days_are_24h`] — when you want to convert a
  [`jiff::Span`] that has nonzero `days` to a [`chrono::TimeDelta`] and you
  have decided that days should be treated as exactly 24 hours (civil
  days, ignoring DST transitions). If your span may cross a DST boundary,
  use [`jiff::Span::to_duration`] with an explicit reference date
  instead.
*/

use chrono::{
    DateTime as ChronoDateTime, NaiveDateTime as ChronoNaiveDateTime,
    NaiveTime as ChronoNaiveTime, TimeDelta as ChronoTimeDelta, Timelike as _,
    Utc,
};
use jiff::{
    civil::{DateTime as JiffDateTime, Time as JiffTime},
    Span as JiffSpan, SpanRelativeTo, Timestamp as JiffTimestamp,
};

use crate::{
    error::Error,
    traits::{ConvertTryFrom, ConvertTryInto as _},
};

/// Convert a [`chrono::NaiveTime`] to [`jiff::civil::Time`], saturating any
/// leap-second value down to `23:59:59.999999999`.
///
/// Chrono represents a leap-second reading by storing a nanosecond value
/// in `1_000_000_000..2_000_000_000`. Jiff has no representation for leap
/// seconds, so the strict
/// [`ConvertTryFrom`](crate::ConvertTryFrom) impl rejects such values.
/// This helper instead clamps them to the last representable instant
/// within the minute.
///
/// # Example
///
/// ```
/// let leap =
///     chrono::NaiveTime::from_hms_nano_opt(23, 59, 59, 1_500_000_000)
///         .unwrap();
/// let t = jiff_chrono::lossy::naive_time_saturating(leap);
/// assert_eq!(t, jiff::civil::time(23, 59, 59, 999_999_999));
/// ```
pub fn naive_time_saturating(t: ChronoNaiveTime) -> JiffTime {
    let nano = t.nanosecond();
    let nano = if nano >= 1_000_000_000 { 999_999_999 } else { nano };
    // NaiveTime guarantees hour in 0..24, minute in 0..60, second in 0..60.
    JiffTime::new(
        t.hour() as i8,
        t.minute() as i8,
        t.second() as i8,
        nano as i32,
    )
    .unwrap()
}

/// Convert a [`chrono::NaiveDateTime`] to [`jiff::civil::DateTime`],
/// saturating any leap-second value in the time component.
///
/// Fails if the date component is outside Jiff's year range of
/// `-9999..=9999`.
///
/// See [`naive_time_saturating`] for the leap-second policy.
pub fn naive_datetime_saturating(
    dt: ChronoNaiveDateTime,
) -> Result<JiffDateTime, Error> {
    let date = dt.date().convert_try_into()?;
    let time = naive_time_saturating(dt.time());
    Ok(JiffDateTime::from_parts(date, time))
}

/// Convert a [`chrono::DateTime<Utc>`](chrono::DateTime) to [`jiff::Timestamp`],
/// saturating any leap-second value down to `:59.999999999`.
///
/// Fails only if the underlying instant is outside Jiff's timestamp range.
///
/// # Example
///
/// ```
/// // Construct a `DateTime<Utc>` that carries a leap-second reading.
/// // `and_hms_nano_opt` accepts nanos up to 2_000_000_000 when the
/// // second is 59, which is how chrono encodes `:60.x`.
/// let leap = chrono::NaiveDate::from_ymd_opt(2016, 12, 31)
///     .unwrap()
///     .and_hms_nano_opt(23, 59, 59, 1_500_000_000)
///     .unwrap()
///     .and_utc();
/// let ts = jiff_chrono::lossy::utc_datetime_saturating(leap)?;
/// assert_eq!(ts.to_string(), "2016-12-31T23:59:59.999999999Z");
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
pub fn utc_datetime_saturating(
    dt: ChronoDateTime<Utc>,
) -> Result<JiffTimestamp, Error> {
    // When chrono stores a leap-second instant, `timestamp()` returns the
    // seconds of the preceding non-leap instant (i.e. ':59'), and
    // `timestamp_subsec_nanos()` returns a value in
    // `1_000_000_000..2_000_000_000`. Clamping the nanos to 999_999_999
    // picks "the last nanosecond of the minute," matching the policy used
    // by [`naive_time_saturating`].
    let secs = dt.timestamp();
    let nanos = dt.timestamp_subsec_nanos();
    let nanos = if nanos >= 1_000_000_000 { 999_999_999 } else { nanos };
    Ok(JiffTimestamp::new(secs, nanos as i32)?)
}

/// Convert a [`jiff::Span`] to [`chrono::TimeDelta`] under the assumption
/// that days are always exactly 24 hours.
///
/// The strict [`ConvertTryFrom`](crate::ConvertTryFrom) impl for
/// `TimeDelta` refuses spans with any nonzero calendar units (years,
/// months, weeks, days), because in general those units only have a
/// well-defined length relative to a reference date. This helper
/// accepts spans whose largest unit is `day` by treating each day as
/// 24 × 60 × 60 seconds — the civil-day interpretation. Spans with
/// nonzero weeks, months, or years still fail, because those units
/// cannot be resolved without a reference date even under this policy.
///
/// If your span might cross a DST boundary, prefer
/// [`jiff::Span::to_duration`] with an explicit civil or zoned
/// reference instead of this helper.
///
/// # Example
///
/// ```
/// use jiff::ToSpan;
///
/// let td = jiff_chrono::lossy::span_to_timedelta_days_are_24h(
///     1.day().hours(2),
/// )?;
/// assert_eq!(td.num_hours(), 26);
///
/// // Weeks/months/years are still rejected.
/// assert!(jiff_chrono::lossy::span_to_timedelta_days_are_24h(
///     1.month(),
/// ).is_err());
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
pub fn span_to_timedelta_days_are_24h(
    span: JiffSpan,
) -> Result<ChronoTimeDelta, Error> {
    let sd = span.to_duration(SpanRelativeTo::days_are_24_hours())?;
    ChronoTimeDelta::convert_try_from(sd)
}
