#![allow(warnings)]
#![no_std]
#![deny(rustdoc::broken_intra_doc_links)]
// No clue why this thing is still unstable because it's pretty amazing. This
// adds Cargo feature annotations to items in the rustdoc output. Which is
// sadly hugely beneficial for this crate due to the number of features.
#![cfg_attr(docsrs, feature(doc_auto_cfg))]
// We generally want all types to impl Debug.
#![warn(missing_debug_implementations)]

// It should be possible to support other pointer widths, but this library
// hasn't been tested nor thought about much in contexts with pointers less
// than 32 bits.
//
// If you need support for 8-bit or 16-bit, please submit a bug report at
// https://github.com/BurntSushi/jiff
#[cfg(not(any(target_pointer_width = "32", target_pointer_width = "64")))]
compile_error!("jiff currently not supported on non-{32,64}");

#[cfg(any(test, feature = "std"))]
extern crate std;

// We don't currently support a non-alloc mode for Jiff. I'm not opposed to
// doing it, but dynamic memory allocation is pretty heavily weaved into some
// core parts of Jiff. In particular, its error types.
//
// When I originally started writing Jiff, my goal was to support a core-only
// mode. But it became too painful to make every use of the heap conditional.
//
// With that said, I believe errors are the only thing that is "pervasive"
// that allocates. That, and time zones. So if core-only was deeply desired,
// we could probably pull the "much worse user experience" level and make it
// happen. Alternatively, we could carve out a "jiff core" crate, although I
// don't really know what that would look like.
//
// If you have a use case for a core-only Jiff, please file an issue. And
// please don't just say, "I want Jiff without heap allocation." Please give a
// detailed accounting of 1) why you can't use dynamic memory allocation and 2)
// what specific functionality from Jiff you actually need.
extern crate alloc;

pub use crate::{
    error::Error,
    instant::{Instant, Tai, TimeScale, Unix},
    span::{Span, ToSpan},
    tz::TimeZone,
    zoned::Zoned,
};

#[macro_use]
mod logging;

pub mod civil;
mod error;
pub mod format;
mod instant;
mod leapseconds;
pub mod round;
mod scale;
pub mod span;
pub mod tz;
mod util;
mod zoned;

#[cfg(test)]
mod tests {
    use std::time::SystemTime;

    use crate::{civil::Date, round::Unit, util::t};

    use super::*;

    #[test]
    fn topscratch() {
        let _ = env_logger::try_init();
        // std::dbg!(t::SpanMonths::MIN, t::SpanMonths::MAX);
        // std::dbg!(t::SpanWeeks::MIN, t::SpanWeeks::MAX);
        // std::dbg!(t::SpanDays::MIN, t::SpanDays::MAX);
        // std::dbg!(t::SpanHours::MIN, t::SpanHours::MAX);
        // std::dbg!(t::SpanMinutes::MIN, t::SpanMinutes::MAX);
        // std::dbg!(t::SpanSeconds::MIN, t::SpanSeconds::MAX);
        // std::dbg!(t::SpanNanoseconds::MIN, t::SpanNanoseconds::MAX);
        // std::dbg!(t::UnixSeconds::MIN, t::UnixSeconds::MAX);

        // let tzname = "America/New_York";
        //
        // let dt = civil::DateTime::constant(2024, 3, 10, 2, 30, 0, 0);
        // let inst: Zoned = dt.to_zoned(tzname).unwrap();
        // let start = inst.start_of_day().unwrap();
        // let end = start.checked_add(1.day()).unwrap();
        // std::dbg!(start.to_instant().until(end.to_instant()));
        //
        // let dt = civil::DateTime::constant(2024, 11, 3, 2, 30, 0, 0);
        // let inst: Zoned = dt.to_zoned(tzname).unwrap();
        // let start = inst.start_of_day().unwrap();
        // let end = start.checked_add(1.day()).unwrap();
        // std::dbg!(start.to_instant().until(end.to_instant()));

        // let dt = civil::DateTime::constant(-9999, 1, 2, 1, 59, 59, 0);
        // let inst: Zoned =
        // dt.to_zoned_with(TimeZone::fixed(tz::Offset::UTC)).unwrap();

        // let dt = civil::DateTime::constant(2024, 3, 9, 2, 30, 0, 0);
        // let inst: Zoned = dt.to_zoned(tzname).unwrap();
        // let later = inst.checked_add(1.day()).unwrap();
        // // let later = inst.checked_add(24.hours()).unwrap();
        // std::dbg!(inst.to_datetime());
        // std::dbg!(later.to_datetime());

        // let dt = civil::DateTime::constant(2024, 11, 2, 1, 30, 0, 0);
        // let inst: Zoned = dt.to_zoned(tzname).unwrap();
        // let later = inst.checked_add(1.day()).unwrap();
        // // let later = inst.checked_add(24.hours()).unwrap();
        // std::dbg!(inst.to_datetime());
        // std::dbg!(later.to_datetime());
        // std::dbg!(later.time_zone().to_offset(later.to_instant()));

        // let tzname = "America/Los_Angeles";
        // let tzdb = tz::TimeZoneDatabase::from_env();
        // let tz = tzdb.get(tzname).unwrap();

        // let dt = civil::DateTime::constant(2015, 06, 30, 23, 59, 60, 0);
        // let unix: Instant = Instant::from_datetime_zulu(dt).unwrap();
        // let tai: Instant<Tai> = Instant::from_datetime_zulu(dt).unwrap();
        // std::dbg!(unix.to_datetime());
        // std::dbg!(tai.to_datetime());

        // let unixz = unix.to_zoned(tzname).unwrap();
        // let taiz = tai.to_zoned(tzname).unwrap();
        // let unixz = Zoned::new(unix, TimeZone::UTC);
        // let taiz = Zoned::new(tai, TimeZone::UTC);
        // std::dbg!(unixz.to_datetime());
        // std::dbg!(taiz.to_datetime());

        // let now = Zoned::new(Instant::now(), tz);
        // std::dbg!(now.to_datetime());
        // let naive_dt = NaiveDateTime::new(date, time);
        // let dt = TIMEZONE.from_local_datetime(&naive_dt).single().unwrap();
        // // The timezone is EST and the DST offset is zero
        // assert_timezone_and_offset(&dt, "EST", 0);

        // let dt = civil::DateTime::constant(2015, 06, 30, 23, 59, 59, 0);
        // let unix: Instant = Instant::from_datetime_zulu(dt).unwrap();
        // let tai: Instant<Tai> = Instant::from_datetime_zulu(dt).unwrap();
        // std::dbg!(dt, unix.second(), tai.second(), tai.to_datetime(), "-----");
        //
        // let dt = civil::DateTime::constant(2015, 06, 30, 23, 59, 60, 0);
        // let unix: Instant = Instant::from_datetime_zulu(dt).unwrap();
        // let tai: Instant<Tai> = Instant::from_datetime_zulu(dt).unwrap();
        // std::dbg!(dt, unix.second(), tai.second(), tai.to_datetime(), "-----");
        //
        // let dt = civil::DateTime::constant(2015, 7, 1, 0, 0, 0, 0);
        // let unix: Instant = Instant::from_datetime_zulu(dt).unwrap();
        // let tai: Instant<Tai> = Instant::from_datetime_zulu(dt).unwrap();
        // std::dbg!(dt, unix.second(), tai.second(), tai.to_datetime(), "-----");
        //
        // let dt = civil::DateTime::constant(2015, 7, 1, 0, 0, 1, 0);
        // let unix: Instant = Instant::from_datetime_zulu(dt).unwrap();
        // let tai: Instant<Tai> = Instant::from_datetime_zulu(dt).unwrap();
        // std::dbg!(dt, unix.second(), tai.second(), tai.to_datetime(), "-----");

        // let dt1 = civil::DateTime::constant(2015, 06, 30, 23, 59, 59, 0);
        // let unix1: Instant = Instant::from_datetime_zulu(dt1).unwrap();
        // let tai1: Instant<Tai> = Instant::from_datetime_zulu(dt1).unwrap();
        //
        // let dt2 = civil::DateTime::constant(2015, 7, 1, 0, 0, 0, 0);
        // let unix2: Instant = Instant::from_datetime_zulu(dt2).unwrap();
        // let tai2: Instant<Tai> = Instant::from_datetime_zulu(dt2).unwrap();
        //
        // std::dbg!(dt2.since(dt1).get_seconds());
        // std::dbg!(unix2.since(unix1).get_seconds());
        // std::dbg!(tai2.since(tai1).get_seconds());

        // let dt = civil::DateTime::constant(2016, 12, 31, 23, 59, 59, 0);
        // let inst: Instant = Instant::from_datetime_zulu(dt).unwrap();
        // std::dbg!(dt, inst);
        //
        // let dt = civil::DateTime::constant(2016, 12, 31, 23, 59, 60, 0);
        // let inst: Instant = Instant::from_datetime_zulu(dt).unwrap();
        // std::dbg!(dt, inst);
        //
        // let dt = civil::DateTime::constant(2017, 1, 1, 0, 0, 0, 0);
        // let inst: Instant = Instant::from_datetime_zulu(dt).unwrap();
        // std::dbg!(dt, inst);

        // let dt1: Zoned = civil::DateTime::constant(2014, 3, 15, 19, 0, 0, 0)
        // .to_zoned("America/New_York")
        // .unwrap();
        // let dt2: Zoned = civil::DateTime::constant(2016, 3, 15, 19, 0, 0, 0)
        // .to_zoned("America/New_York")
        // .unwrap();
        // let span = dt1.until_with_largest_unit(Unit::Hour, &dt2).unwrap();
        // std::eprintln!("{span:?}");
        //
        // let dt1: Zoned<Tai> =
        // civil::DateTime::constant(2014, 3, 15, 19, 0, 0, 0)
        // .to_zoned("America/New_York")
        // .unwrap();
        // let dt2: Zoned<Tai> =
        // civil::DateTime::constant(2016, 3, 15, 19, 0, 0, 0)
        // .to_zoned("America/New_York")
        // .unwrap();
        // let span = dt1.until_with_largest_unit(Unit::Hour, &dt2).unwrap();
        // std::eprintln!("{span:?}");

        {
            use crate::format::temporal::{
                DateTimeParser, Disambiguation, ResolveOffsetConflict,
            };

            // let x = "2020-01-01T12:00-02:00[America/Sao_Paulo]";
            // let x = "2024-03-10T02:30[America/New_York]";
            let x = "2024-11-03T01:30-05[America/New_York]";
            let parsed = DateTimeParser::new()
                .parse_temporal_datetime(x.as_bytes())
                .unwrap()
                .into_full()
                .unwrap();
            let result: Result<Zoned, crate::Error> = parsed.to_zoned(
                crate::tz::db(),
                ResolveOffsetConflict::Reject,
                Disambiguation::Reject,
            );
            match result {
                Ok(zdt) => {
                    std::eprintln!("{}", zdt);
                }
                Err(err) => {
                    std::eprintln!("{}", err);
                }
            }
        }
        /*
        {
            use crate::format::temporal::{
                DateTimeParser, Disambiguation, ResolveOffsetConflict,
            };

            let x = "2024-11-03T01:30-05:00[America/New_York]";
            let parsed = DateTimeParser::new()
                .parse_temporal_datetime(x.as_bytes())
                .unwrap()
                .into_full()
                .unwrap();
            let result: Result<Zoned, crate::Error> = parsed.to_zoned(
                crate::tz::db(),
                ResolveOffsetConflict::Reject,
                Disambiguation::Compatible,
            );
            match result {
                Ok(zdt) => {
                    std::eprintln!("{}", zdt);
                }
                Err(err) => {
                    std::eprintln!("{}", err);
                }
            }
        }
        */
    }
}
