#![allow(warnings)]

use jiff::{
    civil::{Date, DateTime, Time as CivilTime},
    Instant, Span,
};

mod tc39_262;

#[test]
fn scratch() {
    // let t = Time::now();
    // dbg!(t);
    // let dt = t.to_datetime();
    // dbg!(dt);
    //
    // let t = Time::from_unix(-1, 0).unwrap();
    // let dt = t.to_datetime();
    // dbg!(dt);
    //
    // let t = Time::from_unix(0, -1).unwrap();
    // let dt = t.to_datetime();
    // dbg!(dt);

    // let t = Instant::from_unix(-377705116799, -999_999_999).unwrap();
    // let dt = t.to_datetime();
    // dbg!(dt);

    // let start = Date::new(2024, 2, 28).unwrap();
    // let span = Span::new().years(1).months(1);
    // let span = Span::new()
    // .hours(23)
    // .minutes(59)
    // .seconds(59)
    // .nanoseconds(1_000_000_000);
    // let end = start.add(span);
    // eprintln!("{end:?}");
}
