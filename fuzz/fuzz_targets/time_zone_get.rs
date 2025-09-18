#![no_main]

use jiff::tz::TimeZone;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|time_zone_name: &str| {
    // This function should never panic.
    _ = TimeZone::get(time_zone_name);
});
