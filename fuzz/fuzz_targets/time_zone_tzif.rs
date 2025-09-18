#![no_main]

use jiff::tz::TimeZone;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|input: (&str, &[u8])| {
    let (name, data) = input;
    // This function should never panic.
    _ = TimeZone::tzif(name, data);
});
