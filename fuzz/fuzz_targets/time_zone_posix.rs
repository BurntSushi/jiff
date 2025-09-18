#![no_main]

use jiff::tz::TimeZone;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|posix_tz_string: &str| {
    // This function should never panic.
    _ = TimeZone::posix(posix_tz_string);
});
