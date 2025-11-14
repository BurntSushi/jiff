fn main() {
    env_logger::init();

    // SAFETY: This is a single threaded program.
    unsafe {
        std::env::set_var("TZ", "WAT5HUH");
    }
    assert_eq!(
        jiff::tz::TimeZone::try_system().unwrap_err().to_string(),
        "`TZ` environment variable set, but failed to read value: \
         failed to read `TZ` environment variable value as a TZif file \
         after attempting (and failing) a tzdb lookup for that same value",
    );

    // SAFETY: This is a single threaded program.
    unsafe {
        std::env::set_var("TZ", "/usr/share/zoneinfo/WAT5HUH");
    }
    assert_eq!(
        jiff::tz::TimeZone::try_system().unwrap_err().to_string(),
        "`TZ` environment variable set, but failed to read value: \
         failed to read `TZ` environment variable value as a TZif file \
         after attempting (and failing) a tzdb lookup for that same value",
    );

    unsafe {
        std::env::set_var("TZ", "");
    }
    assert_eq!(
        jiff::tz::TimeZone::try_system().unwrap(),
        jiff::tz::TimeZone::UTC,
    );
}
