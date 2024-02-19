use jiff::{
    civil::{time, Time},
    tz::TimeZone,
    Timestamp, Zoned,
};

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainTime/prototype/equals/argument-string-calendar-annotation-invalid-key.js
#[test]
fn argument_string_calendar_annotation_invalid_key() {
    let strings = [
        "00:00[U-CA=iso8601]",
        "T00:00[U-CA=iso8601]",
        "1970-01-01T00:00[U-CA=iso8601]",
        "00:00[u-CA=iso8601]",
        "T00:00[u-CA=iso8601]",
        "1970-01-01T00:00[u-CA=iso8601]",
        "00:00[FOO=bar]",
        "T00:00[FOO=bar]",
        "1970-01-01T00:00[FOO=bar]",
    ];
    for string in strings {
        assert!(
            string.parse::<Time>().is_err(),
            "{string:?} should fail to parse as `Time`"
        );
    }
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainTime/prototype/equals/argument-string-date-with-utc-offset.js
#[test]
fn argument_string_date_with_utc_offset() {
    let valid = [
        "12:34:56.987654321+00:00",
        "12:34:56.987654321+00:00[UTC]",
        "12:34:56.987654321+00:00[!UTC]",
        "12:34:56.987654321-02:30[America/St_Johns]",
        "1976-11-18T12:34:56.987654321+00:00",
        "1976-11-18T12:34:56.987654321+00:00[UTC]",
        "1976-11-18T12:34:56.987654321+00:00[!UTC]",
        "1976-11-18T12:34:56.987654321-02:30[America/St_Johns]",
    ];
    for string in valid {
        let got: Time = string.parse().unwrap();
        assert_eq!(got, time(12, 34, 56, 987_654_321));
    }

    let invalid = [
        "2022-09-15Z",
        "2022-09-15Z[UTC]",
        "2022-09-15Z[Europe/Vienna]",
        "2022-09-15+00:00",
        "2022-09-15+00:00[UTC]",
        "2022-09-15-02:30",
        "2022-09-15-02:30[America/St_Johns]",
    ];
    for string in invalid {
        assert!(
            string.parse::<Time>().is_err(),
            "expected {string:?} to fail to parse as `Time`"
        );
    }
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainTime/prototype/equals/argument-string-no-implicit-midnight.js
#[test]
fn argument_string_no_implicit_midnight() {
    assert!("2019-10-01".parse::<Time>().is_err());
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainTime/prototype/equals/argument-string-time-separators.js
#[test]
fn argument_string_time_separators() {
    let tests = [
        "1976-11-18T12:34:56.987654321",
        "1976-11-18t12:34:56.987654321",
        "1976-11-18 12:34:56.987654321",
        "T12:34:56.987654321",
        "t12:34:56.987654321",
    ];
    for string in tests {
        let t: Time = string.parse().unwrap();
        assert_eq!(t, time(12, 34, 56, 987_654_321));
    }
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainTime/prototype/equals/argument-string-time-zone-annotation.js
#[test]
fn argument_string_time_zone_annotation() {
    let tests = [
        "12:34:56.987654321[Asia/Kolkata]",
        "12:34:56.987654321[!Europe/Vienna]",
        "12:34:56.987654321[+00:00]",
        "12:34:56.987654321[!-02:30]",
        "T12:34:56.987654321[UTC]",
        "T12:34:56.987654321[!Africa/Abidjan]",
        "T12:34:56.987654321[+01:00]",
        "T12:34:56.987654321[!-08:00]",
        "12:34:56.987654321+00:00[America/Sao_Paulo]",
        "12:34:56.987654321+00:00[!Asia/Tokyo]",
        "12:34:56.987654321+00:00[-02:30]",
        "12:34:56.987654321+00:00[!+00:00]",
        "T12:34:56.987654321+00:00[America/New_York]",
        "T12:34:56.987654321+00:00[!UTC]",
        "T12:34:56.987654321+00:00[-08:00]",
        "T12:34:56.987654321+00:00[!+01:00]",
        "1970-01-01T12:34:56.987654321[Africa/Lagos]",
        "1970-01-01T12:34:56.987654321[!America/Vancouver]",
        "1970-01-01T12:34:56.987654321[+00:00]",
        "1970-01-01T12:34:56.987654321[!-02:30]",
        "1970-01-01T12:34:56.987654321+00:00[Europe/London]",
        "1970-01-01T12:34:56.987654321+00:00[!Asia/Seoul]",
        "1970-01-01T12:34:56.987654321+00:00[+01:00]",
        "1970-01-01T12:34:56.987654321+00:00[!-08:00]",
    ];
    for string in tests {
        let t: Time = string.parse().unwrap();
        assert_eq!(t, time(12, 34, 56, 987_654_321));
    }
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainTime/prototype/equals/argument-string-with-time-designator.js
#[test]
fn argument_string_with_time_designator() {
    let tests = [
        "T00:30",
        "t00:30",
        "T0030",
        "t0030",
        "T00:30:00",
        "t00:30:00",
        "T003000",
        "t003000",
        "T00:30:00.000000000",
        "t00:30:00.000000000",
        "T003000.000000000",
        "t003000.000000000",
    ];
    for string in tests {
        let t: Time = string.parse().unwrap();
        assert_eq!(t, time(0, 30, 0, 0));
    }
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainTime/prototype/equals/argument-string-with-utc-designator.js
#[test]
fn argument_string_with_utc_designator() {
    let invalid = [
        "2019-10-01T09:00:00Z",
        "2019-10-01T09:00:00Z[UTC]",
        "09:00:00Z[UTC]",
        "09:00:00Z",
    ];
    for string in invalid {
        assert!(
            string.parse::<Time>().is_err(),
            "expected {string:?} to fail to parse into a `Time`"
        );
    }
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainTime/prototype/equals/argument-zoneddatetime-balance-negative-time-units.js
#[test]
fn argument_zoneddatetime_balance_negative_time_units() {
    let timestamp = Timestamp::new(3661, 001_001_001).unwrap();
    let zdt = Zoned::new(timestamp, TimeZone::UTC);
    // DIFFERENCE: Temporal has a different result here? Not sure why.
    assert_eq!(zdt.datetime().time(), time(1, 1, 1, 001_001_001));
}

/// Source: https://github.com/tc39/test262/blob/29c6f7028a683b8259140e7d6352ae0ca6448a85/test/built-ins/Temporal/PlainTime/prototype/equals/argument-zoneddatetime-negative-epochnanoseconds.js
#[test]
fn argument_zoneddatetime_negative_epochnanoseconds() {
    let timestamp = Timestamp::new(-13_849_764, -999_999_999).unwrap();
    let zdt = Zoned::new(timestamp, TimeZone::UTC);
    assert_eq!(zdt.datetime().time(), time(16, 50, 35, 000_000_001));
}
