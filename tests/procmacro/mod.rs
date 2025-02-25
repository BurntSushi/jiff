use jiff::{
    civil::date,
    tz::{self, AmbiguousOffset, Offset, TimeZone},
    Timestamp,
};

/// Tests Jiff's "static" time zone support via the proc macro.
///
/// This test was copied from `src/tz/timezone.rs`, and modified to use the
/// proc macro. This test isn't in Jiff proper since it seems like unit tests
/// are compiled with a different copy of Jiff, and the `TimeZone` type created
/// by the proc macro doesn't match the one used by the unit tests.
#[test]
fn time_zone_static_tzif_to_ambiguous_timestamp() {
    let tests: &[(TimeZone, &[_])] = &[
        (
            tz::get!("America/New_York"),
            &[
                ((1969, 12, 31, 19, 0, 0, 0), unambiguous(-5)),
                ((2024, 3, 10, 1, 59, 59, 999_999_999), unambiguous(-5)),
                ((2024, 3, 10, 2, 0, 0, 0), gap(-5, -4)),
                ((2024, 3, 10, 2, 59, 59, 999_999_999), gap(-5, -4)),
                ((2024, 3, 10, 3, 0, 0, 0), unambiguous(-4)),
                ((2024, 11, 3, 0, 59, 59, 999_999_999), unambiguous(-4)),
                ((2024, 11, 3, 1, 0, 0, 0), fold(-4, -5)),
                ((2024, 11, 3, 1, 59, 59, 999_999_999), fold(-4, -5)),
                ((2024, 11, 3, 2, 0, 0, 0), unambiguous(-5)),
            ],
        ),
        (
            tz::get!("Europe/Dublin"),
            &[
                ((1970, 1, 1, 0, 0, 0, 0), unambiguous(1)),
                ((2024, 3, 31, 0, 59, 59, 999_999_999), unambiguous(0)),
                ((2024, 3, 31, 1, 0, 0, 0), gap(0, 1)),
                ((2024, 3, 31, 1, 59, 59, 999_999_999), gap(0, 1)),
                ((2024, 3, 31, 2, 0, 0, 0), unambiguous(1)),
                ((2024, 10, 27, 0, 59, 59, 999_999_999), unambiguous(1)),
                ((2024, 10, 27, 1, 0, 0, 0), fold(1, 0)),
                ((2024, 10, 27, 1, 59, 59, 999_999_999), fold(1, 0)),
                ((2024, 10, 27, 2, 0, 0, 0), unambiguous(0)),
            ],
        ),
        (
            tz::get!("Australia/Tasmania"),
            &[
                ((1970, 1, 1, 11, 0, 0, 0), unambiguous(11)),
                ((2024, 4, 7, 1, 59, 59, 999_999_999), unambiguous(11)),
                ((2024, 4, 7, 2, 0, 0, 0), fold(11, 10)),
                ((2024, 4, 7, 2, 59, 59, 999_999_999), fold(11, 10)),
                ((2024, 4, 7, 3, 0, 0, 0), unambiguous(10)),
                ((2024, 10, 6, 1, 59, 59, 999_999_999), unambiguous(10)),
                ((2024, 10, 6, 2, 0, 0, 0), gap(10, 11)),
                ((2024, 10, 6, 2, 59, 59, 999_999_999), gap(10, 11)),
                ((2024, 10, 6, 3, 0, 0, 0), unambiguous(11)),
            ],
        ),
        (
            tz::get!("Antarctica/Troll"),
            &[
                ((1970, 1, 1, 0, 0, 0, 0), unambiguous(0)),
                // test the gap
                ((2024, 3, 31, 0, 59, 59, 999_999_999), unambiguous(0)),
                ((2024, 3, 31, 1, 0, 0, 0), gap(0, 2)),
                ((2024, 3, 31, 1, 59, 59, 999_999_999), gap(0, 2)),
                // still in the gap!
                ((2024, 3, 31, 2, 0, 0, 0), gap(0, 2)),
                ((2024, 3, 31, 2, 59, 59, 999_999_999), gap(0, 2)),
                // finally out
                ((2024, 3, 31, 3, 0, 0, 0), unambiguous(2)),
                // test the fold
                ((2024, 10, 27, 0, 59, 59, 999_999_999), unambiguous(2)),
                ((2024, 10, 27, 1, 0, 0, 0), fold(2, 0)),
                ((2024, 10, 27, 1, 59, 59, 999_999_999), fold(2, 0)),
                // still in the fold!
                ((2024, 10, 27, 2, 0, 0, 0), fold(2, 0)),
                ((2024, 10, 27, 2, 59, 59, 999_999_999), fold(2, 0)),
                // finally out
                ((2024, 10, 27, 3, 0, 0, 0), unambiguous(0)),
            ],
        ),
        (
            tz::get!("America/St_Johns"),
            &[
                ((1969, 12, 31, 20, 30, 0, 0), o_unambiguous(-hms(3, 30, 0))),
                (
                    (2024, 3, 10, 1, 59, 59, 999_999_999),
                    o_unambiguous(-hms(3, 30, 0)),
                ),
                (
                    (2024, 3, 10, 2, 0, 0, 0),
                    o_gap(-hms(3, 30, 0), -hms(2, 30, 0)),
                ),
                (
                    (2024, 3, 10, 2, 59, 59, 999_999_999),
                    o_gap(-hms(3, 30, 0), -hms(2, 30, 0)),
                ),
                ((2024, 3, 10, 3, 0, 0, 0), o_unambiguous(-hms(2, 30, 0))),
                (
                    (2024, 11, 3, 0, 59, 59, 999_999_999),
                    o_unambiguous(-hms(2, 30, 0)),
                ),
                (
                    (2024, 11, 3, 1, 0, 0, 0),
                    o_fold(-hms(2, 30, 0), -hms(3, 30, 0)),
                ),
                (
                    (2024, 11, 3, 1, 59, 59, 999_999_999),
                    o_fold(-hms(2, 30, 0), -hms(3, 30, 0)),
                ),
                ((2024, 11, 3, 2, 0, 0, 0), o_unambiguous(-hms(3, 30, 0))),
            ],
        ),
        // This time zone has an interesting transition where it jumps
        // backwards a full day at 1867-10-19T15:30:00.
        (
            tz::get!("America/Sitka"),
            &[
                ((1969, 12, 31, 16, 0, 0, 0), unambiguous(-8)),
                ((-9999, 1, 2, 16, 58, 46, 0), o_unambiguous(hms(14, 58, 47))),
                (
                    (1867, 10, 18, 15, 29, 59, 0),
                    o_unambiguous(hms(14, 58, 47)),
                ),
                (
                    (1867, 10, 18, 15, 30, 0, 0),
                    // A fold of 24 hours!!!
                    o_fold(hms(14, 58, 47), -hms(9, 1, 13)),
                ),
                (
                    (1867, 10, 19, 15, 29, 59, 999_999_999),
                    // Still in the fold...
                    o_fold(hms(14, 58, 47), -hms(9, 1, 13)),
                ),
                (
                    (1867, 10, 19, 15, 30, 0, 0),
                    // Finally out.
                    o_unambiguous(-hms(9, 1, 13)),
                ),
            ],
        ),
        // As with to_datetime, we test every possible transition
        // point here since this time zone has a small number of them.
        (
            tz::get!("Pacific/Honolulu"),
            &[
                (
                    (1896, 1, 13, 11, 59, 59, 0),
                    o_unambiguous(-hms(10, 31, 26)),
                ),
                (
                    (1896, 1, 13, 12, 0, 0, 0),
                    o_gap(-hms(10, 31, 26), -hms(10, 30, 0)),
                ),
                (
                    (1896, 1, 13, 12, 1, 25, 0),
                    o_gap(-hms(10, 31, 26), -hms(10, 30, 0)),
                ),
                ((1896, 1, 13, 12, 1, 26, 0), o_unambiguous(-hms(10, 30, 0))),
                ((1933, 4, 30, 1, 59, 59, 0), o_unambiguous(-hms(10, 30, 0))),
                (
                    (1933, 4, 30, 2, 0, 0, 0),
                    o_gap(-hms(10, 30, 0), -hms(9, 30, 0)),
                ),
                (
                    (1933, 4, 30, 2, 59, 59, 0),
                    o_gap(-hms(10, 30, 0), -hms(9, 30, 0)),
                ),
                ((1933, 4, 30, 3, 0, 0, 0), o_unambiguous(-hms(9, 30, 0))),
                ((1933, 5, 21, 10, 59, 59, 0), o_unambiguous(-hms(9, 30, 0))),
                (
                    (1933, 5, 21, 11, 0, 0, 0),
                    o_fold(-hms(9, 30, 0), -hms(10, 30, 0)),
                ),
                (
                    (1933, 5, 21, 11, 59, 59, 0),
                    o_fold(-hms(9, 30, 0), -hms(10, 30, 0)),
                ),
                ((1933, 5, 21, 12, 0, 0, 0), o_unambiguous(-hms(10, 30, 0))),
                ((1942, 2, 9, 1, 59, 59, 0), o_unambiguous(-hms(10, 30, 0))),
                (
                    (1942, 2, 9, 2, 0, 0, 0),
                    o_gap(-hms(10, 30, 0), -hms(9, 30, 0)),
                ),
                (
                    (1942, 2, 9, 2, 59, 59, 0),
                    o_gap(-hms(10, 30, 0), -hms(9, 30, 0)),
                ),
                ((1942, 2, 9, 3, 0, 0, 0), o_unambiguous(-hms(9, 30, 0))),
                ((1945, 8, 14, 13, 29, 59, 0), o_unambiguous(-hms(9, 30, 0))),
                ((1945, 8, 14, 13, 30, 0, 0), o_unambiguous(-hms(9, 30, 0))),
                ((1945, 8, 14, 13, 30, 1, 0), o_unambiguous(-hms(9, 30, 0))),
                ((1945, 9, 30, 0, 59, 59, 0), o_unambiguous(-hms(9, 30, 0))),
                (
                    (1945, 9, 30, 1, 0, 0, 0),
                    o_fold(-hms(9, 30, 0), -hms(10, 30, 0)),
                ),
                (
                    (1945, 9, 30, 1, 59, 59, 0),
                    o_fold(-hms(9, 30, 0), -hms(10, 30, 0)),
                ),
                ((1945, 9, 30, 2, 0, 0, 0), o_unambiguous(-hms(10, 30, 0))),
                ((1947, 6, 8, 1, 59, 59, 0), o_unambiguous(-hms(10, 30, 0))),
                (
                    (1947, 6, 8, 2, 0, 0, 0),
                    o_gap(-hms(10, 30, 0), -tz::offset(10)),
                ),
                (
                    (1947, 6, 8, 2, 29, 59, 0),
                    o_gap(-hms(10, 30, 0), -tz::offset(10)),
                ),
                ((1947, 6, 8, 2, 30, 0, 0), unambiguous(-10)),
            ],
        ),
    ];
    for &(ref tz, datetimes_to_ambiguous) in tests {
        let tzname = tz.iana_name().unwrap();
        // let test_file = TzifTestFile::get(tzname);
        // let tz = TimeZone::tzif(test_file.name, test_file.data).unwrap();
        for &(datetime, ambiguous_kind) in datetimes_to_ambiguous {
            let (year, month, day, hour, min, sec, nano) = datetime;
            let dt = date(year, month, day).at(hour, min, sec, nano);
            let got = tz.to_ambiguous_zoned(dt);
            assert_eq!(
                got.offset(),
                ambiguous_kind,
                "\nTZ: {tzname}\ndatetime: \
                     {year:04}-{month:02}-{day:02}T\
                     {hour:02}:{min:02}:{sec:02}.{nano:09}",
            );
        }
    }
}

#[test]
fn time_zone_static_tzif_to_datetime() {
    let o = |hours| tz::offset(hours);
    let tests: &[(TimeZone, &[_])] = &[
        (
            tz::get!("America/New_York"),
            &[
                ((0, 0), o(-5), "EST", (1969, 12, 31, 19, 0, 0, 0)),
                ((1710052200, 0), o(-5), "EST", (2024, 3, 10, 1, 30, 0, 0)),
                (
                    (1710053999, 999_999_999),
                    o(-5),
                    "EST",
                    (2024, 3, 10, 1, 59, 59, 999_999_999),
                ),
                ((1710054000, 0), o(-4), "EDT", (2024, 3, 10, 3, 0, 0, 0)),
                ((1710055800, 0), o(-4), "EDT", (2024, 3, 10, 3, 30, 0, 0)),
                ((1730610000, 0), o(-4), "EDT", (2024, 11, 3, 1, 0, 0, 0)),
                ((1730611800, 0), o(-4), "EDT", (2024, 11, 3, 1, 30, 0, 0)),
                (
                    (1730613599, 999_999_999),
                    o(-4),
                    "EDT",
                    (2024, 11, 3, 1, 59, 59, 999_999_999),
                ),
                ((1730613600, 0), o(-5), "EST", (2024, 11, 3, 1, 0, 0, 0)),
                ((1730615400, 0), o(-5), "EST", (2024, 11, 3, 1, 30, 0, 0)),
            ],
        ),
        (
            tz::get!("Australia/Tasmania"),
            &[
                ((0, 0), o(11), "AEDT", (1970, 1, 1, 11, 0, 0, 0)),
                ((1728142200, 0), o(10), "AEST", (2024, 10, 6, 1, 30, 0, 0)),
                (
                    (1728143999, 999_999_999),
                    o(10),
                    "AEST",
                    (2024, 10, 6, 1, 59, 59, 999_999_999),
                ),
                ((1728144000, 0), o(11), "AEDT", (2024, 10, 6, 3, 0, 0, 0)),
                ((1728145800, 0), o(11), "AEDT", (2024, 10, 6, 3, 30, 0, 0)),
                ((1712415600, 0), o(11), "AEDT", (2024, 4, 7, 2, 0, 0, 0)),
                ((1712417400, 0), o(11), "AEDT", (2024, 4, 7, 2, 30, 0, 0)),
                (
                    (1712419199, 999_999_999),
                    o(11),
                    "AEDT",
                    (2024, 4, 7, 2, 59, 59, 999_999_999),
                ),
                ((1712419200, 0), o(10), "AEST", (2024, 4, 7, 2, 0, 0, 0)),
                ((1712421000, 0), o(10), "AEST", (2024, 4, 7, 2, 30, 0, 0)),
            ],
        ),
        // Pacific/Honolulu is small eough that we just test every
        // possible instant before, at and after each transition.
        (
            tz::get!("Pacific/Honolulu"),
            &[
                (
                    (-2334101315, 0),
                    -hms(10, 31, 26),
                    "LMT",
                    (1896, 1, 13, 11, 59, 59, 0),
                ),
                (
                    (-2334101314, 0),
                    -hms(10, 30, 0),
                    "HST",
                    (1896, 1, 13, 12, 1, 26, 0),
                ),
                (
                    (-2334101313, 0),
                    -hms(10, 30, 0),
                    "HST",
                    (1896, 1, 13, 12, 1, 27, 0),
                ),
                (
                    (-1157283001, 0),
                    -hms(10, 30, 0),
                    "HST",
                    (1933, 4, 30, 1, 59, 59, 0),
                ),
                (
                    (-1157283000, 0),
                    -hms(9, 30, 0),
                    "HDT",
                    (1933, 4, 30, 3, 0, 0, 0),
                ),
                (
                    (-1157282999, 0),
                    -hms(9, 30, 0),
                    "HDT",
                    (1933, 4, 30, 3, 0, 1, 0),
                ),
                (
                    (-1155436201, 0),
                    -hms(9, 30, 0),
                    "HDT",
                    (1933, 5, 21, 11, 59, 59, 0),
                ),
                (
                    (-1155436200, 0),
                    -hms(10, 30, 0),
                    "HST",
                    (1933, 5, 21, 11, 0, 0, 0),
                ),
                (
                    (-1155436199, 0),
                    -hms(10, 30, 0),
                    "HST",
                    (1933, 5, 21, 11, 0, 1, 0),
                ),
                (
                    (-880198201, 0),
                    -hms(10, 30, 0),
                    "HST",
                    (1942, 2, 9, 1, 59, 59, 0),
                ),
                (
                    (-880198200, 0),
                    -hms(9, 30, 0),
                    "HWT",
                    (1942, 2, 9, 3, 0, 0, 0),
                ),
                (
                    (-880198199, 0),
                    -hms(9, 30, 0),
                    "HWT",
                    (1942, 2, 9, 3, 0, 1, 0),
                ),
                (
                    (-769395601, 0),
                    -hms(9, 30, 0),
                    "HWT",
                    (1945, 8, 14, 13, 29, 59, 0),
                ),
                (
                    (-769395600, 0),
                    -hms(9, 30, 0),
                    "HPT",
                    (1945, 8, 14, 13, 30, 0, 0),
                ),
                (
                    (-769395599, 0),
                    -hms(9, 30, 0),
                    "HPT",
                    (1945, 8, 14, 13, 30, 1, 0),
                ),
                (
                    (-765376201, 0),
                    -hms(9, 30, 0),
                    "HPT",
                    (1945, 9, 30, 1, 59, 59, 0),
                ),
                (
                    (-765376200, 0),
                    -hms(10, 30, 0),
                    "HST",
                    (1945, 9, 30, 1, 0, 0, 0),
                ),
                (
                    (-765376199, 0),
                    -hms(10, 30, 0),
                    "HST",
                    (1945, 9, 30, 1, 0, 1, 0),
                ),
                (
                    (-712150201, 0),
                    -hms(10, 30, 0),
                    "HST",
                    (1947, 6, 8, 1, 59, 59, 0),
                ),
                // At this point, we hit the last transition and the POSIX
                // TZ string takes over.
                (
                    (-712150200, 0),
                    -hms(10, 0, 0),
                    "HST",
                    (1947, 6, 8, 2, 30, 0, 0),
                ),
                (
                    (-712150199, 0),
                    -hms(10, 0, 0),
                    "HST",
                    (1947, 6, 8, 2, 30, 1, 0),
                ),
            ],
        ),
        // This time zone has an interesting transition where it jumps
        // backwards a full day at 1867-10-19T15:30:00.
        (
            tz::get!("America/Sitka"),
            &[
                ((0, 0), o(-8), "PST", (1969, 12, 31, 16, 0, 0, 0)),
                (
                    (-377705023201, 0),
                    hms(14, 58, 47),
                    "LMT",
                    (-9999, 1, 2, 16, 58, 46, 0),
                ),
                (
                    (-3225223728, 0),
                    hms(14, 58, 47),
                    "LMT",
                    (1867, 10, 19, 15, 29, 59, 0),
                ),
                // Notice the 24 hour time jump backwards a whole day!
                (
                    (-3225223727, 0),
                    -hms(9, 1, 13),
                    "LMT",
                    (1867, 10, 18, 15, 30, 0, 0),
                ),
                (
                    (-3225223726, 0),
                    -hms(9, 1, 13),
                    "LMT",
                    (1867, 10, 18, 15, 30, 1, 0),
                ),
            ],
        ),
    ];
    for &(ref tz, timestamps_to_datetimes) in tests {
        let tzname = tz.iana_name().unwrap();
        for &((unix_sec, unix_nano), offset, abbrev, datetime) in
            timestamps_to_datetimes
        {
            let (year, month, day, hour, min, sec, nano) = datetime;
            let timestamp = Timestamp::new(unix_sec, unix_nano).unwrap();
            let info = tz.to_offset_info(timestamp);
            assert_eq!(
                info.offset(),
                offset,
                "\nTZ={tzname}, timestamp({unix_sec}, {unix_nano})",
            );
            assert_eq!(
                info.abbreviation(),
                abbrev,
                "\nTZ={tzname}, timestamp({unix_sec}, {unix_nano})",
            );
            assert_eq!(
                info.offset().to_datetime(timestamp),
                date(year, month, day).at(hour, min, sec, nano),
                "\nTZ={tzname}, timestamp({unix_sec}, {unix_nano})",
            );
        }
    }
}

fn hms(hours: i8, minutes: i8, seconds: i8) -> Offset {
    let seconds =
        (hours as i32 * 60 * 60) + (minutes as i32 * 60) + (seconds as i32);
    Offset::from_seconds(seconds).unwrap()
}

fn unambiguous(offset_hours: i8) -> AmbiguousOffset {
    let offset = tz::offset(offset_hours);
    o_unambiguous(offset)
}

fn gap(earlier_offset_hours: i8, later_offset_hours: i8) -> AmbiguousOffset {
    let earlier = tz::offset(earlier_offset_hours);
    let later = tz::offset(later_offset_hours);
    o_gap(earlier, later)
}

fn fold(earlier_offset_hours: i8, later_offset_hours: i8) -> AmbiguousOffset {
    let earlier = tz::offset(earlier_offset_hours);
    let later = tz::offset(later_offset_hours);
    o_fold(earlier, later)
}

fn o_unambiguous(offset: Offset) -> AmbiguousOffset {
    AmbiguousOffset::Unambiguous { offset }
}

fn o_gap(earlier: Offset, later: Offset) -> AmbiguousOffset {
    AmbiguousOffset::Gap { before: earlier, after: later }
}

fn o_fold(earlier: Offset, later: Offset) -> AmbiguousOffset {
    AmbiguousOffset::Fold { before: earlier, after: later }
}
