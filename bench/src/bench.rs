use std::hint::black_box as bb;

use criterion::Criterion;

/// This benchmarks the time it takes to convert a civil datetime to a specific
/// instant, *including* the time it takes to lookup a time zone in the system
/// zoneinfo database. (Lookups may be cached by the library, but that is part
/// of the benchmark model.)
///
/// This applies when, for example, parsing a large number of datetime strings
/// with a time zone in them, e.g., `2024-06-30T13:42-04[America/New_York]`.
/// Jiff is the only Rust library to support RFC 9542 time zone annotations, so
/// we don't measure the parsing here and instead just the TZ name lookup and
/// resolution to an instant.
fn civil_datetime_to_instant_with_tzdb_lookup(c: &mut Criterion) {
    const NAME: &str = "civil_datetime_to_instant_with_tzdb_lookup";
    const TZNAME: &str = "America/New_York";
    const STAMP: i64 = 1719755160;

    if jiff::tz::TimeZone::get(TZNAME).is_ok() {
        let dt = jiff::civil::date(2024, 6, 30).at(9, 46, 0, 0);
        c.bench_function(&format!("jiff/{NAME}"), |b| {
            b.iter(|| {
                let zdt = bb(dt).intz(bb(TZNAME)).unwrap();
                assert_eq!(zdt.timestamp().as_second(), STAMP)
            })
        });
    }

    #[cfg(unix)]
    {
        if tzfile::Tz::named(TZNAME).is_ok() {
            let dt = chrono::NaiveDateTime::new(
                chrono::NaiveDate::from_ymd_opt(2024, 6, 30).unwrap(),
                chrono::NaiveTime::from_hms_opt(9, 46, 0).unwrap(),
            );
            c.bench_function(&format!("chrono-tzfile/{NAME}"), |b| {
                use chrono::TimeZone;

                b.iter(|| {
                    let tz = tzfile::Tz::named(bb(TZNAME)).unwrap();
                    let mapped = (&tz).from_local_datetime(bb(&dt));
                    let zdt = mapped.single().unwrap();
                    assert_eq!(zdt.timestamp(), STAMP);
                })
            });
        }
    }

    // The `time` crate doesn't support this.
}

/// Benchmarks the time it takes to convert a civil datetime to a specific
/// instant, *not* including the time it takes to do a time zone lookup.
///
/// This is useful when you have a known time zone already and want to get
/// a specific instant for many distinct civil datetimes in that time zone.
fn civil_datetime_to_instant_static(c: &mut Criterion) {
    const NAME: &str = "civil_datetime_to_instant_static";
    const TZNAME: &str = "America/New_York";
    const STAMP: i64 = 1719755160;

    if let Ok(tz) = jiff::tz::TimeZone::get(TZNAME) {
        let dt = jiff::civil::date(2024, 6, 30).at(9, 46, 0, 0);
        c.bench_function(&format!("jiff/{NAME}"), |b| {
            b.iter(|| {
                // The natural way to do this is `dt.to_zoned(..)`, but
                // Jiff doesn't actually require one to materialize a `Zoned`
                // to disambiguate a civil datetime.
                let ts = bb(&tz).to_timestamp(bb(dt)).unwrap();
                assert_eq!(ts.as_second(), STAMP);
            })
        });
    }

    #[cfg(unix)]
    {
        if let Ok(tz) = tzfile::Tz::named(TZNAME) {
            let dt = chrono::NaiveDateTime::new(
                chrono::NaiveDate::from_ymd_opt(2024, 6, 30).unwrap(),
                chrono::NaiveTime::from_hms_opt(9, 46, 0).unwrap(),
            );
            c.bench_function(&format!("chrono-tzfile/{NAME}"), |b| {
                use chrono::TimeZone;

                b.iter(|| {
                    let mapped = (&tz).from_local_datetime(bb(&dt));
                    let zdt = mapped.single().unwrap();
                    assert_eq!(zdt.timestamp(), STAMP);
                })
            });
        }
    }

    let dt = chrono::NaiveDateTime::new(
        chrono::NaiveDate::from_ymd_opt(2024, 6, 30).unwrap(),
        chrono::NaiveTime::from_hms_opt(9, 46, 0).unwrap(),
    );
    c.bench_function(&format!("chrono/{NAME}"), |b| {
        use chrono::TimeZone;
        use chrono_tz::America::New_York;

        b.iter(|| {
            let mapped = New_York.from_local_datetime(bb(&dt));
            let zdt = mapped.single().unwrap();
            assert_eq!(zdt.timestamp(), STAMP);
        })
    });

    // The `time` crate doesn't support this.
}

/// Benchmarks the conversion of an instant in time to a civil datetime. This
/// type of operation might be commonly used when converting a timestamp to a
/// human readable representation (i.e., what you might see on a clock) in a
/// specific time zone.
fn instant_to_civil_datetime_static(c: &mut Criterion) {
    const NAME: &str = "instant_to_civil_datetime_static";

    fn define(c: &mut Criterion, tz_name: &str, timestamp: i64) {
        if let Ok(tz) = jiff::tz::TimeZone::get(tz_name) {
            let expected = jiff::civil::date(2024, 6, 30).at(9, 46, 0, 0);

            let ts = jiff::Timestamp::from_second(timestamp).unwrap();

            c.bench_function(&format!("jiff/{NAME}-{tz_name}"), |b| {
                b.iter(|| {
                    let zdt = bb(ts).to_zoned(bb(&tz).clone());
                    assert_eq!(zdt.datetime(), expected);
                })
            });
        }

        #[cfg(unix)]
        {
            if let Ok(tz) = tzfile::Tz::named(tz_name) {
                let expected = chrono::NaiveDateTime::new(
                    chrono::NaiveDate::from_ymd_opt(2024, 6, 30).unwrap(),
                    chrono::NaiveTime::from_hms_opt(9, 46, 0).unwrap(),
                );
                c.bench_function(
                    &format!("chrono-tzfile/{NAME}-{tz_name}"),
                    |b| {
                        use chrono::TimeZone;

                        b.iter(|| {
                            let mapped = (&tz).timestamp_opt(bb(timestamp), 0);
                            let zdt = mapped.single().unwrap();
                            assert_eq!(zdt.naive_local(), expected);
                        })
                    },
                );
            }
        }

        {
            let tz = tz_name.parse::<chrono_tz::Tz>().unwrap();
            let expected = chrono::NaiveDateTime::new(
                chrono::NaiveDate::from_ymd_opt(2024, 6, 30).unwrap(),
                chrono::NaiveTime::from_hms_opt(9, 46, 0).unwrap(),
            );

            c.bench_function(&format!("chrono/{NAME}-{tz_name}"), |b| {
                use chrono::TimeZone;

                b.iter(|| {
                    let mapped = tz.timestamp_opt(bb(timestamp), 0);
                    let zdt = mapped.single().unwrap();
                    assert_eq!(zdt.naive_local(), expected);
                })
            });
        }

        // The `time` crate doesn't support this.
    }

    define(c, "America/New_York", 1719755160);
    define(c, "Asia/Shanghai", 1719711960);
}

/// Benchmarks the conversion of an instant in time to a civil datetime
/// for a fixed offset. This operation might be commonly used in time
/// zones for which there is no DST. This is also generally a component of
/// `instant_to_civil_datetime_static`, since the first step there is to *find*
/// the offset and then convert it to a datetime. This benchmarks that second
/// step.
///
/// Also, the `time` crate can't do time zone name lookups, so we also include
/// this benchmark to incorporate it into some measurements for a similar task.
fn instant_to_civil_datetime_offset(c: &mut Criterion) {
    const NAME: &str = "instant_to_civil_datetime_offset";
    const OFFSET: i8 = -4;
    const STAMP: i64 = 1719755160;

    let expected = jiff::civil::date(2024, 6, 30).at(9, 46, 0, 0);
    let tz = jiff::tz::TimeZone::fixed(jiff::tz::offset(OFFSET));
    let ts = jiff::Timestamp::from_second(STAMP).unwrap();
    c.bench_function(&format!("jiff/{NAME}"), |b| {
        b.iter(|| {
            let zdt = bb(ts).to_zoned(bb(&tz).clone());
            assert_eq!(zdt.datetime(), expected);
        })
    });

    {
        use chrono::TimeZone;
        let expected = chrono::NaiveDateTime::new(
            chrono::NaiveDate::from_ymd_opt(2024, 6, 30).unwrap(),
            chrono::NaiveTime::from_hms_opt(9, 46, 0).unwrap(),
        );
        let tz = chrono::FixedOffset::east_opt(i32::from(OFFSET) * 60 * 60)
            .unwrap();
        c.bench_function(&format!("chrono/{NAME}"), |b| {
            b.iter(|| {
                let zdt = (&tz).timestamp_opt(STAMP, 0).single().unwrap();
                assert_eq!(zdt.naive_local(), expected);
            })
        });
    }

    {
        let expected = time::macros::datetime!(2024-06-30 09:46:00);
        let offset = time::UtcOffset::from_hms(OFFSET, 0, 0).unwrap();
        c.bench_function(&format!("time/{NAME}"), |b| {
            b.iter(|| {
                let zdt = time::OffsetDateTime::from_unix_timestamp(STAMP)
                    .unwrap()
                    .to_offset(offset);
                let dt = time::PrimitiveDateTime::new(zdt.date(), zdt.time());
                assert_eq!(dt, expected);
            })
        });
    }
}

/// This benchmarks the case where one already has a "zone aware" datetime,
/// and measures how long it takes to get a civil datetime.
///
/// For Jiff, a zone aware datetime is both an instant and a civil datetime,
/// so this operation is effectively free.
///
/// For Chrono, its zone aware datetime stores a civil datetime in UTC, so to
/// get the "local" civil time, some arithmetic on the UTC civil datetime needs
/// to be performed.
///
/// For `time`, its zone aware datetime stores a "local" civil datetime, so
/// this operation is effectively free.
fn offset_to_civil_datetime(c: &mut Criterion) {
    const NAME: &str = "offset_to_civil_datetime";
    const OFFSET: i8 = -4;
    const STAMP: i64 = 1719755160;

    let expected = jiff::civil::date(2024, 6, 30).at(9, 46, 0, 0);
    let tz = jiff::tz::TimeZone::fixed(jiff::tz::offset(OFFSET));
    let zdt = jiff::Timestamp::from_second(STAMP).unwrap().to_zoned(tz);
    c.bench_function(&format!("jiff/{NAME}"), |b| {
        b.iter(|| {
            assert_eq!(bb(&zdt).datetime(), expected);
        })
    });

    {
        use chrono::TimeZone;
        let expected = chrono::NaiveDateTime::new(
            chrono::NaiveDate::from_ymd_opt(2024, 6, 30).unwrap(),
            chrono::NaiveTime::from_hms_opt(9, 46, 0).unwrap(),
        );
        let tz = chrono::FixedOffset::east_opt(i32::from(OFFSET) * 60 * 60)
            .unwrap();
        let zdt = (&tz).timestamp_opt(STAMP, 0).single().unwrap();
        c.bench_function(&format!("chrono/{NAME}"), |b| {
            b.iter(|| {
                assert_eq!(bb(zdt).naive_local(), expected);
            })
        });
    }

    {
        let expected = time::macros::datetime!(2024-06-30 09:46:00);
        let offset = time::UtcOffset::from_hms(OFFSET, 0, 0).unwrap();
        let zdt = time::OffsetDateTime::from_unix_timestamp(STAMP)
            .unwrap()
            .to_offset(offset);
        c.bench_function(&format!("time/{NAME}"), |b| {
            b.iter(|| {
                let dt = time::PrimitiveDateTime::new(
                    bb(zdt.date()),
                    bb(zdt.time()),
                );
                assert_eq!(dt, expected);
            })
        });
    }
}

/// This benchmarks the time it takes to get a timestamp from a library's
/// zone-aware datetime type.
///
/// Jiff uses a timestamp internally, so this is effectively free.
///
/// Chrono and `time` both use civil datetimes internally, so they must do a
/// conversion step.
fn offset_to_timestamp(c: &mut Criterion) {
    const NAME: &str = "offset_to_timestamp";
    const OFFSET: i8 = -4;
    const STAMP: i64 = 1719755160;

    let tz = jiff::tz::TimeZone::fixed(jiff::tz::offset(OFFSET));
    let zdt = jiff::Timestamp::from_second(STAMP).unwrap().to_zoned(tz);
    c.bench_function(&format!("jiff/{NAME}"), |b| {
        b.iter(|| {
            assert_eq!(bb(&zdt).timestamp().as_second(), STAMP);
        })
    });

    {
        use chrono::TimeZone;

        let tz = chrono::FixedOffset::east_opt(i32::from(OFFSET) * 60 * 60)
            .unwrap();
        let zdt = (&tz).timestamp_opt(STAMP, 0).single().unwrap();
        c.bench_function(&format!("chrono/{NAME}"), |b| {
            b.iter(|| {
                assert_eq!(bb(zdt).timestamp(), STAMP);
            })
        });
    }

    {
        let offset = time::UtcOffset::from_hms(OFFSET, 0, 0).unwrap();
        let zdt = time::OffsetDateTime::from_unix_timestamp(STAMP)
            .unwrap()
            .to_offset(offset);
        c.bench_function(&format!("time/{NAME}"), |b| {
            b.iter(|| {
                assert_eq!(bb(zdt).unix_timestamp(), STAMP);
            })
        });
    }
}

/// Benchmarks how long it takes to add 2 hours 500 nanos to a timestamp.
fn timestamp_add_time_duration(c: &mut Criterion) {
    const NAME: &str = "timestamp_add_time";
    const STAMP: i128 = 1719755160_000_000_000;
    const EXPECTED: i128 = STAMP + (2 * 60 * 60 * 1_000_000_000) + 500;

    let expected = jiff::Timestamp::from_nanosecond(EXPECTED).unwrap();
    let start = jiff::Timestamp::from_nanosecond(STAMP).unwrap();

    let span = jiff::Span::new().hours(2).nanoseconds(500);
    c.bench_function(&format!("jiff/{NAME}_span"), |b| {
        b.iter(|| {
            let end = bb(&start).checked_add(bb(span)).unwrap();
            assert_eq!(end, expected);
        })
    });

    let duration = jiff::SignedDuration::new(2 * 60 * 60, 500);
    c.bench_function(&format!("jiff/{NAME}_duration"), |b| {
        b.iter(|| {
            let end = bb(&start).checked_add(bb(duration)).unwrap();
            assert_eq!(end, expected);
        })
    });
}

/// Benchmarks how long it takes to add 24 hours to a zone-aware datetime.
///
/// Note that we used a fixed offset as our time zone in order to accommodate
/// the lowest common denominator.
fn zoned_add_time_duration(c: &mut Criterion) {
    const NAME: &str = "zoned_add_time";
    const OFFSET: i8 = -4;
    const STAMP: i64 = 1719755160;
    const EXPECTED: i64 = STAMP + (24 * 60 * 60);

    let tz = jiff::tz::TimeZone::fixed(jiff::tz::offset(OFFSET));
    let expected =
        jiff::Timestamp::from_second(EXPECTED).unwrap().to_zoned(tz.clone());
    let start =
        jiff::Timestamp::from_second(STAMP).unwrap().to_zoned(tz.clone());
    let span = jiff::Span::new().hours(24);
    c.bench_function(&format!("jiff/{NAME}_span"), |b| {
        b.iter(|| {
            let end = bb(&start).checked_add(bb(span)).unwrap();
            assert_eq!(end, expected);
        })
    });
    let duration = jiff::SignedDuration::from_hours(24);
    c.bench_function(&format!("jiff/{NAME}_duration"), |b| {
        b.iter(|| {
            let end = bb(&start).checked_add(bb(duration)).unwrap();
            assert_eq!(end, expected);
        })
    });

    {
        use chrono::TimeZone;

        let tz = chrono::FixedOffset::east_opt(i32::from(OFFSET) * 60 * 60)
            .unwrap();
        let expected = (&tz).timestamp_opt(EXPECTED, 0).single().unwrap();
        let start = (&tz).timestamp_opt(STAMP, 0).single().unwrap();
        let delta = chrono::TimeDelta::hours(24);
        c.bench_function(&format!("chrono/{NAME}_duration"), |b| {
            b.iter(|| {
                let end = bb(start).checked_add_signed(bb(delta)).unwrap();
                assert_eq!(end, expected);
            })
        });
    }

    {
        let offset = time::UtcOffset::from_hms(OFFSET, 0, 0).unwrap();
        let expected = time::OffsetDateTime::from_unix_timestamp(EXPECTED)
            .unwrap()
            .to_offset(offset);
        let start = time::OffsetDateTime::from_unix_timestamp(STAMP)
            .unwrap()
            .to_offset(offset);
        let duration = time::Duration::hours(24);
        c.bench_function(&format!("time/{NAME}_duration"), |b| {
            b.iter(|| {
                let end = bb(start).checked_add(bb(duration)).unwrap();
                assert_eq!(end, expected);
            })
        });
    }
}

/// Benchmarks the amount of time it takes to parse a civil datetime.
fn parse_civil_datetime(c: &mut Criterion) {
    const NAME: &str = "parse_civil_datetime";
    const STRING: &str = "2024-06-30T09:46:00";

    let expected = jiff::civil::date(2024, 6, 30).at(9, 46, 0, 0);
    c.bench_function(&format!("jiff/{NAME}"), |b| {
        b.iter(|| {
            let dt: jiff::civil::DateTime = bb(STRING).parse().unwrap();
            assert_eq!(dt, expected);
        })
    });

    let expected = chrono::NaiveDateTime::new(
        chrono::NaiveDate::from_ymd_opt(2024, 6, 30).unwrap(),
        chrono::NaiveTime::from_hms_opt(9, 46, 0).unwrap(),
    );
    c.bench_function(&format!("chrono/{NAME}"), |b| {
        b.iter(|| {
            let dt: chrono::NaiveDateTime = bb(STRING).parse().unwrap();
            assert_eq!(dt, expected);
        })
    });

    let expected = time::macros::datetime!(2024-06-30 09:46:00);
    c.bench_function(&format!("time/{NAME}"), |b| {
        b.iter(|| {
            let dt = time::PrimitiveDateTime::parse(
                bb(STRING),
                &time::format_description::well_known::Iso8601::DEFAULT,
            )
            .unwrap();
            assert_eq!(dt, expected);
        })
    });
}

/// Benchmarks the amount of time it takes to print a civil datetime.
///
/// This attempts to use the fastest possible API for the corresponding crate.
fn print_civil_datetime(c: &mut Criterion) {
    const NAME: &str = "print_civil_datetime";
    const EXPECTED: &str = "2024-06-30T09:46:00";

    let dt = jiff::civil::date(2024, 6, 30).at(9, 46, 0, 0);
    let mut buf = String::new();
    c.bench_function(&format!("jiff/{NAME}"), |b| {
        b.iter(|| {
            static PRINTER: jiff::fmt::temporal::DateTimePrinter =
                jiff::fmt::temporal::DateTimePrinter::new();
            buf.clear();
            PRINTER.print_datetime(bb(&dt), &mut buf).unwrap();
            assert_eq!(buf, EXPECTED);
        })
    });
}

/// Benchmarks the amount of time it takes to parse an RFC 2822 datetime as a
/// timestamp.
fn parse_rfc2822(c: &mut Criterion) {
    const NAME: &str = "parse_rfc2822";
    const STRING: &str = "Sat, 13 Jul 2024 17:24:59 -0400";

    let expected: jiff::Timestamp = "2024-07-13T21:24:59Z".parse().unwrap();
    c.bench_function(&format!("jiff/{NAME}"), |b| {
        b.iter(|| {
            let ts = jiff::fmt::rfc2822::DateTimeParser::new()
                .parse_timestamp(bb(STRING))
                .unwrap();
            assert_eq!(ts, expected);
        })
    });

    {
        use chrono::TimeZone;

        let expected =
            chrono::Utc.with_ymd_and_hms(2024, 7, 13, 21, 24, 59).unwrap();
        c.bench_function(&format!("chrono/{NAME}"), |b| {
            b.iter(|| {
                let dt =
                    chrono::DateTime::parse_from_rfc2822(bb(STRING)).unwrap();
                assert_eq!(dt, expected);
            })
        });
    }

    let expected = time::macros::datetime!(2024-07-13 21:24:59 UTC);
    c.bench_function(&format!("time/{NAME}"), |b| {
        b.iter(|| {
            let odt = time::OffsetDateTime::parse(
                bb(STRING),
                &time::format_description::well_known::Rfc2822,
            )
            .unwrap();
            assert_eq!(odt, expected);
        })
    });
}

/// Benchmarks the amount of time it takes to parse via a `strptime` format
/// string into a timestamp.
fn parse_strptime(c: &mut Criterion) {
    const NAME: &str = "parse_strptime";
    const STRING: &str = "Mon Jul 15 04:24:59 PM -0400 2024";
    const FMT: &str = "%a %b %e %I:%M:%S %p %z %Y";
    // `time` doesn't have strtime-like APIs, but does provide its own
    // custom formatting machinery. So we just use that since it's solving
    // roughly the same problem as strptime.
    const TIME_FMT: &[time::format_description::BorrowedFormatItem] = time::macros::format_description!(
        "[weekday repr:short case_sensitive:false] \
         [month repr:short case_sensitive:false] \
         [day] \
         [hour repr:12]:[minute]:[second] \
         [period] \
         [offset_hour sign:mandatory][offset_minute] \
         [year]"
    );

    let expected: jiff::Timestamp = "2024-07-15T20:24:59Z".parse().unwrap();
    c.bench_function(&format!("jiff/{NAME}"), |b| {
        b.iter(|| {
            let ts = jiff::Timestamp::strptime(bb(FMT), bb(STRING)).unwrap();
            assert_eq!(ts, expected);
        })
    });

    {
        use chrono::TimeZone;

        let expected = chrono::Utc
            .with_ymd_and_hms(2024, 7, 15, 20, 24, 59)
            .unwrap()
            .timestamp();
        c.bench_function(&format!("chrono/{NAME}"), |b| {
            b.iter(|| {
                let dt = chrono::DateTime::parse_from_str(bb(STRING), bb(FMT))
                    .unwrap();
                assert_eq!(dt.timestamp(), expected);
            })
        });
    }

    {
        use chrono::TimeZone;

        let expected =
            chrono::Utc.with_ymd_and_hms(2024, 7, 15, 20, 24, 59).unwrap();
        let items =
            chrono::format::strftime::StrftimeItems::new(FMT).parse().unwrap();
        c.bench_function(&format!("chrono-amortize/{NAME}"), |b| {
            b.iter(|| {
                let mut parsed = chrono::format::Parsed::new();
                chrono::format::parse(
                    &mut parsed,
                    bb(STRING),
                    items.as_slice().iter(),
                )
                .unwrap();
                let dt = parsed.to_datetime().unwrap();
                assert_eq!(dt, expected);
            })
        });
    }

    let expected = time::macros::datetime!(2024-07-15 20:24:59 UTC);
    c.bench_function(&format!("time/{NAME}"), |b| {
        b.iter(|| {
            let odt =
                time::OffsetDateTime::parse(bb(STRING), &TIME_FMT).unwrap();
            assert_eq!(odt, expected);
        })
    });
}

/// Benchmarks parsing a "friendly" or "human" duration. We compare Jiff with
/// `humantime`.
fn parse_friendly(c: &mut Criterion) {
    use jiff::{SignedDuration, ToSpan};
    use std::time::Duration;

    const NAME: &str = "parse_friendly";
    const TINY: &str = "2s";
    const SHORT: &str = "2h30m";
    const MEDIUM: &str = "2d5h30m";
    const LONG_JIFF: &str = "2y1mo15d5h59m1s";
    const LONG_HUMANTIME: &str = "2y1M15d5h59m1s";
    const LONGER: &str = "2 years 1 month 15 days 5 hours 59 minutes 1 second";
    const LONGEST: &str = "\
        2 years 1 month 15 days \
        5 hours 59 minutes 1 second \
        123 millis 456 usec 789 nanos\
    ";
    // The longest duration parsable by Jiff and humantime that doesn't involve
    // units whose duration can change. This lets us benchmark parsing into a
    // `SignedDuration`, which is more of an apples-to-apples comparison to
    // humantime.
    const LONGEST_TIME: &str = "\
        5 hours 59 minutes 1 second \
        123 millis 456 usec 789 nanos\
    ";

    let benches = [
        ("tiny", TINY, 2.seconds()),
        ("short", SHORT, 2.hours().minutes(30)),
        ("medium", MEDIUM, 2.days().hours(5).minutes(30)),
        (
            "long",
            LONG_JIFF,
            2.years().months(1).days(15).hours(5).minutes(59).seconds(1),
        ),
        (
            "longer",
            LONGER,
            2.years().months(1).days(15).hours(5).minutes(59).seconds(1),
        ),
        (
            "longest",
            LONGEST,
            2.years()
                .months(1)
                .days(15)
                .hours(5)
                .minutes(59)
                .seconds(1)
                .milliseconds(123)
                .microseconds(456)
                .nanoseconds(789),
        ),
        (
            "longest-time",
            LONGEST_TIME,
            5.hours()
                .minutes(59)
                .seconds(1)
                .milliseconds(123)
                .microseconds(456)
                .nanoseconds(789),
        ),
    ];
    for (kind, input, expected) in benches {
        c.bench_function(&format!("jiff-span/{NAME}/{kind}"), |b| {
            b.iter(|| {
                let got: jiff::Span = input.parse().unwrap();
                assert_eq!(got, expected);
            })
        });
    }

    let benches = [
        ("tiny", TINY, SignedDuration::new(2, 0)),
        ("short", SHORT, SignedDuration::new(2 * 60 * 60 + 30 * 60, 0)),
        (
            "longest-time",
            LONGEST_TIME,
            SignedDuration::new(5 * 3600 + 59 * 60 + 1, 123_456_789),
        ),
    ];
    for (kind, input, expected) in benches {
        c.bench_function(&format!("jiff-duration/{NAME}/{kind}"), |b| {
            b.iter(|| {
                let got: jiff::SignedDuration = input.parse().unwrap();
                assert_eq!(got, expected);
            })
        });
    }

    let benches = [
        ("tiny", TINY, Duration::new(2, 0)),
        ("short", SHORT, Duration::new(2 * 60 * 60 + 30 * 60, 0)),
        (
            "medium",
            MEDIUM,
            Duration::new(2 * 24 * 60 * 60 + 5 * 60 * 60 + 30 * 60, 0),
        ),
        (
            "long",
            LONG_HUMANTIME,
            // humantime uses a fixed number of seconds to represent years
            // and months. That is, 365.25d and 30.44d, respectively, where
            // a day is 86400 seconds.
            Duration::new(
                2 * 31_557_600
                    + 1 * 2_630_016
                    + 15 * 86400
                    + 5 * 3600
                    + 59 * 60
                    + 1,
                0,
            ),
        ),
        (
            "longer",
            LONGER,
            // humantime uses a fixed number of seconds to represent years
            // and months. That is, 365.25d and 30.44d, respectively, where
            // a day is 86400 seconds.
            Duration::new(
                2 * 31_557_600
                    + 1 * 2_630_016
                    + 15 * 86400
                    + 5 * 3600
                    + 59 * 60
                    + 1,
                0,
            ),
        ),
        (
            "longest",
            LONGEST,
            // humantime uses a fixed number of seconds to represent years
            // and months. That is, 365.25d and 30.44d, respectively, where
            // a day is 86400 seconds.
            Duration::new(
                2 * 31_557_600
                    + 1 * 2_630_016
                    + 15 * 86400
                    + 5 * 3600
                    + 59 * 60
                    + 1,
                123_456_789,
            ),
        ),
        (
            "longest-time",
            LONGEST_TIME,
            Duration::new(5 * 3600 + 59 * 60 + 1, 123_456_789),
        ),
    ];
    for (kind, input, expected) in benches {
        c.bench_function(&format!("humantime/{NAME}/{kind}"), |b| {
            b.iter(|| {
                let got = humantime::parse_duration(input).unwrap();
                assert_eq!(got, expected);
            })
        });
    }
}

criterion::criterion_group!(
    benches,
    civil_datetime_to_instant_with_tzdb_lookup,
    civil_datetime_to_instant_static,
    instant_to_civil_datetime_static,
    instant_to_civil_datetime_offset,
    offset_to_civil_datetime,
    offset_to_timestamp,
    timestamp_add_time_duration,
    zoned_add_time_duration,
    parse_civil_datetime,
    parse_rfc2822,
    parse_strptime,
    print_civil_datetime,
    parse_friendly,
);
criterion::criterion_main!(benches);
