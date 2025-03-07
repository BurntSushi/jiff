# Chapter 1

Hello, world!

```rust
use jiff::Timestamp;

static TZ: jiff::tz::TimeZone = jiff::tz::get!("America/New_York");

# let zdt = Timestamp::UNIX_EPOCH.in_tz("America/New_York")?;
let zdt = Timestamp::UNIX_EPOCH.to_zoned(TZ.clone());
assert_eq!(zdt.to_string(), "1969-12-31T19:00:00-05:00[America/New_York]");
# Ok::<(), Box<dyn std::error::Error>>(())
```

A Jiff [`TimeZone`] can be fixed, POSIX
or TZif. It is found in the [`jiff::tz`] module. You can use
[`jiff::tz::TimeZone::try_system`] to get the system time zone.

Here's a [`time::PrimitiveDateTime`] link for you too.

And here is a [`jiff::ToSpan::years`] trait method link.

[`TimeZone`]: jiff::tz::TimeZone
