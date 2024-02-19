/*!
This example demonstrates how to find the boot time of your Unix system by
parsing the output of `uptime`. While there are assuredly better ways to find
the precise boot time of your machine, this nevertheless serves as a nice
example.

Because `uptime` only reports the current clock hour and minute, it's possible
that the date has changed since `uptime` was run. If that happens, this program
will report an incorrect start time. Therefore, this program assumes that the
current calendar date is the same as the calendar date on which the `uptime`
command was executed.

Otherwise, this program demonstrates parsing a partial datetime and a bespoke
duration via a regex and loading it into Jiff data types. And then determining
the current time zone aware datetime as known by `uptime`, subtracting the
duration and the finally rounding the zoned datetime to the desired precision.
We do the final rounding step because `uptime` doesn't report its duration in
a granularity smaller than minutes. So it's "odd" to report a boot time with
second (or less) precision.
*/

use std::io::Write;

use anyhow::Context;
use jiff::{Span, Unit, Zoned};
use regex_lite::Regex;

fn main() -> anyhow::Result<()> {
    let up = UptimeDuration::find()?;
    let now = Zoned::now().with().hour(up.hour).minute(up.minute).build()?;
    let span = Span::new()
        .try_days(up.days)?
        .try_hours(up.hours)?
        .try_minutes(up.minutes)?;
    let booted = now.checked_sub(span)?.round(Unit::Minute)?;
    writeln!(&mut std::io::stdout(), "{booted}")?;
    Ok(())
}

struct UptimeDuration {
    // uptime reports the current hour/minute
    hour: i8,
    minute: i8,
    // uptime reports duration in days, hours and minutes
    days: i32,
    hours: i32,
    minutes: i64,
}

impl UptimeDuration {
    /// Parse the current clock time and duration of uptime from stdin.
    ///
    /// This assumes the output of `uptime` is on stdin.
    fn find() -> anyhow::Result<UptimeDuration> {
        let re = Regex::new(
            r"(\d+):(\d+)(?::\d+)?\s+up\s+(\d+)\s+days,\s+(\d+):(\d+)",
        )
        .unwrap();
        for result in std::io::stdin().lines() {
            let line = result?;
            let Some(caps) = re.captures(&line) else { continue };
            let (_, [hour, minute, days, hours, minutes]) = caps.extract();
            let hour: i8 = hour.parse().with_context(|| {
                format!("failed to parse current hour integer '{hour}'")
            })?;
            let minute: i8 = minute.parse().with_context(|| {
                format!("failed to parse current minute integer '{minute}'")
            })?;
            let days: i32 = days
                .parse()
                .with_context(|| format!("failed to parse days '{days}'"))?;
            let hours: i32 = hours
                .parse()
                .with_context(|| format!("failed to parse hours '{hours}'"))?;
            let minutes: i64 = minutes.parse().with_context(|| {
                format!("failed to parse minutes '{minutes}'")
            })?;
            return Ok(UptimeDuration { hour, minute, days, hours, minutes });
        }
        anyhow::bail!("could not find uptime duration on stdin")
    }
}
