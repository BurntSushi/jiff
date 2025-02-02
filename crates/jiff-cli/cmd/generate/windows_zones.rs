/*!
A command for generating Rust source files from a `windowsZones.xml` file.

The time zone situation on Windows is pretty precarious. And for a long time,
Windows had no real way of getting the current IANA Time Zone Database name.
Instead, folks (like ICU) used [GetDynamicTimeZoneInformation] to get the
"Windows" name of a time zone, and then map it to an IANA name courtesy of
[CLDR XML data].

This is the approach Jiff currently uses, since it seems to be the one most
commonly employed by battle tested libraries, and probably also enjoys the
broadest support.

However, it does seem that as of Windows ~10, [WinRT GetTimeZone] provides a
way to get the actual IANA Time Zone Database name. I don't understand enough
about Windows to even know what WinRT means or why getting a time zone requires
using it, but using WinRT seems to require a whole bunch of FFI soup to do it.

I don't yet understand the trade offs between these approaches, so I'm going
with the one that most everyone else seems to use. (Go, Chrono and ICU, at
least.)

Note that we don't use anything else from Windows. We don't use its time zone
transition API for example. We still rely on the IANA Time Zone Database for
that. (Which is usually bundled into Jiff on Windows.)

[GetDynamicTimeZoneInformation]: https://learn.microsoft.com/en-us/windows/win32/api/timezoneapi/nf-timezoneapi-getdynamictimezoneinformation
[CLDR XML data]: https://github.com/unicode-org/cldr/raw/main/common/supplemental/windowsZones.xml
[WinRT GetTimeZone]: https://learn.microsoft.com/en-us/uwp/api/windows.globalization.calendar.gettimezone?view=winrt-22621
*/

use std::{
    collections::BTreeMap,
    fs::File,
    io::{BufWriter, Write},
    path::{Path, PathBuf},
};

use anyhow::Context;
use lexopt::{Arg, Parser};
use regex_lite::Regex;

use crate::args::{self, Usage};

const USAGE: &'static str = r#"
Generate Rust source code from a windowsZones.xml file.

USAGE:
    jiff-cli generate windows-zones <path/to/windowsZones.xml> [<jiff-dir>]

This command generates the requisite Rust source code for mapping from Windows
own custom time zone names to IANA time zone names.

This program should be run from the root of the Jiff repository. Alternatively,
provide a path to the root of the Jiff repository as a second positional
argument.
"#;

pub fn run(p: &mut Parser) -> anyhow::Result<()> {
    let mut config = Config::default();
    args::configure(p, USAGE, &mut [&mut config])?;

    let windows_zones = config.windows_zones()?;
    let jiff = config.jiff();

    let xml = std::fs::read_to_string(windows_zones).with_context(|| {
        format!("failed to read string from {}", windows_zones.display())
    })?;

    let re_version =
        Regex::new(r#"<mapTimezones.*typeVersion="([^"]+)">"#).unwrap();
    let caps = re_version.captures(&xml).context("failed to parse version")?;
    let (_, [version]) = caps.extract();

    // Yeah, that's right, I'm parsing XML with regex. Just watch me.
    let re_tzmap = Regex::new(
        r#"<mapZone other="([^"]+)" territory="001" type="([^"]+)"#,
    )
    .unwrap();
    let mut map: BTreeMap<String, Mapping> = BTreeMap::new();
    for (_, [win, iana]) in re_tzmap.captures_iter(&xml).map(|c| c.extract()) {
        let win_lower = win.to_ascii_lowercase();
        let mapping =
            Mapping { windows: win.to_string(), iana: iana.to_string() };
        anyhow::ensure!(
            map.insert(win_lower, mapping).is_none(),
            "found duplicate Windows time zone name {win}",
        );
    }

    let mapping_path = jiff.join("src/tz/system/windows/windows_zones.rs");
    write_mappings(&mapping_path, version, &map).with_context(|| {
        format!(
            "failed to write Windows time zone mappings to {}",
            mapping_path.display()
        )
    })?;

    Ok(())
}

#[derive(Debug)]
struct Mapping {
    windows: String,
    iana: String,
}

#[derive(Debug)]
struct Config {
    windows_zones: Option<PathBuf>,
    jiff: Option<PathBuf>,
    verbose: bool,
}

impl Config {
    fn windows_zones(&self) -> anyhow::Result<&Path> {
        self.windows_zones
            .as_deref()
            .context("missing path to windowsZones.xml file")
    }

    fn jiff(&self) -> &Path {
        self.jiff.as_deref().unwrap_or_else(|| Path::new("./"))
    }
}

impl Default for Config {
    fn default() -> Config {
        Config { windows_zones: None, jiff: None, verbose: false }
    }
}

impl args::Configurable for Config {
    fn configure(
        &mut self,
        _: &mut Parser,
        arg: &mut Arg,
    ) -> anyhow::Result<bool> {
        match *arg {
            Arg::Short('v') | Arg::Long("verbose") => {
                self.verbose = true;
            }
            Arg::Value(ref mut value) => {
                if self.windows_zones.is_none() {
                    let path = PathBuf::from(std::mem::take(value));
                    self.windows_zones = Some(path);
                } else if self.jiff.is_none() {
                    let path = PathBuf::from(std::mem::take(value));
                    self.jiff = Some(path);
                } else {
                    return Ok(false);
                }
            }
            _ => return Ok(false),
        }
        Ok(true)
    }

    fn usage(&self) -> &[Usage] {
        const USAGES: &'static [Usage] = &[Usage::new(
            "-v, --verbose",
            "Add more output.",
            r#"
This is a generic flag that expands output beyond the "normal" amount. Which
output is added depends on the command.
"#,
        )];
        USAGES
    }
}

fn write_mappings(
    path: &Path,
    version: &str,
    mappings: &BTreeMap<String, Mapping>,
) -> anyhow::Result<()> {
    let mut out = BufWriter::new(File::create(path)?);
    writeln!(out, r#"pub(super) static VERSION: &str = r"{version}";"#)?;
    writeln!(out, "")?;
    writeln!(out, "pub(super) static WINDOWS_TO_IANA: &[(&str, &str)] = &[")?;
    for (_, mapping) in mappings {
        let Mapping { windows, iana } = mapping;
        writeln!(out, r#"    (r"{windows}", r"{iana}"),"#).with_context(
            || format!("failed to write windows time zone map for {windows}"),
        )?;
    }
    writeln!(out, "];")?;
    out.flush()?;
    Ok(())
}
