/*!
A command for generating Rust source files from a zoneinfo directory.

This walks the directory tree given and looks for valid TZif data files. All
found files are concatenated into a single file, with the offset and the
corresponding time zone name recorded for the start of each file. In this way,
we can ship one binary file.
*/

use std::{
    collections::BTreeMap,
    fs::File,
    io::{BufWriter, Read, Seek, Write},
    ops::Range,
    path::{Path, PathBuf},
};

use anyhow::Context;
use jiff::tz::TimeZone;
use lexopt::{Arg, Parser};

use crate::args::{self, Usage};

const USAGE: &'static str = r#"
Generate Rust source code from a zoneinfo directory.

USAGE:
    jiff-cli generate jiff-tzdb <zoneinfo-dir> [<jiff-tzdb-dir>]

This program should be run from the root of the Jiff repository. Namely, it
assumes that `./crates/jiff-tzdb` exists and corresponds to the `jiff-tzdb`
crate.

While you can run this program using your system's zoneinfo directory, it is
recommended to generate your own zoneinfo directory via
`jiff-cli generate zoneinfo`. There are two main reasons for this:

1. Your system zoneinfo directory may be using "fat" TZif files, which will
make the binary size of `jiff-tzdb` bigger than it needs to be. Jiff works just
fine with the "slim" TZif files.
2. Your system zoneinfo directory may not have the version of the tzdata files
anywhere. While the version isn't strictly required, we put it into the crate
for diagnostic purposes. The `jiff-cli generate zoneinfo` command will do this
for you.
"#;

pub fn run(p: &mut Parser) -> anyhow::Result<()> {
    let mut config = Config::default();
    args::configure(p, USAGE, &mut [&mut config])?;

    let zoneinfo = config.zoneinfo()?;
    let jiff_tzdb = config.jiff_tzdb();

    let dat_path = jiff_tzdb.join("concatenated-zoneinfo.dat");
    let mut dat_file =
        BufWriter::new(File::create(&dat_path).with_context(|| {
            format!("failed to create {}", dat_path.display())
        })?);

    let mut buf = vec![];
    let mut offset: u32 = 0;
    // Map from ASCII lowercase TZ name to
    // (canonical name, offset range into dat).
    let mut tzname_to_range: BTreeMap<String, (String, Range<u32>)> =
        BTreeMap::new();
    for result in walkdir::WalkDir::new(zoneinfo).sort_by_file_name() {
        let dent = result.with_context(|| {
            format!(
                "directory traversal of {zoneinfo} failed",
                zoneinfo = zoneinfo.display()
            )
        })?;
        if dent.file_type().is_dir() {
            continue;
        }

        let path = dent.path();
        let mut file = File::open(path).with_context(|| {
            format!("failed to open {path}", path = path.display())
        })?;

        // This probably isn't necessary, but read the first 4 bytes to do a
        // quick check as to whether this is actually a TZif file or not. We
        // could probably just read everything into memory and we'd be fine,
        // but this seems like "good sense."
        let mut header = [0; 4];
        file.read_exact(&mut header).with_context(|| {
            format!(
                "failed to reader header from {path}",
                path = path.display()
            )
        })?;
        if !is_possibly_tzif(&header) {
            if config.verbose {
                eprintln!(
                    "skipping {path} since it isn't TZif",
                    path = path.display()
                );
            }
            continue;
        }
        file.rewind().with_context(|| {
            format!("failed to rewind {path}", path = path.display())
        })?;

        // OK, now that we have a TZif file, read everything into memory and
        // parse it. We don't actually do anything with the parsed `TimeZone`,
        // but we create one in order to verify that Jiff can parse it.
        buf.clear();
        file.read_to_end(&mut buf).with_context(|| {
            format!(
                "failed to read all data from {path}",
                path = path.display()
            )
        })?;
        let len = u32::try_from(buf.len()).with_context(|| {
            format!("could not convert buffer length {} to u32", buf.len())
        })?;

        let tzname = path.strip_prefix(zoneinfo).with_context(|| {
            format!(
                "failed to strip prefix '{zoneinfo}' from '{path}'",
                zoneinfo = zoneinfo.display(),
                path = path.display()
            )
        })?;
        let tzname = tzname.to_str().with_context(|| {
            format!("time zone name '{tzname:?}' is not valid UTF-8")
        })?;
        let tz = TimeZone::tzif(tzname, &buf).with_context(|| {
            format!(
                "failed to parse TZif data from {path}",
                path = path.display()
            )
        })?;
        let iana_name = tz.iana_name().expect("IANA time zone").to_string();
        assert_eq!(tzname, iana_name);

        let offset_end = offset.checked_add(len).with_context(|| {
            format!(
                "adding offset {offset} to TZif data length {len} \
                 resulted in overflow while handling time zone {tzname}",
            )
        })?;
        let iana_name_lower = iana_name.to_ascii_lowercase();
        if tzname_to_range
            .insert(iana_name_lower, (iana_name, offset..offset_end))
            .is_some()
        {
            anyhow::bail!(
                "found duplicate TZif file for time zone {tzname} \
                 at file {path}",
                path = path.display(),
            );
        }
        offset = offset_end;

        dat_file.write_all(&buf).with_context(|| {
            format!(
                "failed to write TZif data for '{tzname}' to {}",
                dat_path.display()
            )
        })?;
    }
    dat_file
        .flush()
        .with_context(|| format!("failed to flush {}", dat_path.display()))?;

    let version_path = zoneinfo.join("version");
    let version = match std::fs::read_to_string(&version_path) {
        Ok(version) => Some(version.trim().to_string()),
        Err(err) => {
            if config.verbose {
                eprintln!(
                    "failed to read version from {}: {err}",
                    version_path.display()
                )
            }
            None
        }
    };

    let tzname_path = jiff_tzdb.join("tzname.rs");
    write_tzname_offsets(&tzname_path, version, &tzname_to_range)
        .with_context(|| {
            format!(
                "failed to write time zone offset data to {}",
                tzname_path.display()
            )
        })?;
    super::rustfmt(&tzname_path)?;

    Ok(())
}

#[derive(Debug)]
struct Config {
    zoneinfo: Option<PathBuf>,
    jiff_tzdb: Option<PathBuf>,
    verbose: bool,
}

impl Config {
    fn zoneinfo(&self) -> anyhow::Result<&Path> {
        self.zoneinfo.as_deref().context("missing path to zoneinfo directory")
    }

    fn jiff_tzdb(&self) -> &Path {
        self.jiff_tzdb
            .as_deref()
            .unwrap_or_else(|| Path::new("./crates/jiff-tzdb"))
    }
}

impl Default for Config {
    fn default() -> Config {
        Config { zoneinfo: None, jiff_tzdb: None, verbose: false }
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
                if self.zoneinfo.is_none() {
                    let path = PathBuf::from(std::mem::take(value));
                    self.zoneinfo = Some(path);
                } else if self.jiff_tzdb.is_none() {
                    let path = PathBuf::from(std::mem::take(value));
                    self.jiff_tzdb = Some(path);
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

fn write_tzname_offsets(
    path: &Path,
    version: Option<String>,
    tzname_to_range: &BTreeMap<String, (String, Range<u32>)>,
) -> anyhow::Result<()> {
    let mut out = BufWriter::new(File::create(path)?);
    writeln!(
        out,
        "pub(super) static VERSION: Option<&str> = {};",
        version.map(|v| format!(r#"Some(r"{v}")"#)).unwrap_or("None".into())
    )?;
    writeln!(out, "")?;
    writeln!(
        out,
        "pub(super) static TZNAME_TO_OFFSET: &[(&str, core::ops::Range<usize>)] = &["
    )?;
    for (_, (tzname, range)) in tzname_to_range {
        // There are two technically possible issues here.
        //
        // Firstly, `tzname` could contain `"##`, which would make it an
        // invalid literal. But in practice, this can't really happen. And if
        // it does, the Rust program won't be valid and we can just fix the
        // bug in this code generator.
        //
        // Secondly, the offset in theory could be too big to fit into a usize.
        // The offset calculation ensure the offset fits into 32-bits, so the
        // only way this could fail is on a 16-bit system. But, at time of
        // writing, Jiff specifically fails to compile on a 16-bit system. So
        // there's no need to worry about that yet. (And it will be a problem,
        // because the offsets exceed 2^16.)
        let Range { start, end } = range;
        writeln!(out, r#"    (r"{tzname}", {start}..{end}),"#).with_context(
            || format!("failed to write time zone offset for {tzname}"),
        )?;
    }
    writeln!(out, "];")?;
    out.flush()?;
    Ok(())
}

/// Does a quick check that returns true if the data might be in TZif format.
///
/// It is possible that this returns true even if the given data is not in TZif
/// format. However, it is impossible for this to return false when the given
/// data is TZif. That is, a false positive is allowed but a false negative is
/// not.
fn is_possibly_tzif(data: &[u8]) -> bool {
    data.starts_with(b"TZif")
}
