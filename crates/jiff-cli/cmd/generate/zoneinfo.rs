/*!
A wrapper around `zic` to generate binary TZif data for `jiff-tzdb`.

It would be nice to abandon using `zic` entirely in favor of our own compiler.
A substantial part of this is done in `jiff/src/tz/zic.rs` in the form of a
complete parser for the zic input format. However, what remains is the actual
conversion step from the data into time zone transition rules. This was
non-trivial enough that I gave up, but it would be very nice to have that
working. From there, we could use it to generate the TZif files themselves.
And at that point, we wouldn't need `zic` any more.
*/

use std::{
    fs::File,
    path::{Path, PathBuf},
    process::Command,
};

use anyhow::Context;
use bstr::ByteSlice;
use lexopt::{Arg, Parser};

use crate::args::{self, Usage};

const USAGE: &'static str = r#"
Generate TZif data for the jiff-tzdb crate.

USAGE:
    jiff-cli generate zoneinfo <tzdata-path> <output-directory>

The output of this program is a directory like `/usr/share/zoneinfo` on most
Linux distributions. This output can then be used as an input to
`jiff-cli generate jiff-tzdb` to generate the actual Rust source code for
the `jiff-tzdb` crate. The purpose of this command is to centralize the
configuration used to build the binary data for the `jiff-tzdb` crate.

Here's an example usage from the root of this repository. If you already
have `zic` installed on your system (the tzdata compiler), then you can just
download and extract the tzdata files:

    mkdir tzdata2024a
    cd tzdata2024a
    curl -LO 'https://data.iana.org/time-zones/releases/tzdata2024a.tar.gz'
    tar xf tzdata2024a.tar.gz

If your system doesn't have `zic`, then you can download the complete tzdb
release (which includes both the code for `zic` and the tzdata files). You may
also need to do this step if the tzdata format changes and the copy of `zic`
on your system is too old to read the latest tzdata files.

    curl -LO 'https://data.iana.org/time-zones/releases/tzdb-2024a.tar.lz'
    tar xf tzdb-2024a.tar.lz
    cd tzdb-2024a

And then build the `zic` compiler:

    make

This should drop a `zic` program in the current directory. You'll then want to
pass the path to this `zic` program via the `--zic` flag to
`jiff-cli generate zoneinfo`. The `zic` program is responsible for transforming
tzdata files (like `northamerica`) into the binary TZif files typically found
in `/usr/share/zoneinfo`.

Then, run:

    jiff-cli generate zoneinfo path/to/tzdata2024a /tmp/zoneinfo-2024a

If you want to re-generate the Rust code for jiff-tzdb, then from the root of
this repository, you'd do:

    jiff-cli generate jiff-tzdb /tmp/zoneinfo-2024a
"#;

static TZDATA_FILES: &[&str] = &[
    "africa",
    "antarctica",
    "asia",
    "australasia",
    "europe",
    "northamerica",
    "southamerica",
    "etcetera",
    "backward",
    "factory",
];

pub fn run(p: &mut Parser) -> anyhow::Result<()> {
    let mut config = Config::default();
    args::configure(p, USAGE, &mut [&mut config])?;

    let tzdata = config.tzdata()?;
    let outdir = config.outdir()?;
    let zic = config.zic();

    // Check that the zic program is available and emit its version to stderr.
    // We do this even if verbose is disabled as a sanity check to ensure that
    // `zic` itself is runnable.
    let mut cmd = Command::new(zic);
    cmd.arg("--version");
    let output =
        cmd.output().with_context(|| format!("failed to run `{cmd:?}`"))?;
    if config.verbose {
        eprintln!("zic --version output: {}", output.stdout.trim().as_bstr());
    }

    // Create the output directory if it doesn't exist.
    std::fs::create_dir_all(outdir).with_context(|| {
        format!("failed to create output directory {}", outdir.display())
    })?;

    // Write the version to our output directory. Unfortunately, this isn't
    // standard for zoneinfo directories, which means `jiff-cli generate
    // jiff-tzdb` can't rely on this being here. But it will notice it when it
    // exists and add it to the crate data.
    let (src, dst) = (tzdata.join("version"), outdir.join("version"));
    std::fs::copy(&src, &dst).with_context(|| {
        format!(
            "failed to copy {src} to {dst}",
            src = src.display(),
            dst = dst.display()
        )
    })?;

    // Generate "rearguard" data. tzdb has this to say about it:
    //
    // > The build procedure constructs three files vanguard.zi, main.zi,
    // > and rearguard.zi, one for each format. Although the files represent
    // > essentially the same data, they may have minor discrepancies that
    // > users are not likely to notice. The files are intended for downstream
    // > data consumers and are not installed. Zoneinfo parsers that do not
    // > support negative SAVE values should start using rearguard.zi, so that
    // > they will be unaffected when the negative-DST feature moves from
    // > vanguard to main. Bleeding-edge Zoneinfo parsers that support the new
    // > features already can use vanguard.zi; in this respect, current tzcode
    // > is bleeding-edge.
    //
    // In effect, rearguard data doesn't use negative DST offsets, which are
    // somewhat odd given that the concept of "daylight saving time" involves
    // moving the clocks forward _to add more daylight_ to the typical waking
    // hours of the day. So we specifically stick to rearguard data so that
    // DST is more accurately modeled. The IANA release distribution provides
    // this via an `awk` script that transforms the standard "main" zi data.
    let mut cmd = Command::new("awk");
    cmd.args(["-v", "DATAFORM=rearguard", "-f"])
        .arg(tzdata.join("ziguard.awk"));
    for tzdata_file in TZDATA_FILES {
        cmd.arg(tzdata.join(tzdata_file));
    }
    let rearguard_path = outdir.join("rearguard.zi");
    let rearguard = File::create(&rearguard_path).with_context(|| {
        format!("failed to create `{}`", rearguard_path.display())
    })?;
    cmd.stdout(rearguard);
    let status =
        cmd.status().with_context(|| format!("failed to run `{cmd:?}`"))?;
    anyhow::ensure!(
        status.success(),
        "running `{cmd:?}` failed with status {status}"
    );

    // Run the zic compiler.
    let mut cmd = Command::new(zic);
    if config.verbose {
        cmd.arg("-v");
    }
    // AFAIK, there is no reason to use `-b fat` other than for code that can't
    // deal with the slim format. But Jiff can just fine. From what I can tell,
    // the main difference is that the `fat` format emits transitions that are
    // redundant with the POSIX TZ strings for that time zone.
    cmd.arg("-b").arg("slim");
    cmd.arg("-d").arg(outdir);
    cmd.arg(&rearguard_path);
    let status =
        cmd.status().with_context(|| format!("failed to run `{cmd:?}`"))?;
    anyhow::ensure!(
        status.success(),
        "running `{cmd:?}` failed with status {status}"
    );

    Ok(())
}

#[derive(Debug)]
struct Config {
    tzdata: Option<PathBuf>,
    outdir: Option<PathBuf>,
    zic: PathBuf,
    verbose: bool,
}

impl Config {
    fn tzdata(&self) -> anyhow::Result<&Path> {
        self.tzdata.as_deref().context("missing path to tzdata directory")
    }

    fn outdir(&self) -> anyhow::Result<&Path> {
        self.outdir.as_deref().context("missing path to output directory")
    }

    fn zic(&self) -> &Path {
        &self.zic
    }
}

impl Default for Config {
    fn default() -> Config {
        Config {
            tzdata: None,
            outdir: None,
            zic: PathBuf::from("zic"),
            verbose: false,
        }
    }
}

impl args::Configurable for Config {
    fn configure(
        &mut self,
        p: &mut Parser,
        arg: &mut Arg,
    ) -> anyhow::Result<bool> {
        match *arg {
            Arg::Long("zic") => {
                self.zic = PathBuf::from(p.value().context("--zic")?);
            }
            Arg::Short('v') | Arg::Long("verbose") => {
                self.verbose = true;
            }
            Arg::Value(ref mut value) => {
                if self.tzdata.is_none() {
                    let path = PathBuf::from(std::mem::take(value));
                    self.tzdata = Some(path);
                } else if self.outdir.is_none() {
                    let path = PathBuf::from(std::mem::take(value));
                    self.outdir = Some(path);
                } else {
                    return Ok(false);
                }
            }
            _ => return Ok(false),
        }
        Ok(true)
    }

    fn usage(&self) -> &[Usage] {
        const USAGES: &'static [Usage] = &[
            Usage::new(
                "-v, --verbose",
                "Add more output.",
                r#"
This is a generic flag that expands output beyond the "normal" amount. Which
output is added depends on the command.
"#,
            ),
            Usage::new(
                "--zic",
                "Set path to `zic` binary.",
                r#"
Sets the path to use for invoking the `zic` binary. By default, this is just
set to `zic`, which relies on it being in your `PATH`.
"#,
            ),
        ];
        USAGES
    }
}
