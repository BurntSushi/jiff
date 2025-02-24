use anyhow::Context;

use crate::args;

mod crc32;
mod shared;
mod tzdb;
mod unit_designator_match;
mod windows_zones;
mod zoneinfo;

const USAGE: &'static str = r#"
A tool for doing various types of generation tasks. Currently, this just
includes generating the data for the jiff-tzdb crate.

USAGE:
    jiff-cli generate <command>

COMMANDS:
    crc32                  Generate CRC32 data tables.
    jiff-tzdb              Generate Rust source code from TZif data for jiff-tzdb
    shared                 Copy shared code from Jiff to jiff-static proc macro
    unit-designator-match  Generate Rust `match` expression for parsing unit labels
    windows-zones          Generate mapping Windows TZ names to IANA names.
    zoneinfo               Generate TZif data for jiff-tzdb
"#;

pub fn run(p: &mut lexopt::Parser) -> anyhow::Result<()> {
    match &*args::next_as_command(USAGE, p)? {
        "crc32" => crc32::run(p),
        "jiff-tzdb" => tzdb::run(p),
        "shared" => shared::run(p),
        "unit-designator-match" => unit_designator_match::run(p),
        "windows-zones" => windows_zones::run(p),
        "zoneinfo" => zoneinfo::run(p),
        unk => anyhow::bail!("unrecognized command '{}'", unk),
    }
}

/// Run rustfmt on the given crate.
///
/// I'm not sure why, but running `rustfmt` on files directly sometimes
/// produces different output than running `cargo fmt`. Maybe `rustfmt`
/// isn't respecting the configuration somehow?
fn cargo_fmt(krate: &str) -> anyhow::Result<()> {
    use std::process::Command;

    let out = Command::new("cargo")
        .arg("fmt")
        .arg("-p")
        .arg(krate)
        .output()
        .context("`cargo fmt` command failed")?;
    anyhow::ensure!(
        out.status.success(),
        "cargo fmt -p {krate}: {}",
        bstr::BString::from(out.stderr),
    );
    Ok(())
}

/// Run rustfmt on the given file path.
fn rustfmt<P: AsRef<std::path::Path>>(path: P) -> anyhow::Result<()> {
    use std::process::Command;

    let path = path.as_ref();
    let out = Command::new("rustfmt")
        .arg(path)
        .output()
        .context("rustfmt command failed")?;
    anyhow::ensure!(
        out.status.success(),
        "rustfmt {}: {}",
        path.display(),
        bstr::BString::from(out.stderr),
    );
    Ok(())
}
