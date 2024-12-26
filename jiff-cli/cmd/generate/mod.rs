use crate::args;

mod crc32;
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
    unit-designator-match  Generate Rust `match` expression for parsing unit labels
    windows-zones          Generate mapping Windows TZ names to IANA names.
    zoneinfo               Generate TZif data for jiff-tzdb
"#;

pub fn run(p: &mut lexopt::Parser) -> anyhow::Result<()> {
    match &*args::next_as_command(USAGE, p)? {
        "crc32" => crc32::run(p),
        "jiff-tzdb" => tzdb::run(p),
        "unit-designator-match" => unit_designator_match::run(p),
        "windows-zones" => windows_zones::run(p),
        "zoneinfo" => zoneinfo::run(p),
        unk => anyhow::bail!("unrecognized command '{}'", unk),
    }
}
