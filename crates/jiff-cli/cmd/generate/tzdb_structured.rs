/*!
A command for generating Rust source files from a zoneinfo directory.

This walks the directory tree given and looks for valid TZif data files. All
found files are parsed into a `jiff_core::tz::tzif::TimeZone`. They are then
written out as structured data via Rust source code.
*/

use std::{
    collections::{BTreeMap, BTreeSet},
    fs::File,
    io::{Read, Seek, Write},
    path::{Path, PathBuf},
};

use anyhow::Context;
use lexopt::{Arg, Parser};
use quote::quote;

use jcore::tz::{
    posix,
    tzif::{self, is_possibly_tzif},
};

use crate::args::{self, Usage};

const USAGE: &'static str = r#"
Generate Rust source code from a zoneinfo directory.

USAGE:
    jiff-cli generate jiff-tzdb-structured <zoneinfo-dir> [<jiff-tzdb-dir>]

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

    let version = read_tzdb_version(&config, &zoneinfo);
    let time_zones =
        parse_time_zones(&config, read_time_zones(&config, &zoneinfo)?)?;

    let tzname_map_path = jiff_tzdb.join("tznamemap.rs");
    write_tzname_map(&tzname_map_path, version, &time_zones)?;
    let timezones_path = jiff_tzdb.join("timezones.rs");
    write_time_zones(&timezones_path, &time_zones)?;

    super::rustfmt(&tzname_map_path)?;
    super::rustfmt(&timezones_path)?;

    Ok(())
}

fn write_tzname_map(
    path: &Path,
    version: Option<String>,
    time_zones: &[ParsedTimeZone],
) -> anyhow::Result<()> {
    let mut out = std::io::BufWriter::new(File::create(path)?);
    let version =
        version.map(|v| quote!(Some(#v))).unwrap_or_else(|| quote!(None));
    writeln!(
        out,
        "{}",
        quote! {
            pub(super) static VERSION: Option<&str> = #version;
        },
    )?;
    writeln!(out, "")?;

    let mut named = time_zones
        .iter()
        .flat_map(|p| {
            let static_name = quote::format_ident!("{}", p.static_name());
            p.names.iter().map(move |name| {
                let name = &name.as_is;
                (
                    name.clone(),
                    quote! {
                        jcore::tz::tzif::MaybeNamedTimeZone {
                            name: Some(jcore::util::SmallStr::statik(#name)),
                            tz: &crate::timezones::#static_name,
                        }
                    },
                )
            })
        })
        .collect::<Vec<_>>();
    named.sort_by(|(name1, _), (name2, _)| name1.cmp(&name2));
    let named = named.iter().map(|(_, quoted)| quoted);
    writeln!(
        out,
        "{}",
        quote! {
            pub(crate) static MAP: &'static [jcore::tz::tzif::MaybeNamedTimeZone<&'static jcore::tz::tzif::TimeZone>] = &[
                #(#named),*
            ];
        },
    )?;
    writeln!(out, "")?;

    Ok(())
}

fn write_time_zones(
    path: &Path,
    time_zones: &[ParsedTimeZone],
) -> anyhow::Result<()> {
    let mut out = std::io::BufWriter::new(File::create(path)?);
    writeln!(out, "use jcore::tz::tzif::DateTime;")?;
    writeln!(out, "use jcore::tz::tzif::Indicator::*;")?;
    writeln!(out, "use jcore::tz::tzif::LocalTimeType;")?;
    writeln!(out, "use jcore::tz::tzif::Timestamp;")?;
    writeln!(out, "use jcore::tz::tzif::TransitionInfo;")?;
    writeln!(out, "use jcore::tz::tzif::TransitionKind::{{self, *}};")?;
    writeln!(out, "")?;
    writeln!(
        out,
        "{}",
        quote::quote! {
            const fn dt(year: i16, month: i8, day: i8, hour: i8, minute: i8, second: i8) -> DateTime {
                DateTime::constant(year, month, day, hour, minute, second)
            }

            const fn ts(second: i64) -> Timestamp {
                Timestamp::constant(second)
            }

            const fn ti(type_index: u8, kind: TransitionKind) -> TransitionInfo {
                TransitionInfo::constant(type_index, kind)
            }
        }
    )?;
    for p in time_zones {
        let tz = p.tz.quote();
        let static_name = quote::format_ident!("{}", p.static_name());
        writeln!(
            out,
            "{}",
            quote! {
                pub(crate) static #static_name: jcore::tz::tzif::TimeZone = #tz;
            }
        )?;
    }
    out.flush()?;
    Ok(())
}

/// Parse time zones that we read from disk.
///
/// The association list returned maps a parsed and unnamed time zone to its
/// corresponding set of names. The set of names corresponds precisely to
/// identical TZif data.
///
/// The names are guaranteed to non-empty.
fn parse_time_zones(
    _config: &Config,
    time_zones: BTreeMap<Vec<u8>, BTreeSet<String>>,
) -> anyhow::Result<Vec<ParsedTimeZone>> {
    let mut parsed = vec![];
    let mut all_lower_names = BTreeSet::new();
    for (tzif, as_is_names) in time_zones {
        let representative = as_is_names.first().unwrap().clone();
        let tz = tzif::TimeZone::parse(&tzif).with_context(|| {
            format!("failed to parse TZif data from {representative}")
        })?;

        let mut names = vec![];
        for as_is in as_is_names {
            let lower = as_is.to_ascii_lowercase();
            anyhow::ensure!(
                all_lower_names.insert(lower.clone()),
                "duplicate lowercase name {as_is} found for {representative}",
            );
            names.push(TimeZoneName { as_is, lower });
        }
        parsed.push(ParsedTimeZone { tz, representative, names });
    }
    parsed.sort_by(|p1, p2| p1.representative.cmp(&p2.representative));
    Ok(parsed)
}

/// Reads all time zone data from the given zoneinfo directory.
///
/// The map returned is from the raw TZif data to a set of names corresponding
/// to that data.
fn read_time_zones(
    config: &Config,
    zoneinfo: &Path,
) -> anyhow::Result<BTreeMap<Vec<u8>, BTreeSet<String>>> {
    let mut buf = vec![];
    let mut tzif_to_names: BTreeMap<Vec<u8>, BTreeSet<String>> =
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

        // OK, now that we have a TZif file, read everything into memory.
        buf.clear();
        file.read_to_end(&mut buf).with_context(|| {
            format!(
                "failed to read all data from {path}",
                path = path.display()
            )
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

        tzif_to_names
            .entry(buf.clone())
            .or_default()
            .insert(tzname.to_string());
    }
    Ok(tzif_to_names)
}

fn read_tzdb_version(config: &Config, zoneinfo: &Path) -> Option<String> {
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
    version
}

struct ParsedTimeZone {
    tz: tzif::TimeZone,
    representative: String,
    names: Vec<TimeZoneName>,
}

struct TimeZoneName {
    as_is: String,
    lower: String,
}

impl ParsedTimeZone {
    fn static_name(&self) -> String {
        self.representative
            .to_ascii_uppercase()
            .replace('/', "_")
            .replace('-', "_MINUS_")
            .replace('+', "_PLUS_")
    }
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

// Everything below at this point is quasi-quoting the jcore data type
// values into `static` data structures as Rust source code.

trait Quote {
    fn quote(&self) -> proc_macro2::TokenStream;
}

impl Quote for tzif::TimeZone {
    fn quote(&self) -> proc_macro2::TokenStream {
        let tzif::TimeZone {
            version,
            checksum,
            ref designations,
            ref posix_tz,
            ref types,
            ref transitions,
        } = *self;
        let designations = designations.iter().map(Quote::quote);
        let posix_tz = posix_tz
            .as_ref()
            .map(|tz| {
                let tz = tz.quote();
                quote!(Some(#tz))
            })
            .unwrap_or_else(|| quote!(None));
        let types = types.iter().map(tzif::LocalTimeType::quote);
        let transitions = transitions.quote();
        quote! {{
            static __TZ_DESIGNATIONS: &[jcore::tz::Abbreviation] = &[#(#designations),*];
            jcore::tz::tzif::TimeZone {
                version: #version,
                checksum: #checksum,
                designations: jcore::util::MaybeStaticSlice::statik(__TZ_DESIGNATIONS),
                posix_tz: #posix_tz,
                types: jcore::util::MaybeStaticSlice::statik(&[#(#types),*]),
                transitions: #transitions,
            }
        }}
    }
}

impl Quote for tzif::Transitions {
    fn quote(&self) -> proc_macro2::TokenStream {
        let tzif::Transitions {
            ref timestamps,
            ref civil_starts,
            ref civil_ends,
            ref infos,
        } = *self;
        let timestamps = timestamps.iter().map(tzif::Timestamp::quote);
        let civil_starts = civil_starts.iter().map(tzif::DateTime::quote);
        let civil_ends = civil_ends.iter().map(tzif::DateTime::quote);
        let infos = infos.iter().map(tzif::TransitionInfo::quote);
        quote! {
            jcore::tz::tzif::Transitions {
                timestamps: jcore::util::MaybeStaticSlice::statik(&[#(#timestamps),*]),
                civil_starts: jcore::util::MaybeStaticSlice::statik(&[#(#civil_starts),*]),
                civil_ends: jcore::util::MaybeStaticSlice::statik(&[#(#civil_ends),*]),
                infos: jcore::util::MaybeStaticSlice::statik(&[#(#infos),*]),
            }
        }
    }
}

impl Quote for tzif::LocalTimeType {
    fn quote(&self) -> proc_macro2::TokenStream {
        let tzif::LocalTimeType { offset, dst, designation, indicator } =
            *self;
        let offset = offset.seconds();
        let dst = dst.quote();
        let indicator = indicator.quote();
        quote! {
            LocalTimeType::constant(
                #offset,
                #dst,
                #designation,
                #indicator,
            )
        }
    }
}

impl Quote for tzif::Indicator {
    fn quote(&self) -> proc_macro2::TokenStream {
        match *self {
            tzif::Indicator::LocalWall => quote! {
                LocalWall
            },
            tzif::Indicator::LocalStandard => quote! {
                LocalStandard
            },
            tzif::Indicator::UTStandard => quote! {
                UTStandard
            },
        }
    }
}

impl Quote for tzif::TransitionInfo {
    fn quote(&self) -> proc_macro2::TokenStream {
        let tzif::TransitionInfo { type_index, kind } = *self;
        let kind = kind.quote();
        quote! {
            ti(#type_index, #kind)
        }
    }
}

impl Quote for tzif::TransitionKind {
    fn quote(&self) -> proc_macro2::TokenStream {
        match *self {
            tzif::TransitionKind::Unambiguous => quote! {
                Unambiguous
            },
            tzif::TransitionKind::Gap => quote! {
                Gap
            },
            tzif::TransitionKind::Fold => quote! {
                Fold
            },
        }
    }
}

impl Quote for tzif::DateTime {
    fn quote(&self) -> proc_macro2::TokenStream {
        let year = self.year();
        let month = self.month();
        let day = self.day();
        let hour = self.hour();
        let minute = self.minute();
        let second = self.second();
        quote! {
            dt(#year, #month, #day, #hour, #minute, #second)
        }
    }
}

impl Quote for posix::TimeZone {
    fn quote(&self) -> proc_macro2::TokenStream {
        let posix::TimeZone { ref std_abbrev, ref std_offset, ref dst } =
            *self;
        let std_abbrev = std_abbrev.quote();
        let std_offset = std_offset.quote();
        let dst = dst
            .as_ref()
            .map(|dst| {
                let dst = dst.quote();
                quote!(Some(#dst))
            })
            .unwrap_or_else(|| quote!(None));
        quote! {
            jcore::tz::posix::TimeZone {
                std_abbrev: #std_abbrev,
                std_offset: #std_offset,
                dst: #dst,
            }
        }
    }
}

impl Quote for posix::Dst {
    fn quote(&self) -> proc_macro2::TokenStream {
        let posix::Dst { ref abbrev, ref offset, ref rule } = *self;
        let abbrev = abbrev.quote();
        let offset = offset.quote();
        let rule = rule.quote();
        quote! {
            jcore::tz::posix::Dst {
                abbrev: #abbrev,
                offset: #offset,
                rule: #rule,
            }
        }
    }
}

impl Quote for posix::Rule {
    fn quote(&self) -> proc_macro2::TokenStream {
        let start = self.start.quote();
        let end = self.end.quote();
        quote! {
            jcore::tz::posix::Rule { start: #start, end: #end }
        }
    }
}

impl Quote for posix::DayTime {
    fn quote(&self) -> proc_macro2::TokenStream {
        let posix::DayTime { ref date, ref time } = *self;
        let date = date.quote();
        let time = time.quote();
        quote! {
            jcore::tz::posix::DayTime { date: #date, time: #time }
        }
    }
}

impl Quote for posix::Day {
    fn quote(&self) -> proc_macro2::TokenStream {
        match *self {
            posix::Day::JulianOne(day) => quote! {
                jcore::tz::posix::Day::JulianOne(#day)
            },
            posix::Day::JulianZero(day) => quote! {
                jcore::tz::posix::Day::JulianZero(#day)
            },
            posix::Day::WeekdayOfMonth { month, week, weekday } => {
                let weekday = weekday.quote();
                quote! {
                    jcore::tz::posix::Day::WeekdayOfMonth {
                        month: #month,
                        week: #week,
                        weekday: #weekday,
                    }
                }
            }
        }
    }
}

impl Quote for jcore::civil::Weekday {
    fn quote(&self) -> proc_macro2::TokenStream {
        use jcore::civil::Weekday::*;
        match *self {
            Sunday => quote!(jcore::civil::Weekday::Sunday),
            Monday => quote!(jcore::civil::Weekday::Monday),
            Tuesday => quote!(jcore::civil::Weekday::Tuesday),
            Wednesday => quote!(jcore::civil::Weekday::Wednesday),
            Thursday => quote!(jcore::civil::Weekday::Thursday),
            Friday => quote!(jcore::civil::Weekday::Friday),
            Saturday => quote!(jcore::civil::Weekday::Saturday),
        }
    }
}

impl Quote for jcore::tz::posix::TransitionCivilTime {
    fn quote(&self) -> proc_macro2::TokenStream {
        let posix::TransitionCivilTime { second } = *self;
        quote! {
            jcore::tz::posix::TransitionCivilTime { second: #second }
        }
    }
}

impl Quote for tzif::Timestamp {
    fn quote(&self) -> proc_macro2::TokenStream {
        let second = self.as_second();
        quote! {
            ts(#second)
        }
    }
}

impl Quote for jcore::tz::Offset {
    fn quote(&self) -> proc_macro2::TokenStream {
        let seconds = self.seconds();
        quote! {
            jcore::tz::Offset::constant_seconds(#seconds)
        }
    }
}

impl Quote for jcore::tz::Dst {
    fn quote(&self) -> proc_macro2::TokenStream {
        match *self {
            jcore::tz::Dst::Yes => quote! { jcore::tz::Dst::Yes },
            jcore::tz::Dst::No => quote! { jcore::tz::Dst::No },
        }
    }
}

impl<const N: usize> Quote for jcore::util::SmallStr<N> {
    fn quote(&self) -> proc_macro2::TokenStream {
        let s = self.as_str();
        quote! {
            jcore::util::SmallStr::statik(#s)
        }
    }
}

impl<T: Quote + 'static> Quote for jcore::util::MaybeStaticSlice<T> {
    fn quote(&self) -> proc_macro2::TokenStream {
        let slice = self.as_slice().iter().map(Quote::quote);
        quote! {{
            jcore::util::MaybeStaticSlice::statik(&[#(#slice),*])
        }}
    }
}
