use std::{
    collections::{BTreeMap, BTreeSet},
    fs::File,
    io::{BufWriter, Write},
    path::Path,
    sync::LazyLock,
};

use anyhow::Context;
use regex_lite::Regex;

/// Generate metadata independently of TZif deduplication: distinct primary
/// identifiers can have identical TZif data.
pub(super) fn generate(zoneinfo: &Path, jiff: &Path) -> anyhow::Result<()> {
    let read = |name| {
        let path = zoneinfo.join(name);
        std::fs::read_to_string(&path)
            .with_context(|| format!("failed to read {}", path.display()))
    };
    let metadata = Metadata::parse(
        &read("rearguard.zi")?,
        &read("backzone")?,
        &read("zone.tab")?,
    )?;
    let path = jiff.join("crates/jiff/src/tz/db/metadata.rs");
    let mut out =
        BufWriter::new(File::create(&path).with_context(|| {
            format!("failed to create {}", path.display())
        })?);
    metadata
        .write(&mut out)
        .and_then(|()| out.flush())
        .with_context(|| format!("failed to write {}", path.display()))?;
    super::super::rustfmt(&path)
}

#[derive(Debug)]
struct Metadata {
    primary: BTreeMap<String, String>,
    locations: BTreeMap<String, Location>,
}

impl Metadata {
    /// Follow ECMA-402's AvailableNamedTimeZoneIdentifiers link and country
    /// rules. Renames take effect with the input release; this generator does
    /// not impose the recommended rename waiting period.
    ///
    /// <https://tc39.es/ecma402/#sup-availablenamedtimezoneidentifiers>
    fn parse(
        zi: &str,
        backzone: &str,
        zone_tab: &str,
    ) -> anyhow::Result<Self> {
        let locations = parse_zone_tab(zone_tab)?;
        let links =
            parse_links(zi).context("failed to parse rearguard.zi links")?;
        let backzone_links =
            parse_links(backzone).context("failed to parse backzone links")?;
        let mut identifiers: BTreeSet<String> =
            links.keys().cloned().collect();
        for (i, line) in zi.lines().enumerate() {
            let lineno = i + 1;
            let mut fields = line.split_ascii_whitespace();
            if fields.next() != Some("Zone") {
                continue;
            }
            let name = fields.next().with_context(|| {
                format!("rearguard.zi:{lineno}: missing Zone name")
            })?;
            anyhow::ensure!(
                identifiers.insert(name.to_string()),
                "rearguard.zi:{lineno}: duplicate identifier {name}",
            );
        }

        let mut countries: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
        for (name, location) in &locations {
            anyhow::ensure!(
                identifiers.contains(name),
                "zone.tab identifier {name} is missing from rearguard.zi",
            );
            countries.entry(&location.country).or_default().push(name);
        }

        let mut primary = BTreeMap::new();
        for name in &identifiers {
            let mut primary_name = name.as_str();
            if links.contains_key(name) && !locations.contains_key(name) {
                let zone = resolve_link(&links, name)?;
                anyhow::ensure!(
                    identifiers.contains(zone),
                    "{name} resolves to missing Zone {zone}",
                );
                let identifier_country =
                    country(name, &locations, &links, &backzone_links)?;
                let zone_country =
                    country(zone, &locations, &links, &backzone_links)?;
                primary_name = if zone.starts_with("Etc/")
                    || identifier_country == zone_country
                {
                    zone
                } else {
                    let country = identifier_country.with_context(|| {
                        format!("could not determine the country for {name}")
                    })?;
                    let country_zones =
                        countries.get(country).with_context(|| {
                            format!(
                                "no zone.tab entries for \
                                 {name}'s country {country}",
                            )
                        })?;
                    if country_zones.len() == 1 {
                        country_zones[0]
                    } else {
                        backzone_links.get(name).with_context(|| {
                            format!("missing backzone Link for {name}")
                        })?
                    }
                };
            }
            if matches!(primary_name, "Etc/UTC" | "Etc/GMT" | "GMT") {
                primary_name = "UTC";
            }
            primary.insert(name.clone(), primary_name.to_string());
        }
        for (name, target) in &primary {
            anyhow::ensure!(
                primary.get(target) == Some(target),
                "{name} resolves to {target}, \
                 which is not a primary identifier",
            );
        }
        Ok(Metadata { primary, locations })
    }

    fn write(&self, mut out: impl Write) -> std::io::Result<()> {
        writeln!(out, "// Generated by `jiff-cli generate jiff-tzdb`.")?;
        writeln!(out, "use super::{{ArrayStr, TimeZoneLocation}};\n")?;
        writeln!(
            out,
            "// Sorted in ascending order by time zone identifier."
        )?;
        writeln!(out, "pub(super) static TIME_ZONE_PRIMARY_IDENTIFIER: &[(&str, &str)] = &[")?;
        for (name, primary) in &self.primary {
            writeln!(out, "    ({name:?}, {primary:?}),")?;
        }
        writeln!(out, "];\n")?;
        writeln!(out, "pub(super) static TIME_ZONE_METADATA: &[(&str, TimeZoneLocation)] = &[")?;
        for (name, location) in &self.locations {
            let Location { country, latitude, longitude } = location;
            writeln!(out, "    ({name:?}, TimeZoneLocation {{")?;
            writeln!(out, "        country: country({country:?}),")?;
            writeln!(out, "        latitude: {latitude:?},")?;
            writeln!(out, "        longitude: {longitude:?},")?;
            writeln!(out, "    }}),")?;
        }
        writeln!(out, "];\n")?;
        // Option::unwrap isn't const on Jiff's MSRV.
        writeln!(out, "const fn country(code: &str) -> ArrayStr<2> {{")?;
        writeln!(out, "    match ArrayStr::new(code) {{")?;
        writeln!(out, "        Some(country) => country,")?;
        writeln!(out, "        None => panic!(\"invalid country code\"),")?;
        writeln!(out, "    }}")?;
        writeln!(out, "}}")?;
        Ok(())
    }
}

/// A location from zone.tab. Non-geographical identifiers such as UTC have
/// metadata with no location.
#[derive(Debug)]
struct Location {
    country: String,
    latitude: f64,
    longitude: f64,
}

fn parse_zone_tab(src: &str) -> anyhow::Result<BTreeMap<String, Location>> {
    let mut locations = BTreeMap::new();
    for (i, line) in src.lines().enumerate() {
        let lineno = i + 1;
        let line = line.split('#').next().unwrap().trim();
        if line.is_empty() {
            continue;
        }
        let parse = || -> anyhow::Result<(&str, Location)> {
            let mut fields = line.split_ascii_whitespace();
            let country = fields.next().context("missing country code")?;
            anyhow::ensure!(
                country.len() == 2
                    && country.bytes().all(|b| b.is_ascii_uppercase()),
                "invalid country code {country:?}",
            );
            let coordinates = fields.next().context("missing coordinates")?;
            let (latitude, longitude) = parse_coordinates(coordinates)?;
            let name =
                fields.next().context("missing time zone identifier")?;
            Ok((
                name,
                Location { country: country.to_string(), latitude, longitude },
            ))
        };
        let (name, location) =
            parse().with_context(|| format!("zone.tab:{lineno}"))?;
        anyhow::ensure!(
            locations.insert(name.to_string(), location).is_none(),
            "zone.tab:{lineno}: duplicate identifier {name}",
        );
    }
    Ok(locations)
}

fn parse_coordinates(src: &str) -> anyhow::Result<(f64, f64)> {
    static RE: LazyLock<Regex> = LazyLock::new(|| {
        Regex::new(
            r"(?x)^
                ([+-][0-9]{2})([0-5][0-9])([0-5][0-9])?
                ([+-][0-9]{3})([0-5][0-9])([0-5][0-9])?
            $",
        )
        .unwrap()
    });
    let caps = RE
        .captures(src)
        .with_context(|| format!("invalid coordinates {src:?}"))?;
    anyhow::ensure!(
        caps.get(3).is_some() == caps.get(6).is_some(),
        "invalid coordinates {src:?}",
    );
    let parse = |i: usize, max: f64| -> anyhow::Result<f64> {
        let degrees: f64 = caps[i].parse()?;
        let minutes: f64 = caps[i + 1].parse()?;
        let seconds =
            caps.get(i + 2).map_or(Ok(0.0), |m| m.as_str().parse::<f64>())?;
        let value = degrees.abs() + minutes / 60.0 + seconds / 3600.0;
        anyhow::ensure!(value <= max, "coordinate out of range: {src:?}");
        Ok(value.copysign(degrees))
    };
    Ok((parse(1, 90.0)?, parse(4, 180.0)?))
}

fn parse_links(src: &str) -> anyhow::Result<BTreeMap<String, String>> {
    let mut links = BTreeMap::new();
    for (i, line) in src.lines().enumerate() {
        let lineno = i + 1;
        let line = line.strip_prefix("#PACKRATLIST zone.tab ").unwrap_or(line);
        let mut fields =
            line.split('#').next().unwrap().split_ascii_whitespace();
        if fields.next() != Some("Link") {
            continue;
        }
        let target = fields
            .next()
            .with_context(|| format!("Link on line {lineno} has no target"))?;
        let name = fields
            .next()
            .with_context(|| format!("Link on line {lineno} has no name"))?;
        anyhow::ensure!(
            links.insert(name.to_string(), target.to_string()).is_none(),
            "duplicate Link name {name} on line {lineno}",
        );
    }
    Ok(links)
}

fn resolve_link<'a>(
    links: &'a BTreeMap<String, String>,
    name: &'a str,
) -> anyhow::Result<&'a str> {
    let mut seen = BTreeSet::new();
    let mut zone = name;
    while let Some(target) = links.get(zone) {
        anyhow::ensure!(seen.insert(zone), "Link cycle involving {name}");
        zone = target;
    }
    Ok(zone)
}

/// Infer an alias's country from historical links, stopping as soon as a name
/// has its own zone.tab entry, before following any cross-country links.
fn country<'a>(
    name: &'a str,
    locations: &'a BTreeMap<String, Location>,
    links: &'a BTreeMap<String, String>,
    backzone_links: &'a BTreeMap<String, String>,
) -> anyhow::Result<Option<&'a str>> {
    let mut seen = BTreeSet::new();
    let mut current = name;
    loop {
        if let Some(location) = locations.get(current) {
            return Ok(Some(&location.country));
        }
        // This historical link is itself cross-country (to Europe/Oslo), so
        // backzone alone cannot establish Jan Mayen's country. ECMA-402 calls
        // out this exception explicitly. This case comes from this portion
        // of the ECMAScript spec:
        //
        // > Note that zone.tab is the preferred source of mapping data because
        // > backzone mappings may, in rare cases, cross the boundaries of ISO
        // > 3166-1 Alpha-2 country codes. For example, "Atlantic/Jan_Mayen"
        // > (in country code "SJ") is mapped in backzone to "Europe/Oslo"
        // > (in country code "NO"). As of the 2024a release of the IANA Time
        // > Zone Database, "Atlantic/Jan_Mayen" is the only case where this
        // > happens.
        //
        // Ref: <https://tc39.es/ecma402/#sup-availablenamedtimezoneidentifiers>
        if current == "Atlantic/Jan_Mayen" {
            return Ok(Some("SJ"));
        }
        anyhow::ensure!(
            seen.insert(current),
            "country Link cycle involving {name}"
        );
        match backzone_links.get(current).or_else(|| links.get(current)) {
            None => return Ok(None),
            Some(target) => current = target,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn primary_identifiers_without_backzone() {
        let zi = "\
Zone Europe/Berlin 1 - CET
Link Europe/Berlin Europe/Oslo
Link Europe/Berlin Arctic/Longyearbyen
Link Europe/Berlin Atlantic/Jan_Mayen
Zone Europe/Prague 1 - CET
Link Europe/Prague Europe/Bratislava
Link Europe/Bratislava Test/Bratislava
Zone Europe/Kyiv 2 - EET
Link Europe/Kyiv Europe/Kiev
Zone Etc/UTC 0 - UTC
Zone Etc/GMT 0 - GMT
Zone Etc/GMT+5 -5 - -05
Link Etc/UTC UTC
Link Etc/UTC UCT
Link Etc/UTC Etc/Universal
Link Etc/GMT GMT
Link GMT Greenwich
Zone Factory 0 - -00
Zone PST8PDT -8 - PST
";
        let zone_tab = "\
# country coordinates identifier comments
DE +5230+01322 Europe/Berlin
NO +5955+01045 Europe/Oslo
SJ +7800+01600 Arctic/Longyearbyen
CZ +5005+01426 Europe/Prague
SK +4809+01707 Europe/Bratislava
UA +5026+03031 Europe/Kyiv
";
        let metadata = Metadata::parse(zi, "", zone_tab).unwrap();
        for (name, primary) in [
            ("Atlantic/Jan_Mayen", "Arctic/Longyearbyen"),
            ("Test/Bratislava", "Europe/Bratislava"),
            ("Europe/Kiev", "Europe/Kyiv"),
            ("Etc/UTC", "UTC"),
            ("Etc/GMT", "UTC"),
            ("GMT", "UTC"),
            ("Greenwich", "UTC"),
            ("UCT", "UTC"),
            ("Etc/Universal", "UTC"),
        ] {
            assert_eq!(metadata.primary[name], primary, "{name}");
        }
        // Every zone.tab identifier remains primary, including Link names.
        for name in metadata.locations.keys() {
            assert_eq!(&metadata.primary[name], name);
        }
        for name in ["Etc/GMT+5", "UTC", "Factory", "PST8PDT"] {
            assert_eq!(metadata.primary[name], name);
            assert!(!metadata.locations.contains_key(name));
        }
    }

    #[test]
    fn primary_identifiers_with_backzone() {
        let zi = "\
Zone Africa/Abidjan 0 - GMT
Link Africa/Abidjan Atlantic/Reykjavik
Link Africa/Abidjan Iceland
Zone Africa/Nairobi 3 - EAT
Link Africa/Nairobi Africa/Asmara
Link Africa/Nairobi Africa/Asmera
Zone America/Panama -5 - EST
Link America/Panama America/Atikokan
Link America/Panama America/Coral_Harbour
Zone America/Toronto -5 - EST
Zone Pacific/Port_Moresby 10 - +10
Link Pacific/Port_Moresby Pacific/Chuuk
Link Pacific/Port_Moresby Pacific/Truk
Link Pacific/Port_Moresby Pacific/Yap
Zone Pacific/Guadalcanal 11 - +11
Link Pacific/Guadalcanal Pacific/Pohnpei
Link Pacific/Guadalcanal Pacific/Ponape
";
        let backzone = "\
Link Africa/Asmara Africa/Asmera
Link Atlantic/Reykjavik Iceland
#PACKRATLIST zone.tab Link America/Atikokan America/Coral_Harbour
Link Pacific/Chuuk Pacific/Truk
Link Pacific/Chuuk Pacific/Yap
Link Pacific/Pohnpei Pacific/Ponape
";
        let zone_tab = "\
CI +0519-00402 Africa/Abidjan
IS +6409-02151 Atlantic/Reykjavik
KE -0117+03649 Africa/Nairobi
ER +1520+03853 Africa/Asmara
PA +0858-07932 America/Panama
CA +484531-0913718 America/Atikokan
CA +4339-07923 America/Toronto
PG -0930+14710 Pacific/Port_Moresby
FM +0725+15147 Pacific/Chuuk Chuuk
FM +0658+15813 Pacific/Pohnpei Pohnpei
SB -0932+16012 Pacific/Guadalcanal
";
        let metadata = Metadata::parse(zi, backzone, zone_tab).unwrap();
        let without_backzone = Metadata::parse(zi, "", zone_tab).unwrap();
        for (name, primary) in [
            ("Iceland", "Atlantic/Reykjavik"),
            ("Africa/Asmera", "Africa/Asmara"),
            ("America/Coral_Harbour", "America/Atikokan"),
            ("Pacific/Truk", "Pacific/Chuuk"),
            ("Pacific/Yap", "Pacific/Chuuk"),
            ("Pacific/Ponape", "Pacific/Pohnpei"),
        ] {
            assert_eq!(metadata.primary[name], primary, "{name}");
            assert_ne!(without_backzone.primary[name], primary, "{name}");
        }
    }

    #[test]
    fn coordinates() {
        for (src, latitude, longitude) in [
            ("+4043-07400", 40.0 + 43.0 / 60.0, -74.0),
            ("-3352+15113", -(33.0 + 52.0 / 60.0), 151.0 + 13.0 / 60.0),
            (
                "+404251-0740023",
                40.0 + 42.0 / 60.0 + 51.0 / 3600.0,
                -(74.0 + 23.0 / 3600.0),
            ),
            (
                "-690022+0393524",
                -(69.0 + 22.0 / 3600.0),
                39.0 + 35.0 / 60.0 + 24.0 / 3600.0,
            ),
            ("+9000-18000", 90.0, -180.0),
            ("-900000+1800000", -90.0, 180.0),
        ] {
            assert_eq!(
                parse_coordinates(src).unwrap(),
                (latitude, longitude),
                "{src}"
            );
        }
        for src in [
            "",
            "+4043",
            "4043-07400",
            "+4060-07400",
            "+4043-18100",
            "+9001+00000",
            "+9100+00000",
            "+404260-0740000",
            "+404200-0740060",
            "+404251-07400",
            "+4043-0740023",
            "+4043x07400",
            "+é43-07400",
        ] {
            assert!(parse_coordinates(src).is_err(), "{src}");
        }
    }

    #[test]
    fn invalid_links() {
        assert!(Metadata::parse("Link A B\nLink B A\n", "", "").is_err());
        assert!(Metadata::parse("Link Missing Alias\n", "", "").is_err());
        assert!(parse_links("Link A B\nLink A B\n").is_err());
        assert!(parse_links("Link A # missing name\n").is_err());
    }
}
