use alloc::string::ToString;

use crate::tz::Tzif;

/// A list of all TZif files in our testdata directory.
///
/// Feel free to add more if there are other "interesting" cases. Note that
/// some tests iterate over this slice to check each entry. So adding a new
/// test file here might require updating some tests.
///
/// # Revisions
///
/// * 2024-03-27: Initial set pulled from my local copy of `tzdata 2024a`.
/// * 2024-07-05: Added `UTC`.
pub(crate) const TZIF_TEST_FILES: &[TzifTestFile] = &[
    TzifTestFile {
        name: "America/New_York",
        data: include_bytes!("testdata/america-new-york.tzif"),
    },
    TzifTestFile {
        name: "America/Sitka",
        data: include_bytes!("testdata/america-sitka.tzif"),
    },
    TzifTestFile {
        name: "America/St_Johns",
        data: include_bytes!("testdata/america-st-johns.tzif"),
    },
    TzifTestFile {
        name: "right/America/New_York",
        data: include_bytes!("testdata/right-america-new-york.tzif"),
    },
    TzifTestFile {
        name: "Antarctica/Troll",
        data: include_bytes!("testdata/antarctica-troll.tzif"),
    },
    TzifTestFile {
        name: "Australia/Tasmania",
        data: include_bytes!("testdata/australia-tasmania.tzif"),
    },
    TzifTestFile {
        name: "Europe/Dublin",
        data: include_bytes!("testdata/europe-dublin.tzif"),
    },
    TzifTestFile {
        name: "Pacific/Honolulu",
        data: include_bytes!("testdata/pacific-honolulu.tzif"),
    },
    TzifTestFile { name: "UTC", data: include_bytes!("testdata/utc.tzif") },
];

/// A single TZif datum.
///
/// It contains the name of the time zone and the raw bytes of the
/// corresponding TZif file.
#[derive(Clone, Copy)]
pub(crate) struct TzifTestFile {
    pub(crate) name: &'static str,
    pub(crate) data: &'static [u8],
}

impl TzifTestFile {
    /// Look up the TZif test file for the given time zone name.
    ///
    /// If one doesn't exist, then this panics and fails the current
    /// test.
    pub(crate) fn get(name: &str) -> TzifTestFile {
        for &tzif_file in TZIF_TEST_FILES {
            if tzif_file.name == name {
                return tzif_file;
            }
        }
        panic!("could not find TZif test file for {name:?}")
    }

    /// Parse this test TZif data into a structured representation.
    pub(crate) fn parse(self) -> Tzif {
        let name = Some(self.name.to_string());
        Tzif::parse(name, self.data).unwrap_or_else(|err| {
            panic!("failed to parse TZif test file for {:?}: {err}", self.name)
        })
    }

    /// Parse this test TZif data as if it were V1.
    pub(crate) fn parse_v1(self) -> Tzif {
        let name = Some(self.name.to_string());
        let mut data = self.data.to_vec();
        data[4] = 0;
        Tzif::parse(name, &data).unwrap_or_else(|err| {
            panic!(
                "failed to parse V1 TZif test file for {:?}: {err}",
                self.name
            )
        })
    }
}
