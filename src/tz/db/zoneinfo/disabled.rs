use alloc::{string::String, vec::Vec};

use crate::tz::TimeZone;

pub(crate) struct ZoneInfo;

impl ZoneInfo {
    pub(crate) fn from_env() -> ZoneInfo {
        ZoneInfo
    }

    #[cfg(feature = "std")]
    pub(crate) fn from_dir(
        dir: &std::path::Path,
    ) -> Result<ZoneInfo, crate::Error> {
        Err(crate::error::err!(
            "system tzdb unavailable: \
             crate feature `tzdb-zoneinfo` is disabled, \
             tzdb lookup for {dir} has therefore failed",
            dir = dir.display(),
        ))
    }

    pub(crate) fn reset(&self) {}

    pub(crate) fn get(&self, _query: &str) -> Option<TimeZone> {
        None
    }

    pub(crate) fn available(&self) -> Vec<String> {
        Vec::new()
    }

    pub(crate) fn is_definitively_empty(&self) -> bool {
        true
    }
}

impl core::fmt::Debug for ZoneInfo {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "ZoneInfo(unavailable)")
    }
}
