use alloc::{string::String, vec::Vec};

use crate::tz::TimeZone;

#[derive(Debug)]
pub(crate) struct BundledZoneInfo;

impl BundledZoneInfo {
    pub(crate) fn new() -> BundledZoneInfo {
        BundledZoneInfo
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
