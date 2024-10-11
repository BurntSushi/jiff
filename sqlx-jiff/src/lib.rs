use serde::{Deserialize, Serialize};
use std::ops::{Deref, DerefMut};

#[cfg(feature = "postgres")]
mod postgres;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Timestamp(pub jiff::Timestamp);

impl From<Timestamp> for jiff::Timestamp {
    fn from(ts: Timestamp) -> Self {
        ts.0
    }
}

impl From<jiff::Timestamp> for Timestamp {
    fn from(ts: jiff::Timestamp) -> Self {
        Self(ts)
    }
}

impl Deref for Timestamp {
    type Target = jiff::Timestamp;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Timestamp {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
