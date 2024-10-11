use serde::{Deserialize, Serialize};
use std::ops::{Deref, DerefMut};

pub trait ToTimestamp {
    fn to_sqlx(self) -> Timestamp;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct Timestamp(jiff::Timestamp);

impl Timestamp {
    pub fn to_jiff(self) -> jiff::Timestamp {
        self.0
    }
}

impl ToTimestamp for jiff::Timestamp {
    fn to_sqlx(self) -> Timestamp {
        Timestamp(self)
    }
}

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
