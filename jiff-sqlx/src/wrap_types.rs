pub trait ToTimestamp {
    fn to_sqlx(self) -> Timestamp;
}

#[derive(Debug, Clone, Copy)]
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

pub trait ToSignedDuration {
    fn to_sqlx(self) -> SignedDuration;
}

#[derive(Debug, Clone, Copy)]
pub struct SignedDuration(jiff::SignedDuration);

impl SignedDuration {
    pub fn to_jiff(self) -> jiff::SignedDuration {
        self.0
    }
}

impl ToSignedDuration for jiff::SignedDuration {
    fn to_sqlx(self) -> SignedDuration {
        SignedDuration(self)
    }
}

impl From<SignedDuration> for jiff::SignedDuration {
    fn from(sd: SignedDuration) -> Self {
        sd.0
    }
}

impl From<jiff::SignedDuration> for SignedDuration {
    fn from(sd: jiff::SignedDuration) -> Self {
        Self(sd)
    }
}
