use crate::{
    error::Error,
    instant::{Instant, Tai, Unix},
    tz::TimeZone,
    util::t,
};

use self::zoneinfo::ZoneInfo;

#[cfg(feature = "std")]
mod zoneinfo;

pub fn db() -> &'static TimeZoneDatabase {
    #[cfg(not(feature = "std"))]
    {
        static NONE: &'static TimeZoneDatabase = TimeZoneDatabase::none();
        NONE
    }
    #[cfg(feature = "std")]
    {
        use std::sync::OnceLock;

        static DB: OnceLock<TimeZoneDatabase> = OnceLock::new();
        DB.get_or_init(|| TimeZoneDatabase::from_env())
    }
}

#[derive(Debug)]
pub struct TimeZoneDatabase {
    kind: TimeZoneDatabaseKind,
}

#[derive(Debug)]
enum TimeZoneDatabaseKind {
    None,
    ZoneInfo(ZoneInfo),
}

impl TimeZoneDatabase {
    pub fn from_env() -> TimeZoneDatabase {
        #[cfg(feature = "std")]
        {
            let zoneinfo = ZoneInfo::from_env();
            let kind = TimeZoneDatabaseKind::ZoneInfo(zoneinfo);
            TimeZoneDatabase { kind }
        }
        #[cfg(not(feature = "std"))]
        {
            TimeZoneDatabase::none()
        }
    }

    pub const fn none() -> TimeZoneDatabase {
        let kind = TimeZoneDatabaseKind::None;
        TimeZoneDatabase { kind }
    }

    pub fn get(&self, name: &str) -> Result<TimeZone, Error> {
        match self.kind {
            TimeZoneDatabaseKind::None => {
                Err(Error::time_zone_lookup("unavailable", name))
            }
            TimeZoneDatabaseKind::ZoneInfo(ref db) => db
                .get(name)
                .ok_or_else(|| Error::time_zone_lookup("zoneinfo", name)),
        }
    }

    pub fn unix_to_tai(
        &self,
        instant: Instant<Unix>,
    ) -> Result<Instant<Tai>, Error> {
        match self.kind {
            TimeZoneDatabaseKind::None => todo!(),
            TimeZoneDatabaseKind::ZoneInfo(ref db) => db.unix_to_tai(instant),
        }
    }

    pub fn tai_to_unix(&self, instant: Instant<Tai>) -> Instant<Unix> {
        match self.kind {
            TimeZoneDatabaseKind::None => todo!(),
            TimeZoneDatabaseKind::ZoneInfo(ref db) => db.tai_to_unix(instant),
        }
    }

    pub fn reset(&self) {
        match self.kind {
            TimeZoneDatabaseKind::None => {}
            TimeZoneDatabaseKind::ZoneInfo(ref db) => db.reset(),
        }
    }

    pub(crate) fn unix_to_tai_timestamp(
        &self,
        unix_timestamp: t::UnixSeconds,
    ) -> Result<t::TaiSeconds, Error> {
        match self.kind {
            TimeZoneDatabaseKind::None => todo!(),
            TimeZoneDatabaseKind::ZoneInfo(ref db) => {
                db.unix_to_tai_timestamp(unix_timestamp)
            }
        }
    }

    pub(crate) fn tai_to_unix_timestamp(
        &self,
        tai_timestamp: t::TaiSeconds,
    ) -> (t::UnixSeconds, bool) {
        match self.kind {
            TimeZoneDatabaseKind::None => todo!(),
            TimeZoneDatabaseKind::ZoneInfo(ref db) => {
                db.tai_to_unix_timestamp(tai_timestamp)
            }
        }
    }
}
