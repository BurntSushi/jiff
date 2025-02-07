use diesel::{
    deserialize::{self, FromSql, Queryable},
    mysql::{
        data_types::{MysqlTime, MysqlTimestampType},
        Mysql, MysqlValue,
    },
    serialize::{self, Output, ToSql},
    sql_types,
};
use jiff::{civil, tz};

use crate::{Date, DateTime, Time, Timestamp, ToDiesel};

static UTC: tz::TimeZone = tz::TimeZone::UTC;

impl Queryable<sql_types::Datetime, Mysql> for Timestamp {
    type Row = Timestamp;

    fn build(row: Timestamp) -> deserialize::Result<Timestamp> {
        Ok(row)
    }
}

impl ToSql<sql_types::Datetime, Mysql> for Timestamp {
    fn to_sql<'b>(
        &'b self,
        out: &mut Output<'b, '_, Mysql>,
    ) -> serialize::Result {
        let mut dt = UTC.to_datetime(self.to_jiff());
        if dt.nanosecond() != 0 {
            dt = dt.round(jiff::Unit::Microsecond)?;
        }
        let mysql_time = MysqlTime::new(
            dt.year().try_into()?,
            dt.month().unsigned_abs().into(),
            dt.day().unsigned_abs().into(),
            dt.hour().unsigned_abs().into(),
            dt.minute().unsigned_abs().into(),
            dt.second().unsigned_abs().into(),
            (dt.subsec_nanosecond().unsigned_abs() / 1_000).into(),
            false,
            MysqlTimestampType::MYSQL_TIMESTAMP_DATETIME_TZ,
            0,
        );
        <MysqlTime as ToSql<sql_types::Datetime, Mysql>>::to_sql(
            &mysql_time,
            &mut out.reborrow(),
        )
    }
}

impl FromSql<sql_types::Datetime, Mysql> for Timestamp {
    fn from_sql(bytes: MysqlValue<'_>) -> deserialize::Result<Timestamp> {
        let mysql_time =
            <MysqlTime as FromSql<sql_types::Datetime, Mysql>>::from_sql(
                bytes,
            )?;
        let nanos =
            mysql_time.second_part.checked_mul(1_000).ok_or_else(|| {
                format!("converting second part to nanoseconds overflowed")
            })?;
        let dt = civil::DateTime::new(
            mysql_time.year.try_into()?,
            mysql_time.month.try_into()?,
            mysql_time.day.try_into()?,
            mysql_time.hour.try_into()?,
            mysql_time.minute.try_into()?,
            mysql_time.second.try_into()?,
            nanos.try_into()?,
        )?;
        let offset = tz::Offset::from_seconds(
            mysql_time.time_zone_displacement.try_into()?,
        )?;
        Ok(offset.to_timestamp(dt)?.to_diesel())
    }
}

impl Queryable<sql_types::Timestamp, Mysql> for DateTime {
    type Row = DateTime;

    fn build(row: DateTime) -> deserialize::Result<DateTime> {
        Ok(row)
    }
}

impl ToSql<sql_types::Timestamp, Mysql> for DateTime {
    fn to_sql<'b>(
        &'b self,
        out: &mut Output<'b, '_, Mysql>,
    ) -> serialize::Result {
        let mut dt = self.to_jiff();
        if dt.nanosecond() != 0 {
            dt = dt.round(jiff::Unit::Microsecond)?;
        }
        let mysql_time = MysqlTime::new(
            dt.year().try_into()?,
            dt.month().unsigned_abs().into(),
            dt.day().unsigned_abs().into(),
            dt.hour().unsigned_abs().into(),
            dt.minute().unsigned_abs().into(),
            dt.second().unsigned_abs().into(),
            (dt.subsec_nanosecond().unsigned_abs() / 1_000).into(),
            false,
            MysqlTimestampType::MYSQL_TIMESTAMP_DATETIME,
            0,
        );
        <MysqlTime as ToSql<sql_types::Timestamp, Mysql>>::to_sql(
            &mysql_time,
            &mut out.reborrow(),
        )
    }
}

impl FromSql<sql_types::Timestamp, Mysql> for DateTime {
    fn from_sql(bytes: MysqlValue<'_>) -> deserialize::Result<DateTime> {
        let mysql_time = <MysqlTime as FromSql<
            sql_types::Timestamp,
            Mysql,
        >>::from_sql(bytes)?;
        let nanos =
            mysql_time.second_part.checked_mul(1_000).ok_or_else(|| {
                format!("converting second part to nanoseconds overflowed")
            })?;
        let dt = civil::DateTime::new(
            mysql_time.year.try_into()?,
            mysql_time.month.try_into()?,
            mysql_time.day.try_into()?,
            mysql_time.hour.try_into()?,
            mysql_time.minute.try_into()?,
            mysql_time.second.try_into()?,
            nanos.try_into()?,
        )?;
        Ok(dt.to_diesel())
    }
}

impl Queryable<sql_types::Date, Mysql> for Date {
    type Row = Date;

    fn build(row: Date) -> deserialize::Result<Date> {
        Ok(row)
    }
}

impl ToSql<sql_types::Date, Mysql> for Date {
    fn to_sql<'b>(
        &'b self,
        out: &mut Output<'b, '_, Mysql>,
    ) -> serialize::Result {
        let date = self.to_jiff();
        let mysql_time = MysqlTime::new(
            date.year().try_into()?,
            date.month().unsigned_abs().into(),
            date.day().unsigned_abs().into(),
            0,
            0,
            0,
            0,
            false,
            MysqlTimestampType::MYSQL_TIMESTAMP_DATE,
            0,
        );
        <MysqlTime as ToSql<sql_types::Date, Mysql>>::to_sql(
            &mysql_time,
            &mut out.reborrow(),
        )
    }
}

impl FromSql<sql_types::Date, Mysql> for Date {
    fn from_sql(bytes: MysqlValue<'_>) -> deserialize::Result<Date> {
        let mysql_time =
            <MysqlTime as FromSql<sql_types::Date, Mysql>>::from_sql(bytes)?;
        let date = civil::Date::new(
            mysql_time.year.try_into()?,
            mysql_time.month.try_into()?,
            mysql_time.day.try_into()?,
        )?;
        Ok(date.to_diesel())
    }
}

impl Queryable<sql_types::Time, Mysql> for Time {
    type Row = Time;

    fn build(row: Time) -> deserialize::Result<Time> {
        Ok(row)
    }
}

impl ToSql<sql_types::Time, Mysql> for Time {
    fn to_sql<'b>(
        &'b self,
        out: &mut Output<'b, '_, Mysql>,
    ) -> serialize::Result {
        let mut time = self.to_jiff();
        if time.nanosecond() != 0 {
            time = time.round(jiff::Unit::Microsecond)?;
        }
        let mysql_time = MysqlTime::new(
            0,
            0,
            0,
            time.hour().unsigned_abs().into(),
            time.minute().unsigned_abs().into(),
            time.second().unsigned_abs().into(),
            (time.subsec_nanosecond().unsigned_abs() / 1_000).into(),
            false,
            MysqlTimestampType::MYSQL_TIMESTAMP_TIME,
            0,
        );
        <MysqlTime as ToSql<sql_types::Time, Mysql>>::to_sql(
            &mysql_time,
            &mut out.reborrow(),
        )
    }
}

impl FromSql<sql_types::Time, Mysql> for Time {
    fn from_sql(bytes: MysqlValue<'_>) -> deserialize::Result<Time> {
        let mysql_time =
            <MysqlTime as FromSql<sql_types::Time, Mysql>>::from_sql(bytes)?;
        let nanos =
            mysql_time.second_part.checked_mul(1_000).ok_or_else(|| {
                format!("converting second part to nanoseconds overflowed")
            })?;
        let time = civil::Time::new(
            mysql_time.hour.try_into()?,
            mysql_time.minute.try_into()?,
            mysql_time.second.try_into()?,
            nanos.try_into()?,
        )?;
        Ok(time.to_diesel())
    }
}
