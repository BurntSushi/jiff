use diesel::{
    connection::Connection, mysql::MysqlConnection, sql_query, sql_types,
    QueryableByName, RunQueryDsl,
};
use jiff::civil;
use jiff_diesel::ToDiesel;

mod schema {
    diesel::table! {
        datetimes {
            id -> Integer, // Diesel tables require an ID column.
            ts -> Datetime,
            dt -> Timestamp,
            d -> Date,
            t -> Time,
        }
    }

    diesel::table! {
        nullable_datetimes {
            id -> Integer, // Diesel tables require an ID column.
            ts -> Nullable<Datetime>,
            dt -> Nullable<Timestamp>,
            d -> Nullable<Date>,
            t -> Nullable<Time>,
        }
    }
}

fn main() -> anyhow::Result<()> {
    // To set this up, I ran
    //
    //     $ sudo mariadb
    //     MariaDB [(none)]> CREATE USER 'demo'@'localhost' IDENTIFIED BY 'password';
    //     MariaDB [(none)]> CREATE DATABASE jiff_diesel_example;
    //     MariaDB [(none)]> GRANT ALL PRIVILEGES ON jiff_diesel_example.* TO 'demo'@'localhost';
    //
    // And then I was able to connect using the code below.
    let mut conn = MysqlConnection::establish(
        "mysql://demo:password@localhost/jiff_diesel_example",
    )?;

    sql_query(
        "CREATE TEMPORARY TABLE IF NOT EXISTS datetimes (
            id integer primary key,
            ts datetime not null,
            dt timestamp not null,
            d date not null,
            t time(6) not null
        )",
    )
    .execute(&mut conn)
    .unwrap();

    sql_query(
        "CREATE TEMPORARY TABLE IF NOT EXISTS nullable_datetimes (
            id integer primary key,
            ts datetime,
            dt timestamp,
            d date,
            t time(6)
        )",
    )
    .execute(&mut conn)
    .unwrap();

    example_datetime_roundtrip(&mut conn)?;
    example_nullable_datetime_roundtrip(&mut conn)?;
    example_datetime_sql_query_roundtrip(&mut conn)?;

    Ok(())
}

/// Performs a round-trip with all of Jiff's datetime types.
fn example_datetime_roundtrip(
    conn: &mut MysqlConnection,
) -> anyhow::Result<()> {
    use diesel::prelude::*;

    #[derive(
        Clone, Copy, Debug, PartialEq, Queryable, Insertable, Selectable,
    )]
    #[diesel(table_name = schema::datetimes)]
    #[diesel(check_for_backend(diesel::mysql::Mysql))]
    struct Row {
        id: i32,
        #[diesel(
            serialize_as = jiff_diesel::Timestamp,
            deserialize_as = jiff_diesel::Timestamp
        )]
        ts: jiff::Timestamp,
        #[diesel(
            serialize_as = jiff_diesel::DateTime,
            deserialize_as = jiff_diesel::DateTime
        )]
        dt: jiff::civil::DateTime,
        #[diesel(
            serialize_as = jiff_diesel::Date,
            deserialize_as = jiff_diesel::Date
        )]
        d: jiff::civil::Date,
        #[diesel(
            serialize_as = jiff_diesel::Time,
            deserialize_as = jiff_diesel::Time
        )]
        t: jiff::civil::Time,
    }

    let given = Row {
        id: 0,
        ts: "1970-01-01T00:00:00Z".parse()?,
        dt: civil::date(2025, 7, 20).at(0, 0, 0, 0),
        d: civil::date(1999, 1, 8),
        t: civil::time(23, 59, 59, 999_999_000),
    };

    let _ = diesel::insert_into(schema::datetimes::table)
        .values(given)
        .execute(conn)?;

    let got = schema::datetimes::table
        .select(Row::as_select())
        .filter(schema::datetimes::id.eq(given.id))
        .first(conn)?;

    assert_eq!(given, got);

    Ok(())
}

/// Performs a round-trip with all of Jiff's nullable datetime types.
fn example_nullable_datetime_roundtrip(
    conn: &mut MysqlConnection,
) -> anyhow::Result<()> {
    use diesel::prelude::*;

    #[derive(
        Clone, Copy, Debug, PartialEq, Queryable, Insertable, Selectable,
    )]
    #[diesel(table_name = schema::nullable_datetimes)]
    #[diesel(check_for_backend(diesel::mysql::Mysql))]
    struct Row {
        id: i32,
        #[diesel(
            serialize_as = jiff_diesel::NullableTimestamp,
            deserialize_as = jiff_diesel::NullableTimestamp
        )]
        ts: Option<jiff::Timestamp>,
        #[diesel(
            serialize_as = jiff_diesel::NullableDateTime,
            deserialize_as = jiff_diesel::NullableDateTime
        )]
        dt: Option<jiff::civil::DateTime>,
        #[diesel(
            serialize_as = jiff_diesel::NullableDate,
            deserialize_as = jiff_diesel::NullableDate
        )]
        d: Option<jiff::civil::Date>,
        #[diesel(
            serialize_as = jiff_diesel::NullableTime,
            deserialize_as = jiff_diesel::NullableTime
        )]
        t: Option<jiff::civil::Time>,
    }

    let given = Row {
        id: 1,
        ts: Some("1970-01-01T00:00:00Z".parse()?),
        dt: Some(civil::date(2025, 7, 20).at(0, 0, 0, 0)),
        d: Some(civil::date(1999, 1, 8)),
        t: Some(civil::time(23, 59, 59, 999_999_000)),
    };

    let _ = diesel::insert_into(schema::nullable_datetimes::table)
        .values(given)
        .execute(conn)?;

    let got = schema::nullable_datetimes::table
        .select(Row::as_select())
        .filter(schema::nullable_datetimes::id.eq(given.id))
        .first(conn)?;

    assert_eq!(given, got);

    let given = Row { id: 2, ts: None, dt: None, d: None, t: None };

    let _ = diesel::insert_into(schema::nullable_datetimes::table)
        .values(given)
        .execute(conn)?;

    let got = schema::nullable_datetimes::table
        .select(Row::as_select())
        .filter(schema::nullable_datetimes::id.eq(given.id))
        .first(conn)?;

    assert_eq!(given, got);

    Ok(())
}

fn example_datetime_sql_query_roundtrip(
    conn: &mut MysqlConnection,
) -> anyhow::Result<()> {
    #[derive(Clone, Copy, Debug, PartialEq, QueryableByName)]
    #[diesel(table_name = schema::datetimes)]
    #[diesel(check_for_backend(diesel::mysql::Mysql))]
    struct Row {
        #[diesel(
            serialize_as = jiff_diesel::Timestamp,
            deserialize_as = jiff_diesel::Timestamp
        )]
        ts: jiff::Timestamp,
        #[diesel(
            serialize_as = jiff_diesel::DateTime,
            deserialize_as = jiff_diesel::DateTime
        )]
        dt: jiff::civil::DateTime,
        #[diesel(
            serialize_as = jiff_diesel::Date,
            deserialize_as = jiff_diesel::Date
        )]
        d: jiff::civil::Date,
        #[diesel(
            serialize_as = jiff_diesel::Time,
            deserialize_as = jiff_diesel::Time
        )]
        t: jiff::civil::Time,
    }

    let given = Row {
        ts: "1970-01-01T00:00:00Z".parse()?,
        dt: civil::date(2025, 7, 20).at(0, 0, 0, 0),
        d: civil::date(1999, 1, 8),
        t: civil::time(23, 59, 59, 999_999_000),
    };

    // We need to name the columns as Diesel's sql_query matches fields by name.
    let got = sql_query(
        "select
            CAST(? AS DATETIME) as ts,
            CAST(? AS DATETIME) as dt,
            CAST(? AS DATE) as d,
            CAST(? AS TIME(6)) as t
        ",
    )
    .bind::<sql_types::Datetime, _>(&given.ts.to_diesel())
    .bind::<sql_types::Timestamp, _>(&given.dt.to_diesel())
    .bind::<sql_types::Date, _>(&given.d.to_diesel())
    .bind::<sql_types::Time, _>(&given.t.to_diesel())
    .get_result(conn)?;
    assert_eq!(given, got);

    Ok(())
}
