use diesel::{
    connection::Connection, mysql::MysqlConnection, query_dsl::RunQueryDsl,
    sql_query, sql_types, QueryableByName,
};
use jiff::civil;
use jiff_diesel::ToDiesel;

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

    example_datetime_roundtrip(&mut conn)?;

    Ok(())
}

/// Performs a round-trip with all of Jiff's datetime types.
fn example_datetime_roundtrip(
    conn: &mut MysqlConnection,
) -> anyhow::Result<()> {
    diesel::table! {
        jiffs {
            id -> Integer, // Diesel tables require an ID column.
            ts -> Datetime,
            dt -> Timestamp,
            d -> Date,
            t -> Time
        }
    }

    #[derive(Debug, PartialEq, QueryableByName)]
    #[diesel(check_for_backend(diesel::mysql::Mysql))]
    struct Jiff {
        #[diesel(deserialize_as = jiff_diesel::Timestamp)]
        pub ts: jiff::Timestamp,
        #[diesel(deserialize_as = jiff_diesel::DateTime)]
        pub dt: jiff::civil::DateTime,
        #[diesel(deserialize_as = jiff_diesel::Date)]
        pub d: jiff::civil::Date,
        #[diesel(deserialize_as = jiff_diesel::Time)]
        pub t: jiff::civil::Time,
    }

    let given = Jiff {
        ts: "1970-01-01T00:00:00Z".parse()?,
        dt: civil::date(2025, 7, 20).at(0, 0, 0, 0),
        d: civil::date(1999, 1, 8),
        t: civil::time(23, 59, 59, 999_999_000),
    };

    // We need to name the columns as Diesel's sql_query matches fields by name.
    let got = sql_query(
        "select CAST(? AS DATETIME) as ts, CAST(? AS DATETIME) as dt, CAST(? AS DATE) as d, CAST(? AS TIME(6)) as t",
    )
    .bind::<sql_types::Datetime, _>(&given.ts.to_diesel())
    .bind::<sql_types::Timestamp, _>(&given.dt.to_diesel())
    .bind::<sql_types::Date, _>(&given.d.to_diesel())
    .bind::<sql_types::Time, _>(&given.t.to_diesel())
    .get_result(conn)?;
    assert_eq!(given, got);

    Ok(())
}
