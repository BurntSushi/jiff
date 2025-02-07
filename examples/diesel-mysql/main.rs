use diesel::{
    connection::Connection, dsl::sql, mysql::MysqlConnection,
    query_dsl::RunQueryDsl, select, sql_types, ExpressionMethods,
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

    example_datetime_decode(&mut conn)?;
    example_datetime_encode(&mut conn)?;

    Ok(())
}

/// Performs a decoding with all of Jiff's datetime types.
fn example_datetime_decode(conn: &mut MysqlConnection) -> anyhow::Result<()> {
    // Decoding jiff::Timestamp
    let query = select(sql::<sql_types::Datetime>("'1970-01-01 00:00:00Z'"));
    let got: jiff_diesel::Timestamp = query.get_result(conn)?;
    let expected =
        "1970-01-01T00:00:00Z".parse::<jiff::Timestamp>()?.to_diesel();
    assert_eq!(expected, got);

    // Decoding jiff::civil::DateTime
    let query = select(sql::<sql_types::Timestamp>("'2025-07-20 00:00:00'"));
    let got: jiff_diesel::DateTime = query.get_result(conn)?;
    let expected = civil::date(2025, 7, 20).at(0, 0, 0, 0).to_diesel();
    assert_eq!(expected, got);

    // Decoding jiff::civil::Date
    let query = select(sql::<sql_types::Date>("'1999-01-08'"));
    let got: jiff_diesel::Date = query.get_result(conn)?;
    let expected = civil::date(1999, 1, 8).to_diesel();
    assert_eq!(expected, got);

    // Decoding with jiff::civil::Time
    let query = select(sql::<sql_types::Time>("'23:59:59.999999'"));
    let got: jiff_diesel::Time = query.get_result(conn)?;
    let expected = civil::time(23, 59, 59, 999_999_000).to_diesel();
    assert_eq!(expected, got);

    Ok(())
}

/// Performs a encoding with all of Jiff's datetime types.
fn example_datetime_encode(conn: &mut MysqlConnection) -> anyhow::Result<()> {
    // Encoding jiff::Timestamp
    let ts = "1970-01-01T00:00:01Z".parse::<jiff::Timestamp>()?.to_diesel();
    let query = select(
        sql::<sql_types::Datetime>("CAST('1970-01-01 00:00:01' AS DATETIME)")
            .eq(ts),
    );
    assert!(query.get_result::<bool>(conn)?);

    // Encoding jiff::civil::DateTime
    let dt = civil::date(2025, 7, 20).at(0, 0, 0, 0).to_diesel();
    let query = select(
        sql::<sql_types::Timestamp>("CAST('2025-07-20 00:00:00' AS DATETIME)")
            .eq(dt),
    );
    assert!(query.get_result::<bool>(conn)?);

    // Encoding jiff::civil::Date
    let date = civil::date(1999, 1, 8).to_diesel();
    let query =
        select(sql::<sql_types::Date>("CAST('1999-01-08' AS DATE)").eq(date));
    assert!(query.get_result::<bool>(conn)?);

    // Encoding jiff::civil::Time
    let time = civil::time(23, 59, 59, 999_999_000).to_diesel();
    let query = select(
        sql::<sql_types::Time>("CAST('23:59:59.999999' AS TIME(6))").eq(time),
    );
    assert!(query.get_result::<bool>(conn)?);

    Ok(())
}
