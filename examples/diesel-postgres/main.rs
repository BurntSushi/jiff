use diesel::{
    connection::Connection, dsl::sql, pg::PgConnection,
    query_dsl::RunQueryDsl, select, sql_query, sql_types, QueryableByName,
};
use jiff::civil;
use jiff_diesel::ToDiesel;

fn main() -> anyhow::Result<()> {
    let mut conn = PgConnection::establish(
        "postgres://postgres:password@localhost/test",
    )?;

    example_datetime_roundtrip(&mut conn)?;
    example_nullable_datetime_roundtrip(&mut conn)?;
    example_span_decode(&mut conn)?;
    example_time_zone_setting(&mut conn)?;

    Ok(())
}

/// Performs a round-trip with all of Jiff's datetime types.
fn example_datetime_roundtrip(conn: &mut PgConnection) -> anyhow::Result<()> {
    diesel::table! {
        datetimes {
            id -> Integer, // Diesel tables require an ID column.
            ts -> Timestamptz,
            dt -> Timestamp,
            d -> Date,
            t -> Time
        }
    }

    #[derive(Debug, PartialEq, QueryableByName)]
    #[diesel(table_name = datetimes)]
    #[diesel(check_for_backend(diesel::pg::Pg))]
    struct Row {
        #[diesel(deserialize_as = jiff_diesel::Timestamp)]
        ts: jiff::Timestamp,
        #[diesel(deserialize_as = jiff_diesel::DateTime)]
        dt: jiff::civil::DateTime,
        #[diesel(deserialize_as = jiff_diesel::Date)]
        d: jiff::civil::Date,
        #[diesel(deserialize_as = jiff_diesel::Time)]
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
            $1 as ts,
            $2 as dt,
            $3 as d,
            $4 as t
        ",
    )
    .bind::<sql_types::Timestamptz, _>(&given.ts.to_diesel())
    .bind::<sql_types::Timestamp, _>(&given.dt.to_diesel())
    .bind::<sql_types::Date, _>(&given.d.to_diesel())
    .bind::<sql_types::Time, _>(&given.t.to_diesel())
    .get_result(conn)?;
    assert_eq!(given, got);

    Ok(())
}

/// Performs a round-trip with all of Jiff's datetime types.
fn example_nullable_datetime_roundtrip(
    conn: &mut PgConnection,
) -> anyhow::Result<()> {
    diesel::table! {
        nullable_datetimes {
            id -> Integer, // Diesel tables require an ID column.
            ts -> Nullable<Timestamptz>,
            dt -> Nullable<Timestamp>,
            d -> Nullable<Date>,
            t -> Nullable<Time>
        }
    }

    #[derive(Debug, PartialEq, QueryableByName)]
    #[diesel(table_name = nullable_datetimes)]
    #[diesel(check_for_backend(diesel::pg::Pg))]
    struct Row {
        #[diesel(deserialize_as = jiff_diesel::NullableTimestamp)]
        ts: Option<jiff::Timestamp>,
        #[diesel(deserialize_as = jiff_diesel::NullableDateTime)]
        dt: Option<jiff::civil::DateTime>,
        #[diesel(deserialize_as = jiff_diesel::NullableDate)]
        d: Option<jiff::civil::Date>,
        #[diesel(deserialize_as = jiff_diesel::NullableTime)]
        t: Option<jiff::civil::Time>,
    }

    let given = Row {
        ts: Some("1970-01-01T00:00:00Z".parse()?),
        dt: Some(civil::date(2025, 7, 20).at(0, 0, 0, 0)),
        d: Some(civil::date(1999, 1, 8)),
        t: Some(civil::time(23, 59, 59, 999_999_000)),
    };

    // We need to name the columns as Diesel's sql_query matches fields by name.
    let got = sql_query(
        "select
            $1 as ts,
            $2 as dt,
            $3 as d,
            $4 as t
        ",
    )
    .bind::<sql_types::Nullable<sql_types::Timestamptz>, _>(
        &given.ts.to_diesel(),
    )
    .bind::<sql_types::Nullable<sql_types::Timestamp>, _>(
        &given.dt.to_diesel(),
    )
    .bind::<sql_types::Nullable<sql_types::Date>, _>(&given.d.to_diesel())
    .bind::<sql_types::Nullable<sql_types::Time>, _>(&given.t.to_diesel())
    .get_result(conn)?;
    assert_eq!(given, got);

    let given_null = Row { ts: None, dt: None, d: None, t: None };

    let got_null = sql_query("select $1 as ts, $2 as dt, $3 as d, $4 as t")
        .bind::<sql_types::Nullable<sql_types::Timestamptz>, _>(
            &given_null.ts.to_diesel(),
        )
        .bind::<sql_types::Nullable<sql_types::Timestamp>, _>(
            &given_null.dt.to_diesel(),
        )
        .bind::<sql_types::Nullable<sql_types::Date>, _>(
            &given_null.d.to_diesel(),
        )
        .bind::<sql_types::Nullable<sql_types::Time>, _>(
            &given_null.t.to_diesel(),
        )
        .get_result(conn)?;
    assert_eq!(given_null, got_null);

    Ok(())
}

/// Shows how to decode a PostgreSQL interval into a Jiff `Span`.
///
/// Jiff doesn't support encoding a `Span` as a PostgreSQL interval, but
/// Jiff can decode a PostgreSQL interval into a `Span`. The reason for this
/// is that encoding an arbitrary `Span` into a PostgreSQL interval requires
/// a relative datetime. Therefore, users wanting to store a `Span` will
/// need to explicitly use a `sqlx::postgres::types::PgInterval` at least at
/// encoding time.
fn example_span_decode(conn: &mut PgConnection) -> anyhow::Result<()> {
    let query = select(sql::<sql_types::Interval>(
        "'2 years 15 months 100 weeks 99 hours 123456789 milliseconds'::interval",
    ));
    let got: jiff_diesel::Span = query.get_result(conn)?;

    // The reason the span is in months/days/micros is because this
    // is how the interval is transmitted from PostgreSQL. Years and
    // months collapse into months, weeks and days collapses into days
    // and everything else collapses into microseconds. If you need to
    // preserve a `Span` as-is, then you'll need to encode it using Jiff's
    // "friendly" duration format.
    let span =
        jiff::Span::new().months(39).days(700).microseconds(479856789000i64);
    assert_eq!(span.fieldwise(), got.to_jiff());

    Ok(())
}

/// Demonstrates that PostgreSQL's time zone session setting doesn't fuck up
/// decoding.
///
/// This doesn't seem to trigger the same "text" decoding path that happens
/// in SQLx. No clue why. And the Diesel impls for datetime types don't seem
/// to have handling for text decoding, so maybe Diesel is doing something
/// that forces binary data. ¯\_(ツ)_/¯
///
/// Ref: https://github.com/launchbadge/sqlx/issues/703#issuecomment-939133588
fn example_time_zone_setting(conn: &mut PgConnection) -> anyhow::Result<()> {
    sql_query("SET TIME ZONE 'Australia/Tasmania'").execute(conn)?;

    let ts = "2020-01-01T05:01:01Z".parse::<jiff::Timestamp>()?.to_diesel();
    let query = select(sql::<sql_types::Timestamptz>(
        "'2020-01-01 05:01:01+00'::timestamp with time zone",
    ));
    let got: jiff_diesel::Timestamp = query.get_result(conn)?;
    assert_eq!(ts, got);

    let dt =
        "2020-01-01T05:01:01".parse::<jiff::civil::DateTime>()?.to_diesel();
    let query = select(sql::<sql_types::Timestamp>(
        "'2020-01-01 05:01:01+00'::timestamp without time zone",
    ));
    let got: jiff_diesel::DateTime = query.get_result(conn)?;
    assert_eq!(dt, got);

    Ok(())
}
