/*!
This example demonstrate's a footgun with Diesel's default setup for
PostgreSQL's `TIMESTAMP WITHOUT TIME ZONE`.

Specifically, Diesel permits deserializing a `TIMESTAMP WITHOUT TIME ZONE`
value into a `std::time::SystemTime`. The latter is a true timestamp type
corresponding to a real physical instant in time. The former is actually a
local time, where any time zone offset information associated with it is
completely ignored at insertion time. Therefore, trying to read it as a real
Unix timestamp will fail if the data in the database were local times.

The two row types below are used to demonstrate a more complicated scenario
where one is trying to read local times from a database as if they were
timestamps. In a very small example like this, it looks somewhat ham-fisted: we
should just use the same type! Indeed, if you do, you aren't as likely to run
into problems. That's because this is a short example meant to demonstrate how
a bigger program *could* go wrong.

Unfortunately, the inverse of this footgun is also possible if you're using
`chrono` or `time`. For example, Diesel lets one deserialize
`TIMESTAMP WITH TIME ZONE` values directly into a `chrono::NaiveDateTime`:
<https://github.com/diesel-rs/diesel/blob/edd7bd32f52a52f3f451a0fd9820fc8dcf8342a8/diesel/src/pg/types/date_and_time/chrono.rs#L50-L62>
That means Diesel will let you deserialize a local time from a value that is
always in UTC, virtually guaranteeing an unintended result.

In contrast, the `jiff-diesel` integration crate specifically keeps these
concepts separate. If you have a `TIMESTAMP WITHOUT TIME ZONE`, then you can
only deserialize into a `jiff::civil::DateTime` and _not_ a `jiff::Timestamp`.
(Although you can still deserialize into a `std::time::SystemTime`. Jiff can't
do anything to stop that. Diesel would need to remove the impl in its next
semver incompatible release.) Conversely, if you have a
`TIMESTAMP WITH TIME ZONE`, then you can only deserialize into a
`jiff::Timestamp` and _not_ a `jiff::civil::DateTime`.

Now how common is this sort of footgun? I'm not sure. At minimum, it could
lead to extra confusion about the distinction between PostgreSQL's timestamp
types. It's already quite confusing because `TIMESTAMP WITHOUT TIME ZONE` is
*not* actually a timestamp.

This came up in discussion here:
https://github.com/BurntSushi/jiff/pull/509

See also this Stack Overflow question that might also help:
https://stackoverflow.com/questions/5876218/difference-between-timestamps-with-without-time-zone-in-postgresql

N.B. "civil" and "local" mean the same thing.
*/

use diesel::prelude::*;
use diesel::{
    connection::Connection, pg::PgConnection, query_dsl::RunQueryDsl,
    sql_query,
};
use jiff::civil;

mod schema {
    diesel::table! {
        datetimes {
            id -> Integer, // Diesel tables require an ID column.
            dt -> Timestamp,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Queryable, Insertable, Selectable)]
#[diesel(table_name = schema::datetimes)]
#[diesel(check_for_backend(diesel::pg::Pg))]
struct RowInsert {
    /// We insert local datetimes.
    #[diesel(
        serialize_as = jiff_diesel::DateTime,
        deserialize_as = jiff_diesel::DateTime
    )]
    dt: jiff::civil::DateTime,
}

#[derive(Clone, Copy, Debug, PartialEq, Queryable, Insertable, Selectable)]
#[diesel(table_name = schema::datetimes)]
#[diesel(check_for_backend(diesel::pg::Pg))]
struct RowSelect {
    /// We select the data as a timestamp, even if it isn't an actual
    /// timestamp.
    dt: std::time::SystemTime,
}

fn main() -> anyhow::Result<()> {
    use schema::datetimes::dsl::*;

    let mut conn = PgConnection::establish(
        "postgres://postgres:password@localhost/test",
    )?;

    sql_query(
        "CREATE TEMPORARY TABLE IF NOT EXISTS datetimes (
            id integer primary key generated always as identity,
            dt timestamp not null
        )",
    )
    .execute(&mut conn)
    .unwrap();

    // Let's say a local time in my time zone (America/New_York, in summer,
    // so -4 hours from UTC) was inserted. This corresponds to the timestamp
    // `2025-07-20T21:30:00Z`. Or `1753047000` seconds since the Unix epoch.
    let given = RowInsert { dt: civil::date(2025, 7, 20).at(17, 30, 0, 0) };
    diesel::insert_into(schema::datetimes::table)
        .values(given)
        .execute(&mut conn)?;

    // Since Diesel permits deserializing a PostgreSQL
    // `TIMESTAMP WITHOUT TIME ZONE` value into a `std::time::SystemTime`,
    // we can select right into.
    let results =
        datetimes.limit(1).select(RowSelect::as_select()).load(&mut conn)?;
    let got = results.get(0).ok_or_else(|| anyhow::anyhow!("no results"))?;

    // Now let's convert the system time to a Jiff timestamp so that we can
    // look at it:
    let timestamp = jiff::Timestamp::try_from(got.dt)?;
    // And now look at the timestamp we get back:
    assert_eq!(timestamp.to_string(), "2025-07-20T17:30:00Z");
    // It's not equivalent to `2025-07-20T21:30:00Z`, which is the time that
    // we started with. This happens because `TIMESTAMP WITHOUT TIME ZONE`
    // stores the datetime given *as is* and drops any offset information.
    // The only way to re-capture the original local time is to undo the
    // implicit transformation we made originally:
    let datetime = timestamp.to_zoned(jiff::tz::TimeZone::UTC).datetime();
    assert_eq!(datetime.to_string(), "2025-07-20T17:30:00");
    // And if we want to capture the original instant in time, we have to know
    // to convert this civil datetime back to UTC using the original offset:
    let timestamp = datetime
        .to_zoned(jiff::tz::TimeZone::fixed(jiff::tz::Offset::from_hours(
            -4,
        )?))?
        .timestamp();
    assert_eq!(timestamp.to_string(), "2025-07-20T21:30:00Z");

    // The fundamental problem here is that Diesel permits deserializing a
    // local time into a timestamp type. If you're *always* careful to undo
    // the transformation given, or always use UTC on the way in and out
    // (e.g., always use `std::time::SystemTime`), then you won't run into
    // problems. But if there's data in the database corresponding to local
    // datetimes and you try to read it with a `SystemTime`, you're almost
    // certainly going to get garbage results.

    Ok(())
}
