/*!
This crate provides integration points for [Jiff](jiff) and [Diesel](diesel).

Examples can be found in the
[examples directory of the Jiff repository][examples].

Note that to use this crate, you'll likely need to enable one of its
[database backend features](#crate-features).

# Organization

This crates defines several types that wrap corresponding types in
Jiff. Each wrapper type provides implementations of traits found in
Diesel. For most types, these are the [`diesel::deserialize::Queryable`],
[`diesel::deserialize::FromSql`] and [`diesel::serialize::ToSql`] traits.

The intended workflow is to use these wrapper types within your wire types for
encoding and decoding data from databases such as PostgreSQL. The wrapper types
own the logic for encoding and decoding the data in database specific formats.

In order to the minimize the annoyance of wrapper types, the following
conveniences are afforded:

* A [`ToDiesel`] trait is provided. Several Jiff types implement this trait.
The trait provides easy conversion to the corresponding wrapper type in this
crate.
* A concrete `to_jiff` method is provided on each wrapper type. For example,
[`Timestamp::to_jiff`]. This method is the reverse of `ToDiesel`. This converts
from the wrapper type to the corresponding Jiff type.
* There are `From` trait implementations from the wrapper type to the
corresponding Jiff type, and vice versa.

Moreover, the types with a `Nullable` prefix are meant to be wrapper types
for optional values. For example, `NullableTimestamp` is a wrapper type for
`Option<jiff::Timestamp>`. [Diesel requires additional wrapper types to
express nullable values.][diesel-optional-wrapper-types]

# Database support

At present, MySQL, PostgreSQL and SQLite are supported.

# Future

This crate exists because there are generally only three ways to implement
the necessary traits in Diesel:

1. Make Jiff depend on Diesel, and implement the corresponding traits where
Jiff's types are defined.
2. Make Diesel depend on Jiff, and implement the corresponding traits where the
traits are defined.
3. Make a crate like this one with types that wrap Jiff's types, and implements
the corresponding traits for the wrapper types.

This was done because it seems inappropriate for a "lower level" crate like
Jiff to depend on Diesel. And while it might be appropriate for Diesel to
optionally depend on Jiff (like it does for [`chrono`] or [`time`]), at time of
writing, Jiff is still early in its life. It's totally reasonable to wait for
it to mature. Plus, the thought of three different datetime integrations is,
admittedly, tough to stomach.

In the future, it may be prudent for this crate to be upstreamed into Diesel
itself.

# Crate features

* **mysql** - Enables `diesel/mysql_backend`.
* **postgres** - Enables `diesel/postgres_backend`.
* **sqlite** - Enables `disel/sqlite`.

[examples]: https://github.com/BurntSushi/jiff/tree/master/examples
[`chrono`]: https://docs.rs/chrono
[`time`]: https://docs.rs/time
[diesel-optional-wrapper-types]: https://github.com/diesel-rs/diesel/discussions/4425
*/
#![deny(missing_docs)]

pub use self::nullable::{
    NullableDate, NullableDateTime, NullableSpan, NullableTime,
    NullableTimestamp,
};
pub use self::wrappers::{Date, DateTime, Span, Time, Timestamp, ToDiesel};

#[cfg(feature = "mysql")]
mod mysql;
mod nullable;
#[cfg(feature = "postgres")]
mod postgres;
#[cfg(feature = "sqlite")]
mod sqlite;
mod wrappers;
