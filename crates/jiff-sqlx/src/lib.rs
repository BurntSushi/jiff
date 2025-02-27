/*!
This crate provides integration points for [Jiff](jiff) and [SQLx][sqlx].

Examples can be found in the
[examples directory of the Jiff repository][examples].

Note that to use this crate, you'll likely need to enable one of its
[database backend features](#crate-features).

# Organization

This crates defines several types that wrap corresponding types in Jiff. Each
wrapper type provides implementations of traits found in SQLx. For most types,
these are the [`sqlx_core::types::Type`], [`sqlx_core::decode::Decode`] and
[`sqlx_core::encode::Encode`] traits.

The intended workflow is to use these wrapper types within your wire types for
encoding and decoding data from databases such as PostgreSQL. The wrapper types
own the logic for encoding and decoding the data in database specific formats.

In order to the minimize the annoyance of wrapper types, the following
conveniences are afforded:

* A [`ToSqlx`] trait is provided. Several Jiff types implement this trait. The
trait provides easy conversion to the corresponding wrapper type in this crate.
* A concrete `to_jiff` method is provided on each wrapper type. For example,
[`Timestamp::to_jiff`]. This method is the reverse of `ToSqlx`. This converts
from the wrapper type to the corresponding Jiff type.
* There are `From` trait implementations from the wrapper type to the
corresponding Jiff type, and vice versa.

# Database support

At present, both PostgreSQL and SQLite are supported.

Ideally, MySQL support would be present too, but it
[appears impossible until SQLx exposes some APIs][sqlx-mysql-bunk].

# Future

This crate exists because there are generally only three ways to implement
the necessary traits in SQLx:

1. Make Jiff depend on SQLx, and implement the corresponding traits where
Jiff's types are defined.
2. Make SQLx depend on Jiff, and implement the corresponding traits where the
traits are defined.
3. Make a crate like this one with types that wrap Jiff's types, and implements
the corresponding traits for the wrapper types.

This was done because it seems inappropriate for a "lower level" crate like
Jiff to depend on SQLx. And while it might be appropriate for SQLx to optionally
depend on Jiff (like it does for [`chrono`] or [`time`]), at time of writing,
Jiff is still early in its life. It's totally reasonable to wait for it to
mature. Plus, the thought of three different datetime integrations is,
admittedly, tough to stomach.

In the future, it may be prudent for this crate to be upstreamed into SQLx
itself.

# Crate features

* **postgres** - Enables the `sqlx-postgres` dependency.
* **sqlite** - Enables the `sqlx-sqlite` dependency.

[sqlx]: https://docs.rs/sqlx/0.8
[examples]: https://github.com/BurntSushi/jiff/tree/master/examples
[`chrono`]: https://docs.rs/chrono
[`time`]: https://docs.rs/time
[sqlx-mysql-bunk]: https://github.com/launchbadge/sqlx/issues/3487#issuecomment-2641843693
*/

#![deny(missing_docs)]

pub use self::wrappers::{Date, DateTime, Span, Time, Timestamp, ToSqlx};

#[cfg(feature = "postgres")]
mod postgres;
#[cfg(feature = "sqlite")]
mod sqlite;
mod wrappers;
