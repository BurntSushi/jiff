/*!
This module provides helpers to use with [Serde].

The helpers are exposed as modules meant to be used with
Serde's [`with` attribute].

At present, the helpers are limited to serializing and deserializing
[`Timestamp`](crate::Timestamp) values as an integer number of seconds,
milliseconds, microseconds or nanoseconds.

# Module hierarchy

The available helpers can be more quickly understood by looking at a fully
rendered tree of this module's hierarchy. Only the leaves of the tree are
usable with Serde's `with` attribute. For each leaf, the full path is spelled
out for easy copy & paste.

* [`timestamp`]
    * [`second`](self::timestamp::second)
        * [`jiff::fmt::serde::timestamp::second::required`](self::timestamp::second::required)
        * [`jiff::fmt::serde::timestamp::second::optional`](self::timestamp::second::optional)
    * [`millisecond`](self::timestamp::millisecond)
        * [`jiff::fmt::serde::timestamp::millisecond::required`](self::timestamp::millisecond::required)
        * [`jiff::fmt::serde::timestamp::millisecond::optional`](self::timestamp::millisecond::optional)
    * [`microsecond`](self::timestamp::millisecond)
        * [`jiff::fmt::serde::timestamp::microsecond::required`](self::timestamp::microsecond::required)
        * [`jiff::fmt::serde::timestamp::microsecond::optional`](self::timestamp::microsecond::optional)
    * [`nanosecond`](self::timestamp::millisecond)
        * [`jiff::fmt::serde::timestamp::nanosecond::required`](self::timestamp::nanosecond::required)
        * [`jiff::fmt::serde::timestamp::nanosecond::optional`](self::timestamp::nanosecond::optional)

# Advice

In general, these helpers should only be used to interface with "legacy" APIs
that transmit times as integer number of seconds (or milliseconds or whatever).
If you're designing a new API and need to transmit instants in time that don't
care about time zones, then you should use `Timestamp` directly. It will
automatically use RFC 3339. (And if you do want to include the time zone, then
using [`Zoned`](crate::Zoned) directly will work as well by utilizing the
RFC 9557 extension to RFC 3339.)

# Example

This example shows how to deserialize an integer number of seconds since the
Unix epoch into a [`Timestamp`](crate::Timestamp). And the reverse operation
for serialization:

```
use jiff::Timestamp;

#[derive(Debug, serde::Deserialize, serde::Serialize)]
struct Record {
    #[serde(with = "jiff::fmt::serde::timestamp::second::required")]
    timestamp: Timestamp,
}

let json = r#"{"timestamp":1517644800}"#;
let got: Record = serde_json::from_str(&json)?;
assert_eq!(got.timestamp, Timestamp::from_second(1517644800)?);
assert_eq!(serde_json::to_string(&got)?, json);

# Ok::<(), Box<dyn std::error::Error>>(())
```

# Example: optional support

And this example shows how to use an `Option<Timestamp>` instead of a
`Timestamp`. Note that in this case, we show how to roundtrip the number of
**milliseconds** since the Unix epoch:

```
use jiff::Timestamp;

#[derive(Debug, serde::Deserialize, serde::Serialize)]
struct Record {
    #[serde(with = "jiff::fmt::serde::timestamp::millisecond::optional")]
    timestamp: Option<Timestamp>,
}

let json = r#"{"timestamp":1517644800123}"#;
let got: Record = serde_json::from_str(&json)?;
assert_eq!(got.timestamp, Some(Timestamp::from_millisecond(1517644800_123)?));
assert_eq!(serde_json::to_string(&got)?, json);

# Ok::<(), Box<dyn std::error::Error>>(())
```

[Serde]: https://serde.rs/
[`with` attribute]: https://serde.rs/field-attrs.html#with
*/

/// Convenience routines for (de)serializing [`Timestamp`](crate::Timestamp) as
/// raw integer values.
pub mod timestamp {
    use serde::de;

    /// A generic visitor for `Option<Timestamp>`.
    struct OptionalVisitor<V>(V);

    impl<'de, V: de::Visitor<'de, Value = crate::Timestamp>> de::Visitor<'de>
        for OptionalVisitor<V>
    {
        type Value = Option<crate::Timestamp>;

        fn expecting(
            &self,
            f: &mut core::fmt::Formatter,
        ) -> core::fmt::Result {
            f.write_str(
                "an integer number of seconds from the Unix epoch or `None`",
            )
        }

        #[inline]
        fn visit_some<D: de::Deserializer<'de>>(
            self,
            de: D,
        ) -> Result<Option<crate::Timestamp>, D::Error> {
            de.deserialize_i64(self.0).map(Some)
        }

        #[inline]
        fn visit_none<E: de::Error>(
            self,
        ) -> Result<Option<crate::Timestamp>, E> {
            Ok(None)
        }
    }

    /// (De)serialize an integer number of seconds from the Unix epoch.
    pub mod second {
        use serde::de;

        struct Visitor;

        impl<'de> de::Visitor<'de> for Visitor {
            type Value = crate::Timestamp;

            fn expecting(
                &self,
                f: &mut core::fmt::Formatter,
            ) -> core::fmt::Result {
                f.write_str("an integer number of seconds from the Unix epoch")
            }

            #[inline]
            fn visit_i8<E: de::Error>(
                self,
                v: i8,
            ) -> Result<crate::Timestamp, E> {
                self.visit_i64(i64::from(v))
            }

            #[inline]
            fn visit_u8<E: de::Error>(
                self,
                v: u8,
            ) -> Result<crate::Timestamp, E> {
                self.visit_i64(i64::from(v))
            }

            #[inline]
            fn visit_i16<E: de::Error>(
                self,
                v: i16,
            ) -> Result<crate::Timestamp, E> {
                self.visit_i64(i64::from(v))
            }

            #[inline]
            fn visit_u16<E: de::Error>(
                self,
                v: u16,
            ) -> Result<crate::Timestamp, E> {
                self.visit_i64(i64::from(v))
            }

            #[inline]
            fn visit_i32<E: de::Error>(
                self,
                v: i32,
            ) -> Result<crate::Timestamp, E> {
                self.visit_i64(i64::from(v))
            }

            #[inline]
            fn visit_u32<E: de::Error>(
                self,
                v: u32,
            ) -> Result<crate::Timestamp, E> {
                self.visit_i64(i64::from(v))
            }

            #[inline]
            fn visit_i64<E: de::Error>(
                self,
                v: i64,
            ) -> Result<crate::Timestamp, E> {
                crate::Timestamp::from_second(v).map_err(de::Error::custom)
            }

            #[inline]
            fn visit_u64<E: de::Error>(
                self,
                v: u64,
            ) -> Result<crate::Timestamp, E> {
                let v = i64::try_from(v).map_err(|_| {
                    de::Error::custom(alloc::format!(
                        "got unsigned integer {v} seconds, \
                         which is too big to fit in a Jiff `Timestamp`",
                    ))
                })?;
                self.visit_i64(v)
            }

            #[inline]
            fn visit_i128<E: de::Error>(
                self,
                v: i128,
            ) -> Result<crate::Timestamp, E> {
                let v = i64::try_from(v).map_err(|_| {
                    de::Error::custom(alloc::format!(
                        "got signed integer {v} seconds, \
                         which is too big to fit in a Jiff `Timestamp`",
                    ))
                })?;
                self.visit_i64(v)
            }

            #[inline]
            fn visit_u128<E: de::Error>(
                self,
                v: u128,
            ) -> Result<crate::Timestamp, E> {
                let v = i64::try_from(v).map_err(|_| {
                    de::Error::custom(alloc::format!(
                        "got unsigned integer {v} seconds, \
                         which is too big to fit in a Jiff `Timestamp`",
                    ))
                })?;
                self.visit_i64(v)
            }
        }

        /// (De)serialize a required integer number of seconds from the Unix
        /// epoch.
        pub mod required {
            /// Serialize a required integer number of seconds since the Unix
            /// epoch.
            #[inline]
            pub fn serialize<S: serde::Serializer>(
                timestamp: &crate::Timestamp,
                se: S,
            ) -> Result<S::Ok, S::Error> {
                se.serialize_i64(timestamp.as_second())
            }

            /// Deserialize a required integer number of seconds since the
            /// Unix epoch.
            #[inline]
            pub fn deserialize<'de, D: serde::Deserializer<'de>>(
                de: D,
            ) -> Result<crate::Timestamp, D::Error> {
                de.deserialize_i64(super::Visitor)
            }
        }

        /// (De)serialize an optional integer number of seconds from the Unix
        /// epoch.
        pub mod optional {
            /// Serialize an optional integer number of seconds since the Unix
            /// epoch.
            #[inline]
            pub fn serialize<S: serde::Serializer>(
                timestamp: &Option<crate::Timestamp>,
                se: S,
            ) -> Result<S::Ok, S::Error> {
                match *timestamp {
                    None => se.serialize_none(),
                    Some(ts) => se.serialize_i64(ts.as_second()),
                }
            }

            /// Deserialize an optional integer number of seconds since the
            /// Unix epoch.
            #[inline]
            pub fn deserialize<'de, D: serde::Deserializer<'de>>(
                de: D,
            ) -> Result<Option<crate::Timestamp>, D::Error> {
                de.deserialize_option(super::super::OptionalVisitor(
                    super::Visitor,
                ))
            }
        }
    }

    /// (De)serialize an integer number of milliseconds from the Unix epoch.
    pub mod millisecond {
        use serde::de;

        struct Visitor;

        impl<'de> de::Visitor<'de> for Visitor {
            type Value = crate::Timestamp;

            fn expecting(
                &self,
                f: &mut core::fmt::Formatter,
            ) -> core::fmt::Result {
                f.write_str(
                    "an integer number of milliseconds from the Unix epoch",
                )
            }

            #[inline]
            fn visit_i8<E: de::Error>(
                self,
                v: i8,
            ) -> Result<crate::Timestamp, E> {
                self.visit_i64(i64::from(v))
            }

            #[inline]
            fn visit_u8<E: de::Error>(
                self,
                v: u8,
            ) -> Result<crate::Timestamp, E> {
                self.visit_i64(i64::from(v))
            }

            #[inline]
            fn visit_i16<E: de::Error>(
                self,
                v: i16,
            ) -> Result<crate::Timestamp, E> {
                self.visit_i64(i64::from(v))
            }

            #[inline]
            fn visit_u16<E: de::Error>(
                self,
                v: u16,
            ) -> Result<crate::Timestamp, E> {
                self.visit_i64(i64::from(v))
            }

            #[inline]
            fn visit_i32<E: de::Error>(
                self,
                v: i32,
            ) -> Result<crate::Timestamp, E> {
                self.visit_i64(i64::from(v))
            }

            #[inline]
            fn visit_u32<E: de::Error>(
                self,
                v: u32,
            ) -> Result<crate::Timestamp, E> {
                self.visit_i64(i64::from(v))
            }

            #[inline]
            fn visit_i64<E: de::Error>(
                self,
                v: i64,
            ) -> Result<crate::Timestamp, E> {
                crate::Timestamp::from_millisecond(v)
                    .map_err(de::Error::custom)
            }

            #[inline]
            fn visit_u64<E: de::Error>(
                self,
                v: u64,
            ) -> Result<crate::Timestamp, E> {
                let v = i64::try_from(v).map_err(|_| {
                    de::Error::custom(alloc::format!(
                        "got unsigned integer {v} milliseconds, \
                         which is too big to fit in a Jiff `Timestamp`",
                    ))
                })?;
                self.visit_i64(v)
            }

            #[inline]
            fn visit_i128<E: de::Error>(
                self,
                v: i128,
            ) -> Result<crate::Timestamp, E> {
                let v = i64::try_from(v).map_err(|_| {
                    de::Error::custom(alloc::format!(
                        "got signed integer {v} milliseconds, \
                         which is too big to fit in a Jiff `Timestamp`",
                    ))
                })?;
                self.visit_i64(v)
            }

            #[inline]
            fn visit_u128<E: de::Error>(
                self,
                v: u128,
            ) -> Result<crate::Timestamp, E> {
                let v = i64::try_from(v).map_err(|_| {
                    de::Error::custom(alloc::format!(
                        "got unsigned integer {v} milliseconds, \
                         which is too big to fit in a Jiff `Timestamp`",
                    ))
                })?;
                self.visit_i64(v)
            }
        }

        /// (De)serialize a required integer number of milliseconds from the
        /// Unix epoch.
        pub mod required {
            /// Serialize a required integer number of milliseconds since the
            /// Unix epoch.
            #[inline]
            pub fn serialize<S: serde::Serializer>(
                timestamp: &crate::Timestamp,
                se: S,
            ) -> Result<S::Ok, S::Error> {
                se.serialize_i64(timestamp.as_millisecond())
            }

            /// Deserialize a required integer number of milliseconds since the
            /// Unix epoch.
            #[inline]
            pub fn deserialize<'de, D: serde::Deserializer<'de>>(
                de: D,
            ) -> Result<crate::Timestamp, D::Error> {
                de.deserialize_i64(super::Visitor)
            }
        }

        /// (De)serialize an optional integer number of milliseconds from the
        /// Unix epoch.
        pub mod optional {
            /// Serialize an optional integer number of milliseconds since the
            /// Unix epoch.
            #[inline]
            pub fn serialize<S: serde::Serializer>(
                timestamp: &Option<crate::Timestamp>,
                se: S,
            ) -> Result<S::Ok, S::Error> {
                match *timestamp {
                    None => se.serialize_none(),
                    Some(ts) => se.serialize_i64(ts.as_millisecond()),
                }
            }

            /// Deserialize an optional integer number of milliseconds since
            /// the Unix epoch.
            #[inline]
            pub fn deserialize<'de, D: serde::Deserializer<'de>>(
                de: D,
            ) -> Result<Option<crate::Timestamp>, D::Error> {
                de.deserialize_option(super::super::OptionalVisitor(
                    super::Visitor,
                ))
            }
        }
    }

    /// (De)serialize an integer number of microseconds from the Unix epoch.
    pub mod microsecond {
        use serde::de;

        struct Visitor;

        impl<'de> de::Visitor<'de> for Visitor {
            type Value = crate::Timestamp;

            fn expecting(
                &self,
                f: &mut core::fmt::Formatter,
            ) -> core::fmt::Result {
                f.write_str(
                    "an integer number of microseconds from the Unix epoch",
                )
            }

            #[inline]
            fn visit_i8<E: de::Error>(
                self,
                v: i8,
            ) -> Result<crate::Timestamp, E> {
                self.visit_i64(i64::from(v))
            }

            #[inline]
            fn visit_u8<E: de::Error>(
                self,
                v: u8,
            ) -> Result<crate::Timestamp, E> {
                self.visit_i64(i64::from(v))
            }

            #[inline]
            fn visit_i16<E: de::Error>(
                self,
                v: i16,
            ) -> Result<crate::Timestamp, E> {
                self.visit_i64(i64::from(v))
            }

            #[inline]
            fn visit_u16<E: de::Error>(
                self,
                v: u16,
            ) -> Result<crate::Timestamp, E> {
                self.visit_i64(i64::from(v))
            }

            #[inline]
            fn visit_i32<E: de::Error>(
                self,
                v: i32,
            ) -> Result<crate::Timestamp, E> {
                self.visit_i64(i64::from(v))
            }

            #[inline]
            fn visit_u32<E: de::Error>(
                self,
                v: u32,
            ) -> Result<crate::Timestamp, E> {
                self.visit_i64(i64::from(v))
            }

            #[inline]
            fn visit_i64<E: de::Error>(
                self,
                v: i64,
            ) -> Result<crate::Timestamp, E> {
                crate::Timestamp::from_microsecond(v)
                    .map_err(de::Error::custom)
            }

            #[inline]
            fn visit_u64<E: de::Error>(
                self,
                v: u64,
            ) -> Result<crate::Timestamp, E> {
                let v = i64::try_from(v).map_err(|_| {
                    de::Error::custom(alloc::format!(
                        "got unsigned integer {v} microseconds, \
                         which is too big to fit in a Jiff `Timestamp`",
                    ))
                })?;
                self.visit_i64(v)
            }

            #[inline]
            fn visit_i128<E: de::Error>(
                self,
                v: i128,
            ) -> Result<crate::Timestamp, E> {
                let v = i64::try_from(v).map_err(|_| {
                    de::Error::custom(alloc::format!(
                        "got signed integer {v} microseconds, \
                         which is too big to fit in a Jiff `Timestamp`",
                    ))
                })?;
                self.visit_i64(v)
            }

            #[inline]
            fn visit_u128<E: de::Error>(
                self,
                v: u128,
            ) -> Result<crate::Timestamp, E> {
                let v = i64::try_from(v).map_err(|_| {
                    de::Error::custom(alloc::format!(
                        "got unsigned integer {v} microseconds, \
                         which is too big to fit in a Jiff `Timestamp`",
                    ))
                })?;
                self.visit_i64(v)
            }
        }

        /// (De)serialize a required integer number of microseconds from the
        /// Unix epoch.
        pub mod required {
            /// Serialize a required integer number of microseconds since the
            /// Unix epoch.
            #[inline]
            pub fn serialize<S: serde::Serializer>(
                timestamp: &crate::Timestamp,
                se: S,
            ) -> Result<S::Ok, S::Error> {
                se.serialize_i64(timestamp.as_microsecond())
            }

            /// Deserialize a required integer number of microseconds since the
            /// Unix epoch.
            #[inline]
            pub fn deserialize<'de, D: serde::Deserializer<'de>>(
                de: D,
            ) -> Result<crate::Timestamp, D::Error> {
                de.deserialize_i64(super::Visitor)
            }
        }

        /// (De)serialize an optional integer number of microseconds from the
        /// Unix epoch.
        pub mod optional {
            /// Serialize an optional integer number of microseconds since the
            /// Unix epoch.
            #[inline]
            pub fn serialize<S: serde::Serializer>(
                timestamp: &Option<crate::Timestamp>,
                se: S,
            ) -> Result<S::Ok, S::Error> {
                match *timestamp {
                    None => se.serialize_none(),
                    Some(ts) => se.serialize_i64(ts.as_microsecond()),
                }
            }

            /// Deserialize an optional integer number of microseconds since
            /// the Unix epoch.
            #[inline]
            pub fn deserialize<'de, D: serde::Deserializer<'de>>(
                de: D,
            ) -> Result<Option<crate::Timestamp>, D::Error> {
                de.deserialize_option(super::super::OptionalVisitor(
                    super::Visitor,
                ))
            }
        }
    }

    /// (De)serialize an integer number of nanoseconds from the Unix epoch.
    pub mod nanosecond {
        use serde::de;

        struct Visitor;

        impl<'de> de::Visitor<'de> for Visitor {
            type Value = crate::Timestamp;

            fn expecting(
                &self,
                f: &mut core::fmt::Formatter,
            ) -> core::fmt::Result {
                f.write_str(
                    "an integer number of nanoseconds from the Unix epoch",
                )
            }

            #[inline]
            fn visit_i64<E: de::Error>(
                self,
                v: i64,
            ) -> Result<crate::Timestamp, E> {
                self.visit_i128(i128::from(v))
            }

            #[inline]
            fn visit_u64<E: de::Error>(
                self,
                v: u64,
            ) -> Result<crate::Timestamp, E> {
                self.visit_u128(u128::from(v))
            }

            #[inline]
            fn visit_i128<E: de::Error>(
                self,
                v: i128,
            ) -> Result<crate::Timestamp, E> {
                crate::Timestamp::from_nanosecond(v).map_err(de::Error::custom)
            }

            #[inline]
            fn visit_u128<E: de::Error>(
                self,
                v: u128,
            ) -> Result<crate::Timestamp, E> {
                let v = i128::try_from(v).map_err(|_| {
                    de::Error::custom(alloc::format!(
                        "got unsigned integer {v} nanoseconds, \
                         which is too big to fit in a Jiff `Timestamp`",
                    ))
                })?;
                self.visit_i128(v)
            }
        }

        /// (De)serialize a required integer number of nanoseconds from the
        /// Unix epoch.
        pub mod required {
            /// Serialize a required integer number of nanoseconds since the
            /// Unix epoch.
            #[inline]
            pub fn serialize<S: serde::Serializer>(
                timestamp: &crate::Timestamp,
                se: S,
            ) -> Result<S::Ok, S::Error> {
                se.serialize_i128(timestamp.as_nanosecond())
            }

            /// Deserialize a required integer number of nanoseconds since the
            /// Unix epoch.
            #[inline]
            pub fn deserialize<'de, D: serde::Deserializer<'de>>(
                de: D,
            ) -> Result<crate::Timestamp, D::Error> {
                de.deserialize_i128(super::Visitor)
            }
        }

        /// (De)serialize an optional integer number of nanoseconds from the
        /// Unix epoch.
        pub mod optional {
            /// Serialize an optional integer number of nanoseconds since the
            /// Unix epoch.
            #[inline]
            pub fn serialize<S: serde::Serializer>(
                timestamp: &Option<crate::Timestamp>,
                se: S,
            ) -> Result<S::Ok, S::Error> {
                match *timestamp {
                    None => se.serialize_none(),
                    Some(ts) => se.serialize_i128(ts.as_nanosecond()),
                }
            }

            /// Deserialize an optional integer number of nanoseconds since the
            /// Unix epoch.
            #[inline]
            pub fn deserialize<'de, D: serde::Deserializer<'de>>(
                de: D,
            ) -> Result<Option<crate::Timestamp>, D::Error> {
                de.deserialize_option(super::super::OptionalVisitor(
                    super::Visitor,
                ))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::Timestamp;

    #[test]
    fn timestamp_second_required() {
        #[derive(Debug, serde::Deserialize, serde::Serialize)]
        struct Data {
            #[serde(with = "crate::fmt::serde::timestamp::second::required")]
            ts: Timestamp,
        }

        let json = r#"{"ts":1517644800}"#;
        let got: Data = serde_json::from_str(&json).unwrap();
        assert_eq!(got.ts, Timestamp::from_second(1517644800).unwrap());
        assert_eq!(serde_json::to_string(&got).unwrap(), json);
    }

    #[test]
    fn timestamp_second_optional() {
        #[derive(Debug, serde::Deserialize, serde::Serialize)]
        struct Data {
            #[serde(with = "crate::fmt::serde::timestamp::second::optional")]
            ts: Option<Timestamp>,
        }

        let json = r#"{"ts":1517644800}"#;
        let got: Data = serde_json::from_str(&json).unwrap();
        assert_eq!(got.ts, Some(Timestamp::from_second(1517644800).unwrap()));
        assert_eq!(serde_json::to_string(&got).unwrap(), json);
    }

    #[test]
    fn timestamp_millisecond_required() {
        #[derive(Debug, serde::Deserialize, serde::Serialize)]
        struct Data {
            #[serde(
                with = "crate::fmt::serde::timestamp::millisecond::required"
            )]
            ts: Timestamp,
        }

        let json = r#"{"ts":1517644800000}"#;
        let got: Data = serde_json::from_str(&json).unwrap();
        assert_eq!(
            got.ts,
            Timestamp::from_millisecond(1517644800_000).unwrap()
        );
        assert_eq!(serde_json::to_string(&got).unwrap(), json);

        let json = r#"{"ts":1517644800123}"#;
        let got: Data = serde_json::from_str(&json).unwrap();
        assert_eq!(
            got.ts,
            Timestamp::from_millisecond(1517644800_123).unwrap()
        );
        assert_eq!(serde_json::to_string(&got).unwrap(), json);
    }

    #[test]
    fn timestamp_millisecond_optional() {
        #[derive(Debug, serde::Deserialize, serde::Serialize)]
        struct Data {
            #[serde(
                with = "crate::fmt::serde::timestamp::millisecond::optional"
            )]
            ts: Option<Timestamp>,
        }

        let json = r#"{"ts":1517644800000}"#;
        let got: Data = serde_json::from_str(&json).unwrap();
        assert_eq!(
            got.ts,
            Some(Timestamp::from_millisecond(1517644800_000).unwrap())
        );
        assert_eq!(serde_json::to_string(&got).unwrap(), json);

        let json = r#"{"ts":1517644800123}"#;
        let got: Data = serde_json::from_str(&json).unwrap();
        assert_eq!(
            got.ts,
            Some(Timestamp::from_millisecond(1517644800_123).unwrap())
        );
        assert_eq!(serde_json::to_string(&got).unwrap(), json);
    }

    #[test]
    fn timestamp_microsecond_required() {
        #[derive(Debug, serde::Deserialize, serde::Serialize)]
        struct Data {
            #[serde(
                with = "crate::fmt::serde::timestamp::microsecond::required"
            )]
            ts: Timestamp,
        }

        let json = r#"{"ts":1517644800000000}"#;
        let got: Data = serde_json::from_str(&json).unwrap();
        assert_eq!(
            got.ts,
            Timestamp::from_microsecond(1517644800_000000).unwrap()
        );
        assert_eq!(serde_json::to_string(&got).unwrap(), json);

        let json = r#"{"ts":1517644800123456}"#;
        let got: Data = serde_json::from_str(&json).unwrap();
        assert_eq!(
            got.ts,
            Timestamp::from_microsecond(1517644800_123456).unwrap()
        );
        assert_eq!(serde_json::to_string(&got).unwrap(), json);
    }

    #[test]
    fn timestamp_microsecond_optional() {
        #[derive(Debug, serde::Deserialize, serde::Serialize)]
        struct Data {
            #[serde(
                with = "crate::fmt::serde::timestamp::microsecond::optional"
            )]
            ts: Option<Timestamp>,
        }

        let json = r#"{"ts":1517644800000000}"#;
        let got: Data = serde_json::from_str(&json).unwrap();
        assert_eq!(
            got.ts,
            Some(Timestamp::from_microsecond(1517644800_000000).unwrap())
        );
        assert_eq!(serde_json::to_string(&got).unwrap(), json);

        let json = r#"{"ts":1517644800123456}"#;
        let got: Data = serde_json::from_str(&json).unwrap();
        assert_eq!(
            got.ts,
            Some(Timestamp::from_microsecond(1517644800_123456).unwrap())
        );
        assert_eq!(serde_json::to_string(&got).unwrap(), json);
    }

    #[test]
    fn timestamp_nanosecond_required() {
        #[derive(Debug, serde::Deserialize, serde::Serialize)]
        struct Data {
            #[serde(
                with = "crate::fmt::serde::timestamp::nanosecond::required"
            )]
            ts: Timestamp,
        }

        let json = r#"{"ts":1517644800000000000}"#;
        let got: Data = serde_json::from_str(&json).unwrap();
        assert_eq!(
            got.ts,
            Timestamp::from_nanosecond(1517644800_000000000).unwrap()
        );
        assert_eq!(serde_json::to_string(&got).unwrap(), json);

        let json = r#"{"ts":1517644800123456789}"#;
        let got: Data = serde_json::from_str(&json).unwrap();
        assert_eq!(
            got.ts,
            Timestamp::from_nanosecond(1517644800_123456789).unwrap()
        );
        assert_eq!(serde_json::to_string(&got).unwrap(), json);
    }

    #[test]
    fn timestamp_nanosecond_optional() {
        #[derive(Debug, serde::Deserialize, serde::Serialize)]
        struct Data {
            #[serde(
                with = "crate::fmt::serde::timestamp::nanosecond::optional"
            )]
            ts: Option<Timestamp>,
        }

        let json = r#"{"ts":1517644800000000000}"#;
        let got: Data = serde_json::from_str(&json).unwrap();
        assert_eq!(
            got.ts,
            Some(Timestamp::from_nanosecond(1517644800_000000000).unwrap())
        );
        assert_eq!(serde_json::to_string(&got).unwrap(), json);

        let json = r#"{"ts":1517644800123456789}"#;
        let got: Data = serde_json::from_str(&json).unwrap();
        assert_eq!(
            got.ts,
            Some(Timestamp::from_nanosecond(1517644800_123456789).unwrap())
        );
        assert_eq!(serde_json::to_string(&got).unwrap(), json);
    }
}
