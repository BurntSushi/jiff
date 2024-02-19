pub(crate) use self::inner::*;

#[cfg(not(any(
    feature = "tzdb-bundle-always",
    all(feature = "tzdb-bundle-platform", windows),
)))]
#[path = "disabled.rs"]
mod inner;
#[cfg(any(
    feature = "tzdb-bundle-always",
    all(feature = "tzdb-bundle-platform", windows),
))]
#[path = "enabled.rs"]
mod inner;
