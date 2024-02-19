// Some feature combinations result in some of these macros never being used.
// Which is fine. Just squash the warnings.
#![allow(unused_macros)]

macro_rules! log {
    ($($tt:tt)*) => {
        #[cfg(feature = "logging")]
        {
            $($tt)*
        }
    }
}

macro_rules! error {
    ($($tt:tt)*) => { log!(log::error!($($tt)*)) }
}

macro_rules! warn {
    ($($tt:tt)*) => { log!(log::warn!($($tt)*)) }
}

macro_rules! info {
    ($($tt:tt)*) => { log!(log::info!($($tt)*)) }
}

macro_rules! debug {
    ($($tt:tt)*) => { log!(log::debug!($($tt)*)) }
}

macro_rules! trace {
    ($($tt:tt)*) => { log!(log::trace!($($tt)*)) }
}

/// A copy of std's `dbg!` macro that doesn't do pretty printing.
///
/// This is nice because we usually want more compact output in this crate.
/// Also, because we don't import std's prelude, we have to use `std::dbg!`.
/// This macro definition makes it available as `dbg!`.
#[cfg(feature = "std")]
#[macro_export]
macro_rules! dbg {
    () => {
        std::eprintln!("[{}:{}:{}]", $crate::file!(), $crate::line!(), $crate::column!())
    };
    ($val:expr $(,)?) => {
        match $val {
            tmp => {
                std::eprintln!(
                    "[{}:{}:{}] {} = {:?}",
                    $crate::file!(),
                    $crate::line!(),
                    $crate::column!(),
                    $crate::stringify!($val),
                    &tmp,
                );
                tmp
            }
        }
    };
    ($($val:expr),+ $(,)?) => {
        ($($crate::dbg!($val)),+,)
    };
}
