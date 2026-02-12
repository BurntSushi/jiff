#![allow(dead_code)]
#![no_std]
#![cfg_attr(docsrs_jiff, feature(doc_cfg))]
#![warn(missing_debug_implementations)]

#[cfg(any(test, feature = "std"))]
extern crate std;

#[cfg(any(test, feature = "alloc"))]
extern crate alloc;

pub use self::timestamp::{AmbiguousOffset, Offset, Timestamp};

mod macros;

pub mod bounds;
pub mod civil;
pub mod constants;
mod timestamp;
