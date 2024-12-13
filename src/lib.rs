#![cfg_attr(not(test), no_std)]
#![doc = include_str!("../README.md")]

mod encode_safe;
pub mod encode_unsafe;

/// The crate's prelude.
pub mod prelude {
    pub use crate::{Encode, EncodeExt as _};
}

pub use crate::encode_safe::{Encode, EncodeExt};
