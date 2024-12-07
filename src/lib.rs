#![cfg_attr(not(test), no_std)]
#![doc = include_str!("../README.md")]

mod encode;
pub mod encode_safe;

/// The crate's prelude.
pub mod prelude {
    pub use crate::{Encode, EncodeExt as _};
}

pub use crate::encode::{Buffer, Encode, EncodeExt, Size};
