#![cfg_attr(not(test), no_std)]
#![doc = include_str!("../README.md")]

pub mod encode_safe;
mod encode_unsafe;
mod writer;

/// The crate's prelude.
pub mod prelude {
    pub use crate::{Encode, EncodeExt as _};
}

pub use crate::{
    encode_unsafe::{Buffer, Encode, EncodeExt, Size},
    writer::Writer,
};
