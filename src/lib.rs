#![cfg_attr(not(test), no_std)]
#![doc = include_str!("../README.md")]

mod encode;
mod writer;

/// The crate's prelude.
pub mod prelude {
    pub use crate::{Encode, EncodeExt as _};
}

pub use crate::{
    encode::{Buffer, Encode, EncodeExt, Size},
    writer::Writer,
};
