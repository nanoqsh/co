#![cfg_attr(not(test), no_std)]
#![doc = include_str!("../README.md")]

mod decode;
mod encode;
mod reader;
mod writer;

/// The crate's prelude.
pub mod prelude {
    pub use crate::{AsDecoder as _, Decode, DecodeWith, Encode, EncodeExt as _};
}

pub use crate::{
    decode::{AsDecoder, Decode, DecodeWith, Decoder},
    encode::{Buffer, Encode, EncodeExt, LittleEndianEncodeExt, Size},
    reader::Reader,
    writer::Writer,
};
