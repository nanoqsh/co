mod encode;

/// The crate's prelude.
pub mod prelude {
    pub use crate::{Encode, EncodeExt as _};
}

pub use crate::encode::{Buffer, Encode, EncodeExt, Size};
