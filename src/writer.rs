use core::{mem::MaybeUninit, slice};

/// The buffer writer.
///
/// In this implementation, it is not required to be used directly,
/// use the [`Encode`](crate::Encode) trait instead.
pub struct Writer<'buf> {
    buf: &'buf mut [MaybeUninit<u8>],
    pos: usize,
}

impl<'buf> Writer<'buf> {
    #[inline]
    pub(crate) fn new(buf: &'buf mut [MaybeUninit<u8>]) -> Self {
        Self { buf, pos: 0 }
    }

    #[inline]
    pub(crate) fn remaining(&self) -> usize {
        self.buf.len() - self.pos
    }

    #[inline]
    fn as_mut_ptr(&mut self) -> *mut u8 {
        debug_assert!(self.pos <= self.buf.len(), "writer invariant violation");

        let ptr: *mut u8 = self.buf.as_mut_ptr().cast();

        // SAFETY:
        // * the writer maintains the invariant `pos <= buf.len()`,
        //   based on this, we can conclude that
        //   `ptr + pos` will never exceed `isize::MAX`
        //   and will always point to an allocated object
        unsafe { ptr.add(self.pos) }
    }

    /// Writes a slice into the buffer.
    ///
    /// SAFETY:
    /// * the caller must ensure that the buffer has enough space
    ///   to write the entire slice i.e. `self.remaining() >= s.len()`.
    #[inline]
    pub(crate) unsafe fn write_slice(&mut self, s: &[u8]) {
        debug_assert!(self.remaining() >= s.len());

        let ptr = self.as_mut_ptr();

        // SAFETY:
        // * the slice and `buf` are nonoverlapping since `buf` passed by `&mut [_]`.
        unsafe { ptr.copy_from_nonoverlapping(s.as_ptr(), s.len()) }

        self.pos += s.len();
    }

    /// Writes a byte into the buffer.
    ///
    /// SAFETY:
    /// * the caller must ensure that the buffer has enough space
    ///   to write the byte i.e. `self.remaining() >= 1`.
    #[inline]
    pub(crate) unsafe fn write_byte(&mut self, u: u8) {
        debug_assert!(self.remaining() >= size_of::<u8>());

        let ptr = self.as_mut_ptr();

        // SAFETY: checked by the caller
        unsafe { ptr.write(u) }

        self.pos += size_of::<u8>();
    }

    /// Returns the fully initialized buffer.
    ///
    /// SAFETY:
    /// * the caller must ensure `self.remaining() == 0`,
    ///   this means the whole buffer was initialized.
    #[inline]
    pub(crate) unsafe fn init(self) -> &'buf mut [u8] {
        debug_assert_eq!(self.remaining(), 0);

        // SAFETY: checked by the caller
        unsafe { slice::from_raw_parts_mut(self.buf.as_mut_ptr().cast(), self.buf.len()) }
    }
}
