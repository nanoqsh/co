/// The buffer reader.
///
/// In this implementation it is not required to be used directly,
/// use the [decoder](crate::Decoder) type instead.
pub struct Reader<'buf> {
    buf: &'buf [u8],
    pos: usize,
}

impl<'buf> Reader<'buf> {
    #[inline]
    pub(crate) fn new(buf: &'buf [u8]) -> Self {
        Self { buf, pos: 0 }
    }

    #[inline]
    pub(crate) fn remaining(&self) -> usize {
        self.buf.len() - self.pos
    }

    #[inline]
    pub(crate) fn read_byte(&mut self) -> Option<u8> {
        let &byte = self.buf.get(self.pos)?;
        self.pos += 1;
        Some(byte)
    }

    #[inline]
    pub(crate) fn read_slice(&mut self, n: usize) -> Option<&'buf [u8]> {
        debug_assert!(self.pos <= self.buf.len(), "reader invariant violation");

        let new_pos = usize::checked_add(self.pos, n).expect("the position cannot overflow");
        if new_pos > self.buf.len() {
            return None;
        }

        debug_assert!(
            new_pos <= self.buf.len(),
            "`new_pos` must not exceed the buffer length",
        );

        // SAFETY:
        // * `pos <= buf.len()` guaranteed by the reader invariant
        // * `pos + n` cannot overflow
        // * `pos + n <= buf.len()` checked above
        let slice = unsafe { self.buf.get_unchecked(self.pos..new_pos) };

        self.pos = new_pos;
        Some(slice)
    }

    #[inline]
    pub(crate) fn read_array<const N: usize>(&mut self) -> Option<&'buf [u8; N]> {
        let slice = self.read_slice(N)?;

        debug_assert_eq!(
            slice.len(),
            N,
            "slice length must be equal to the array size",
        );

        let array_ptr = slice.as_ptr() as *const [u8; N];

        // SAFETY: the slice length is `N` due to `read_slice` implementation
        let array_ref = unsafe { &*array_ptr };

        Some(array_ref)
    }
}
