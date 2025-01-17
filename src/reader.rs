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
    pub(crate) fn read_byte(&mut self) -> Option<u8> {
        let &byte = self.buf.get(self.pos)?;
        self.pos += 1;
        Some(byte)
    }

    #[inline]
    pub(crate) fn read_slice(&mut self, n: usize) -> Option<&'buf [u8]> {
        let slice = self.buf.get(self.pos..self.pos + n)?;
        self.pos += n;
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
