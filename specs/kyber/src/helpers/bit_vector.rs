pub(crate) struct BitVector {
    bits : Vec<u8>
}

impl From<&[u8]> for BitVector {
    fn from(bytes : &[u8]) -> Self {
        let mut out = Vec::with_capacity(bytes.len() * 8);

        for byte in bytes {
            for j in 0..u8::BITS {
                out.push((byte >> j) & 1);
            }
        }

        Self {
            bits: out
        }
    }
}

impl BitVector {
    pub fn chunks(&self, chunk_size: usize) -> std::slice::Chunks<'_, u8> {
        self.bits.chunks(chunk_size)
    }
}
