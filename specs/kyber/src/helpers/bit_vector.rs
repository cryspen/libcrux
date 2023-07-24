pub(crate) struct BitVector {
    bits: Vec<u8>,
}

pub(crate) struct BitVectorChunks<'a> {
    chunk_iterator: std::slice::Chunks<'a, u8>,
}

impl BitVectorChunks<'_> {
    pub fn next(&mut self) -> Option<BitVector> {
        self.chunk_iterator.next().map(|bits| BitVector {
            bits: bits.to_vec(),
        })
    }
}

impl IntoIterator for BitVector {
    type Item = u8;
    type IntoIter = <Vec<u8> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.bits.into_iter()
    }
}

impl From<&[u8]> for BitVector {
    fn from(bytes: &[u8]) -> Self {
        let mut out = Vec::with_capacity(bytes.len() * 8);

        for byte in bytes {
            for j in 0..u8::BITS {
                out.push((byte >> j) & 1);
            }
        }

        Self { bits: out }
    }
}

impl BitVector {
    pub fn new(bits: Vec<u8>) -> Self {
        for bit in &bits {
            assert!(*bit == 0 || *bit == 1);
        }

        Self { bits }
    }
    pub fn chunks(&self, chunk_size: usize) -> BitVectorChunks {
        BitVectorChunks {
            chunk_iterator: self.bits.chunks(chunk_size),
        }
    }
}
