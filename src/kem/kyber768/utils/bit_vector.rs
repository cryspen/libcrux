pub struct BitVector {
    bits: Vec<u8>,
}

pub struct BitVectorChunks<'a> {
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
    pub fn chunks(&self, chunk_size: usize) -> BitVectorChunks {
        BitVectorChunks {
            chunk_iterator: self.bits.chunks(chunk_size),
        }
    }
}

pub trait LittleEndianBitStream {
    fn nth_bit(&self, n: usize) -> u8;
    fn iter(&self) -> LittleEndianBitStreamIter<'_>;
}

pub struct LittleEndianBitStreamIter<'a> {
    bytes: &'a [u8],
    bit: usize,
}

impl Iterator for LittleEndianBitStreamIter<'_> {
    type Item = u8;

    fn next(&mut self) -> Option<Self::Item> {
        let byte_index = self.bit / 8;
        if byte_index >= self.bytes.len() {
            return None;
        }

        let out = self.bytes.nth_bit(self.bit);
        self.bit += 1;

        Some(out)
    }
}

impl LittleEndianBitStream for &[u8] {
    fn nth_bit(&self, n: usize) -> u8 {
        let byte = n / 8;
        let byte_bit = n % 8;
        (self[byte] >> byte_bit) & 1
    }

    fn iter(&self) -> LittleEndianBitStreamIter<'_> {
        LittleEndianBitStreamIter {
            bytes: self,
            bit: 0,
        }
    }
}

impl LittleEndianBitStream for Vec<u8> {
    fn nth_bit(&self, n: usize) -> u8 {
        self.as_slice().nth_bit(n)
    }

    fn iter(&self) -> LittleEndianBitStreamIter<'_> {
        LittleEndianBitStreamIter {
            bytes: self,
            bit: 0,
        }
    }
}
