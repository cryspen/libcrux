/*pub struct BitVector {
    bits: Vec<u8>,
}
impl BitVector {
    pub fn len(&self) -> usize {
        return self.bits.len();
    }
}
impl IntoIterator for BitVector {
    type Item = u8;
    type IntoIter = <Vec<u8> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.bits.into_iter()
    }
}
impl BitVector {
    pub fn new() -> Self {
        Self {
            bits: Vec::<u8>::new(),
        }
    }

    pub fn push(&mut self, value: u8) {
        assert!(value == 0 || value == 1);

        self.bits.push(value);
    }

    pub fn chunks(&self, chunk_size: usize) -> BitVectorChunks {
        BitVectorChunks {
            chunk_iterator: self.bits.chunks(chunk_size),
        }
    }
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
impl<'a> Iterator for BitVectorChunks<'a> {
    type Item = &'a [u8];

    fn next(&mut self) -> Option<Self::Item> {
        self.chunk_iterator.next()
    }
}*/
pub type BitVector = Vec<u8>;
pub type BitSlice<'a> = &'a [u8];
