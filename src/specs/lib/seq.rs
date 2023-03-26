pub struct Seq<T>(Vec<T>);

impl<T: Clone> Seq<T> {
    /// Get a slice with length `len` of this sequence, starting at `start`.
    pub fn slice(&self, start: usize, len: usize) -> Self {
        let mut a = Self(Vec::with_capacity(len));
        a.0.extend_from_slice(&self.0[start..start + len]);
        a
    }

    /// Get the number of chunks of length `chunk_size` in this sequence.
    pub fn num_chunks(&self, chunk_size: usize) -> usize {
        (self.0.len() + chunk_size - 1) / chunk_size
    }

    /// Get the `chunk_number` chunk of `chunk_size` from this sequence.
    ///
    /// Use `chunk` to get a non-owning version that doesn't need to copy.
    ///
    /// Returns a tuple with the length of the resulting sequence as well as the sequence.
    pub fn get_chunk(&self, chunk_size: usize, chunk_number: usize) -> (usize, Self) {
        let idx_start = chunk_size * chunk_number;
        let len = if idx_start + chunk_size > self.0.len() {
            self.0.len() - idx_start
        } else {
            chunk_size
        };
        let out = self.slice(idx_start, len);
        (len, out)
    }

    fn update_slice(mut self, start_out: usize, v: &Seq<T>, start_in: usize, len: usize) -> Self {
        debug_assert!(
            self.0.len() >= start_out + len,
            "{} < {} + {}",
            self.0.len(),
            start_out,
            len
        );
        debug_assert!(
            v.0.len() >= start_in + len,
            "{} < {} + {}",
            v.0.len(),
            start_in,
            len
        );
        for i in 0..len {
            self.0[start_out + i] = v.0[start_in + i].clone();
        }
        self
    }

    /// Update this sequence, at position 0, with the values from `v`.
    ///
    /// Returns the new sequence.
    fn update_start(self, v: &Seq<T>) -> Self {
        let len = v.0.len();
        self.update_slice(0, v, 0, len)
    }
}
