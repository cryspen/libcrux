/// An incremental eXtendable Output Function API for SHA3 (shake).
///
/// This x4 variant of the incremental API always processes 4 inputs at a time.
/// This uses AVX2 when available to run the 4 operations in parallel.
///
/// More generic APIs will be added later.
mod internal;

/// Incremental state
#[cfg_attr(hax, hax_lib::opaque_type)]
pub struct Shake128StateX4 {
    state: internal::Shake128StateX4,
}

impl Shake128StateX4 {
    /// Create a new Shake128 x4 state.
    #[inline(always)]
    pub fn new() -> Self {
        Self {
            state: internal::Shake128StateX4::new(),
        }
    }

    /// This is only used internally to work around Eurydice bugs.
    #[inline(always)]
    pub fn free_memory(self) {
        self.state.free();
    }

    /// Absorb 4 blocks.
    ///
    /// A blocks MUST all be the same length.
    /// Each slice MUST be a multiple of the block length 168.
    #[inline(always)]
    pub fn absorb_4blocks(&mut self, input: [&[u8]; 4]) {
        self.state.absorb_blocks(input)
    }

    /// Absorb up to 4 blocks.
    ///
    /// The `input` must be of length 1 to 4.
    /// A blocks MUST all be the same length.
    /// Each slice MUST be a multiple of the block length 168.
    #[inline(always)]
    pub fn absorb_final<const N: usize>(&mut self, input: [&[u8]; N]) {
        // Pad the input to the length of 4
        let data = [
            input[0],
            if N > 1 { input[1] } else { &[] },
            if N > 2 { input[2] } else { &[] },
            if N > 3 { input[3] } else { &[] },
        ];
        self.state.absorb_final(data);
    }

    /// Squeeze `M` blocks of length `N`
    #[inline(always)]
    pub fn squeeze_blocks<const N: usize, const M: usize>(&mut self) -> [[u8; N]; M] {
        self.state.squeeze_blocks()
    }
}
