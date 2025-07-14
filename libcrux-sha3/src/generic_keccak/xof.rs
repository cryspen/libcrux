use crate::{
    generic_keccak::KeccakState,
    traits::{Absorb, KeccakItem, Squeeze1},
};

/// The internal keccak state that can also buffer inputs to absorb.
/// This is used in the general xof APIs.
pub(crate) struct KeccakXofState<
    const PARALLEL_LANES: usize,
    const RATE: usize,
    STATE: KeccakItem<PARALLEL_LANES>,
> {
    inner: KeccakState<PARALLEL_LANES, STATE>,

    // Buffer inputs on absorb.
    buf: [[u8; RATE]; PARALLEL_LANES],

    // Buffered length.
    buf_len: usize,

    // Needs sponge.
    sponge: bool,
}

#[hax_lib::attributes]
impl<const PARALLEL_LANES: usize, const RATE: usize, STATE: KeccakItem<PARALLEL_LANES>>
    KeccakXofState<PARALLEL_LANES, RATE, STATE>
{
    /// An all zero block
    pub(crate) const fn zero_block() -> [u8; RATE] {
        [0u8; RATE]
    }

    /// Generate a new keccak xof state.
    pub(crate) fn new() -> Self {
        Self {
            inner: KeccakState::new(),
            buf: [Self::zero_block(); PARALLEL_LANES],
            buf_len: 0,
            sponge: false,
        }
    }

    /// Absorb
    ///
    /// This function takes any number of bytes to absorb and buffers if it's not enough.
    /// The function assumes that all input slices in `inputs` have the same length.
    ///
    /// Only a multiple of `RATE` blocks are absorbed.
    /// For the remaining bytes [`absorb_final`] needs to be called.
    ///
    /// This works best with relatively small `inputs`.
    #[inline(always)]
    pub(crate) fn absorb(&mut self, inputs: &[&[u8]; PARALLEL_LANES])
    where
        KeccakState<PARALLEL_LANES, STATE>: Absorb<PARALLEL_LANES>,
    {
        let input_remainder_len = self.absorb_full(inputs);

        // ... buffer the rest if there's not enough input (left).
        if input_remainder_len > 0 {
            debug_assert!(
                self.buf_len == 0  // We consumed everything (or it was empty all along).
                 || self.buf_len + input_remainder_len <= RATE
            );

            let input_len = inputs[0].len();

            #[allow(clippy::needless_range_loop)]
            for i in 0..PARALLEL_LANES {
                self.buf[i][self.buf_len..self.buf_len + input_remainder_len]
                    .copy_from_slice(&inputs[i][input_len - input_remainder_len..]);
            }
            self.buf_len += input_remainder_len;
        }
    }

    // Note: consciously not inlining this function to avoid using too much stack
    pub(crate) fn absorb_full(&mut self, inputs: &[&[u8]; PARALLEL_LANES]) -> usize
    where
        KeccakState<PARALLEL_LANES, STATE>: Absorb<PARALLEL_LANES>,
    {
        debug_assert!(PARALLEL_LANES > 0);
        debug_assert!(self.buf_len < RATE);
        #[cfg(all(debug_assertions, not(hax)))]
        {
            for block in inputs {
                debug_assert!(block.len() == inputs[0].len());
            }
        }

        // Check if there are buffered bytes to absorb first and consume them.
        let input_consumed = self.fill_buffer(inputs);

        if input_consumed > 0 {
            let mut borrowed = [[0u8; RATE].as_slice(); PARALLEL_LANES];
            // We have a full block in the local buffer now.
            #[allow(clippy::needless_range_loop)]
            for i in 0..PARALLEL_LANES {
                borrowed[i] = &self.buf[i];
            }

            self.inner.load_block::<RATE>(&borrowed, 0);
            self.inner.keccakf1600();

            // "empty" the local buffer
            self.buf_len = 0;
        }

        // We only need to consume the rest of the input.
        let input_to_consume = inputs[0].len() - input_consumed;

        // Consume the (rest of the) input ...
        let num_blocks = input_to_consume / RATE;
        let remainder = input_to_consume % RATE;
        for i in 0..num_blocks {
            // We only get in here if `input_len / RATE > 0`.
            self.inner
                .load_block::<RATE>(inputs, input_consumed + i * RATE);
            self.inner.keccakf1600();
        }

        remainder
    }

    /// Consume the internal buffer and the required amount of the input to pad to
    /// `RATE`.
    ///
    /// Returns the `consumed` bytes from `inputs` if there's enough buffered
    /// content to consume, and `0` otherwise.
    /// If `consumed > 0` is returned, `self.buf` contains a full block to be
    /// loaded.
    // Note: consciously not inlining this function to avoid using too much stack
    #[hax_lib::requires(PARALLEL_LANES > 0 && self.buf_len < RATE)]
    pub(crate) fn fill_buffer(&mut self, inputs: &[&[u8]; PARALLEL_LANES]) -> usize {
        let input_len = inputs[0].len();

        // Nothing buffered, buffer full, or no input
        if self.buf_len == 0 || self.buf_len >= RATE || input_len == 0 {
            return 0;
        }

        // Remaining space to complete a full block
        let need = RATE - self.buf_len;
        if input_len < need {
            return 0;
        }

        let end = RATE; // buf_len + need == RATE
        #[allow(clippy::needless_range_loop)]
        for i in 0..PARALLEL_LANES {
            self.buf[i][self.buf_len..end].copy_from_slice(&inputs[i][..need]);
        }
        self.buf_len = end;
        need
    }

    /// Absorb a final block.
    ///
    /// The `inputs` block may be empty. Everything in the `inputs` block beyond
    /// `RATE` bytes is ignored.
    #[inline(always)]
    pub(crate) fn absorb_final<const DELIMITER: u8>(&mut self, inputs: &[&[u8]; PARALLEL_LANES])
    where
        KeccakState<PARALLEL_LANES, STATE>: Absorb<PARALLEL_LANES>,
    {
        self.absorb(inputs);

        let mut borrowed = [[0u8; RATE].as_slice(); PARALLEL_LANES];

        #[allow(clippy::needless_range_loop)]
        for i in 0..PARALLEL_LANES {
            borrowed[i] = &self.buf[i];
        }

        self.inner
            .load_last::<RATE, DELIMITER>(&borrowed, 0, self.buf_len);
        self.inner.keccakf1600();
    }
}

/// Squeeze we only implement for N = 1 right now.
/// This is because it's not needed for N > 1 right now, but also because hax
/// can't handle the required mutability for it.
impl<const RATE: usize, STATE: KeccakItem<1>> KeccakXofState<1, RATE, STATE> {
    /// Squeeze `N` x `LEN` bytes. Only `N = 1` for now.
    #[inline(always)]
    pub(crate) fn squeeze(&mut self, out: &mut [u8])
    where
        KeccakState<1, STATE>: Squeeze1<STATE>,
    {
        if self.sponge {
            // If we called `squeeze` before, call f1600 first.
            // We do it this way around so that we don't call f1600 at the end
            // when we don't need it.
            self.inner.keccakf1600();
        }

        let out_len = out.len();

        if out_len > 0 {
            if out_len <= RATE {
                self.inner.squeeze::<RATE>(out, 0, out_len);
            } else {
                // How many blocks do we need to squeeze out?
                let blocks = out_len / RATE;

                for i in 0..blocks {
                    // Here we know that we always have full blocks to write out.
                    self.inner.keccakf1600();
                    self.inner.squeeze::<RATE>(out, i * RATE, RATE);
                }

                let remaining = out_len % RATE;
                if remaining > 0 {
                    // Squeeze out the last partial block
                    self.inner.keccakf1600();
                    self.inner.squeeze::<RATE>(out, blocks * RATE, remaining);
                }
            }
            self.sponge = true;
        }
    }
}
