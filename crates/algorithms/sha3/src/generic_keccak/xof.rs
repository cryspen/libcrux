use hax_lib::int::*;

use crate::{
    generic_keccak::KeccakState,
    traits::{Absorb, KeccakItem, Squeeze},
};

// Helper lemma for F* verification in the `absorb_full` loop.
//
// Proves that for any a, i, n, rate > 0 with i < n,
// we have a + i * rate + rate ≤ a + n * rate,
// i.e. each block‐offset stays within the total input length.
#[hax_lib::fstar::before(
    r#"
let rec lemma_offset_plus_rate_le_total (a i n rate: nat)
    : Lemma
        (requires i < n && rate > 0)
        (ensures a + i * rate + rate <= a + n * rate)
        (decreases n) =
    if n = 0 then ()
    else if i = n - 1 then ()
    else lemma_offset_plus_rate_le_total a i (n - 1) rate
"#
)]
// Helper lemma for F* verification in the 'squeeze' function.
//
// Proves the division‐multiplication‐modulo identity:
//   for any a, b with b != 0,
//   (a / b) * b + (a % b) = a.
#[hax_lib::fstar::before(
    r#"
let lemma_div_mul_mod (a b: usize)
    : Lemma
        (requires b <>. mk_usize 0)
        (ensures (a /! b) *! b +! (a %! b) =. a)
    = ()
"#
)]
// TODO: Should not be needed. Use hax_lib::fstar::options("")
#[hax_lib::fstar::before(
    r#"
#push-options "--split_queries always --z3rlimit 300"
"#
)]

/// The internal keccak state that can also buffer inputs to absorb.
/// This is used in the general xof APIs.
#[hax_lib::attributes]
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

#[cfg(hax)]
pub(crate) fn keccak_xof_state_inv<
    const PARALLEL_LANES: usize,
    const RATE: usize,
    STATE: KeccakItem<PARALLEL_LANES>,
>(
    xof: &KeccakXofState<PARALLEL_LANES, RATE, STATE>,
) -> bool {
    RATE != 0 && RATE <= 200 && RATE % 8 == 0 && xof.buf_len <= RATE
}

#[hax_lib::attributes]
#[hax_lib::fstar::options("--split_queries always --z3rlimit 300")] // TODO: Has no effect
impl<const PARALLEL_LANES: usize, const RATE: usize, STATE: KeccakItem<PARALLEL_LANES>>
    KeccakXofState<PARALLEL_LANES, RATE, STATE>
{
    /// An all zero block
    pub(crate) const fn zero_block() -> [u8; RATE] {
        [0u8; RATE]
    }

    /// Generate a new keccak xof state.
    #[hax_lib::requires(
        PARALLEL_LANES == 1 && // TODO: Generalize for the parallel case
        RATE != 0 &&
        RATE <= 200 &&
        RATE % 8 == 0
    )]
    #[hax_lib::ensures(|result|
        keccak_xof_state_inv(&result)
    )]
    pub(crate) fn new() -> Self {
        Self {
            inner: KeccakState::new(),
            buf: [Self::zero_block(); PARALLEL_LANES],
            buf_len: 0,
            sponge: false,
        }
    }

    /// Try to complete the internal partial buffer by consuming the minimum required
    /// number of bytes from the provided `inputs` so that `self.buf` becomes exactly
    /// one full block of size `RATE`.
    ///
    /// Behaviour:
    /// - If `self.buf_len` is 0 (no buffered bytes) or already equal to `RATE`
    ///   (already a full block), or if the combined available bytes in `inputs` are
    ///   not enough to reach `RATE`, the function does nothing and returns 0.
    /// - If `0 < self.buf_len < RATE` and `inputs[..]` contain at least
    ///   `RATE - self.buf_len` bytes, the function copies exactly
    ///   `consumed = RATE - self.buf_len` bytes from each lane `inputs[i]` into
    ///   `self.buf[i]` starting at the current `self.buf_len` offset, sets
    ///   `self.buf_len = RATE`, and returns `consumed`.
    ///
    /// Returns the `consumed` bytes from `inputs` if there's enough buffered
    /// content to consume, and `0` otherwise.
    /// If `consumed > 0` is returned, `self.buf` contains a full block to be
    /// loaded.
    // Note: consciously not inlining this function to avoid using too much stack
    // #[hax_lib::fstar::options("--fuel 5")]
    #[hax_lib::requires(
        PARALLEL_LANES == 1 &&
        keccak_xof_state_inv(self)
    )]
    #[hax_lib::ensures(|consumed|
        keccak_xof_state_inv(future(self)) &&
        if consumed == 0 {
            future(self).buf_len == self.buf_len && (
                self.buf_len == 0 ||
                self.buf_len == RATE ||
                self.buf_len.to_int() + inputs[0].len().to_int() < RATE.to_int()
            )
        } else {
            future(self).buf_len == RATE &&
            consumed == RATE - self.buf_len
        }
    )]
    pub(crate) fn fill_buffer(&mut self, inputs: &[&[u8]; PARALLEL_LANES]) -> usize {
        let input_len = inputs[0].len();

        // Check if we have enough data when combining the internal buffer and the input.
        if self.buf_len != 0 && self.buf_len != RATE && input_len >= RATE - self.buf_len {
            let consumed = RATE - self.buf_len;

            #[cfg(hax)]
            let self_buf_len = self.buf_len; // ghost variable for F* proof

            #[allow(clippy::needless_range_loop)]
            for i in 0..PARALLEL_LANES {
                hax_lib::loop_invariant!(|_: usize| { self.buf_len == self_buf_len });
                self.buf[i][self.buf_len..].copy_from_slice(&inputs[i][..consumed]);
            }

            self.buf_len = RATE;
            consumed
        } else {
            0
        }
    }

    // Note: consciously not inlining this function to avoid using too much stack
    #[hax_lib::requires(
        PARALLEL_LANES == 1 &&
        keccak_xof_state_inv(self)
    )]
    #[hax_lib::ensures(|remainder|
        keccak_xof_state_inv(future(self)) &&
        future(self).buf_len.to_int() + remainder.to_int() <= RATE.to_int()
    )]
    pub(crate) fn absorb_full(&mut self, inputs: &[&[u8]; PARALLEL_LANES]) -> usize
    where
        KeccakState<PARALLEL_LANES, STATE>: Absorb<PARALLEL_LANES>,
    {
        debug_assert!(PARALLEL_LANES > 0);
        debug_assert!(self.buf_len <= RATE);
        #[cfg(all(debug_assertions, not(hax)))]
        {
            for block in inputs {
                debug_assert!(block.len() == inputs[0].len());
            }
        }

        // Check if there are buffered bytes to absorb first and consume them.
        let input_consumed = self.fill_buffer(inputs);

        // We only need to consume the rest of the input.
        let input_to_consume = inputs[0].len() - input_consumed;

        // Consume the (rest of the) input ...
        let num_blocks = input_to_consume / RATE;
        let remainder = input_to_consume % RATE;

        if input_consumed > 0 || self.buf_len == RATE {
            // We have a full block in the local buffer now.
            // Convert self.buf to the right type for load_block
            let borrowed: [&[u8]; PARALLEL_LANES] =
                core::array::from_fn(|i| self.buf[i].as_slice());

            self.inner.load_block::<RATE>(&borrowed, 0);
            self.inner.keccakf1600();

            // "empty" the local buffer
            self.buf_len = 0;
        }

        #[cfg(hax)]
        let self_buf_len = self.buf_len;

        #[cfg(hax)]
        let end = input_consumed + num_blocks * RATE;

        #[cfg(hax)]
        hax_lib::assert!(end <= inputs[0].len());

        for i in 0..num_blocks {
            hax_lib::loop_invariant!(|_: usize| self.buf_len == self_buf_len);

            hax_lib::fstar!("lemma_offset_plus_rate_le_total (v input_consumed) (v i) (v num_blocks) (v v_RATE)");
            let start = i * RATE + input_consumed;

            // TODO: The cfg should not be needed here
            #[cfg(hax)]
            hax_lib::assert!(start + RATE <= end);

            self.inner.load_block::<RATE>(inputs, start);
            self.inner.keccakf1600();
        }

        remainder
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
    #[hax_lib::requires(
        PARALLEL_LANES == 1 &&
        keccak_xof_state_inv(self)
    )]
    #[hax_lib::ensures(|_|
        keccak_xof_state_inv(future(self))
    )]
    pub(crate) fn absorb(&mut self, inputs: &[&[u8]; PARALLEL_LANES])
    where
        KeccakState<PARALLEL_LANES, STATE>: Absorb<PARALLEL_LANES>,
    {
        let input_remainder_len = self.absorb_full(inputs);

        // ... buffer the rest if there's not enough input (left).
        if input_remainder_len > 0 {
            #[cfg(not(eurydice))]
            debug_assert!(
                // self.buf_len == 0 || // We consumed everything (or it was empty all along).
                self.buf_len + input_remainder_len <= RATE
            );

            hax_lib::assert!(input_remainder_len.to_int() + self.buf_len.to_int() <= RATE.to_int());

            let input_len = inputs[0].len();

            #[cfg(hax)]
            let self_buf_len = self.buf_len;

            #[allow(clippy::needless_range_loop)]
            for i in 0..PARALLEL_LANES {
                hax_lib::loop_invariant!(|_: usize| self.buf_len == self_buf_len);

                self.buf[i][self.buf_len..self.buf_len + input_remainder_len]
                    .copy_from_slice(&inputs[i][input_len - input_remainder_len..input_len]);
            }

            self.buf_len += input_remainder_len;
        }
    }

    /// Absorb a final block.
    ///
    /// The `inputs` block may be empty. Everything in the `inputs` block beyond
    /// `RATE` bytes is ignored.
    #[inline(always)]
    #[hax_lib::requires(
        PARALLEL_LANES == 1 &&
        keccak_xof_state_inv(self)
    )]
    #[hax_lib::ensures(|_|
        keccak_xof_state_inv(future(self))
    )]
    pub(crate) fn absorb_final<const DELIMITER: u8>(&mut self, inputs: &[&[u8]; PARALLEL_LANES])
    where
        KeccakState<PARALLEL_LANES, STATE>: Absorb<PARALLEL_LANES>,
    {
        self.absorb(inputs);

        let borrowed: [&[u8]; PARALLEL_LANES] = core::array::from_fn(|i| &self.buf[i][..]);

        self.inner
            .load_last::<RATE, DELIMITER>(&borrowed, 0, self.buf_len);
        self.inner.keccakf1600();
    }
}

/// Squeeze we only implement for N = 1 right now.
/// This is because it's not needed for N > 1 right now, but also because hax
/// can't handle the required mutability for it.
#[hax_lib::attributes]
impl<const RATE: usize, STATE: KeccakItem<1>> KeccakXofState<1, RATE, STATE> {
    /// Squeeze `N` x `LEN` bytes. Only `N = 1` for now.
    #[inline(always)]
    #[hax_lib::requires(keccak_xof_state_inv(self))]
    #[hax_lib::ensures(|_|
        keccak_xof_state_inv(future(self)) &&
        future(out).len() == out.len()
    )]
    pub(crate) fn squeeze(&mut self, out: &mut [u8])
    where
        KeccakState<1, STATE>: Squeeze<STATE>,
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

                #[cfg(hax)]
                let self_buf_len = self.buf_len;

                for i in 0..blocks {
                    hax_lib::loop_invariant!(
                        |_: usize| out.len() == out_len && self_buf_len == self.buf_len
                    );
                    hax_lib::fstar!("assert (v i * v v_RATE <= v out_len)");

                    #[cfg(hax)]
                    hax_lib::assert!(i.to_int() * RATE.to_int() <= out.len().to_int());

                    // Here we know that we always have full blocks to write out.
                    self.inner.keccakf1600();
                    self.inner.squeeze::<RATE>(out, i * RATE, RATE);
                }

                // For a and b with b < a
                // (a / b) * b + a % b = a

                let remaining = out_len % RATE;
                if remaining > 0 {
                    // Squeeze out the last partial block
                    self.inner.keccakf1600();

                    hax_lib::fstar!("lemma_div_mul_mod out_len v_RATE");
                    hax_lib::fstar!("assert (v blocks * v v_RATE + v remaining == v out_len)");
                    self.inner.squeeze::<RATE>(out, blocks * RATE, remaining);
                }
            }
            self.sponge = true;
        }
    }
}
