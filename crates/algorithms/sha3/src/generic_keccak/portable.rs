use super::*;

#[cfg(hax)]
use crate::proof_utils::{lemma_mul_succ_le, valid_rate};

#[cfg(hax)]
use hax_lib::int::*;

#[cfg(hax)]
use hax_lib::prop::*;

// Workaround for hax#1698: `fstar::before`/`after` on impl blocks is silently
// dropped by the extractor, and `fstar::options` on methods inside an inherent
// impl triggers a macro-expansion error.  Attach push-options to a hax-only
// dummy function, which does extract properly.  No `#pop-options` is needed
// since this impl is the last item before the free-function items and each
// free function below sets its own options.
#[cfg(hax)]
#[hax_lib::fstar::before(r#"#push-options "--z3rlimit 800""#)]
fn _keccak_state_impl_opts() {}

#[hax_lib::attributes]
impl KeccakState<1, u64> {
    #[inline(always)]
    #[hax_lib::requires(
        valid_rate(RATE) &&
        start.to_int() + RATE.to_int() <= out.len().to_int()
    )]
    #[hax_lib::ensures(|_| future(out).len() == out.len())]
    pub(crate) fn squeeze_next_block<const RATE: usize>(&mut self, out: &mut [u8], start: usize) {
        self.keccakf1600();
        self.squeeze::<RATE>(out, start, RATE);
    }

    #[inline(always)]
    #[hax_lib::requires(
        valid_rate(RATE) &&
        RATE <= out.len()
    )]
    #[hax_lib::ensures(|_| future(out).len() == out.len())]
    pub(crate) fn squeeze_first_block<const RATE: usize>(&self, out: &mut [u8]) {
        self.squeeze::<RATE>(out, 0, RATE);
    }

    #[inline(always)]
    #[hax_lib::requires(
        valid_rate(RATE) &&
        3 * RATE <= out.len()
    )]
    #[hax_lib::ensures(|_| future(out).len() == out.len())]
    pub(crate) fn squeeze_first_three_blocks<const RATE: usize>(&mut self, out: &mut [u8]) {
        self.squeeze::<RATE>(out, 0, RATE);

        self.keccakf1600();
        self.squeeze::<RATE>(out, RATE, RATE);

        self.keccakf1600();
        self.squeeze::<RATE>(out, 2 * RATE, RATE);
    }

    #[inline(always)]
    #[hax_lib::requires(
        valid_rate(RATE) &&
        5 * RATE <= out.len()
    )]
    #[hax_lib::ensures(|_| future(out).len() == out.len())]
    pub(crate) fn squeeze_first_five_blocks<const RATE: usize>(&mut self, out: &mut [u8]) {
        self.squeeze::<RATE>(out, 0, RATE);

        self.keccakf1600();
        self.squeeze::<RATE>(out, RATE, RATE);

        self.keccakf1600();
        self.squeeze::<RATE>(out, 2 * RATE, RATE);

        self.keccakf1600();
        self.squeeze::<RATE>(out, 3 * RATE, RATE);

        self.keccakf1600();
        self.squeeze::<RATE>(out, 4 * RATE, RATE);
    }
}

/// Absorb phase of `keccak1`: initialise a Keccak state, absorb all full
/// rate-byte blocks of `input`, then pad and absorb the final partial block
/// with domain-separation byte `DELIM` and the pad10*1 terminator.
#[hax_lib::requires(valid_rate(RATE))]
#[hax_lib::fstar::options("--z3rlimit 300")]
#[inline]
pub(crate) fn absorb<const RATE: usize, const DELIM: u8>(input: &[u8]) -> KeccakState<1, u64> {
    let mut s = KeccakState::<1, u64>::new();
    let input_len = input.len();
    let input_blocks = input_len / RATE;
    let input_rem = input_len % RATE;
    for i in 0..input_blocks {
        #[cfg(hax)]
        lemma_mul_succ_le(i, input_blocks, RATE);

        s.absorb_block::<RATE>(&[input], i * RATE);
    }
    s.absorb_final::<RATE, DELIM>(&[input], input_len - input_rem, input_rem);
    s
}

/// Squeeze phase of `keccak1`: extract `output.len()` bytes from `s`,
/// applying Keccak-f between each full rate-byte block of output.
///
/// The ensures clause factors the result as a composition of impl
/// primitives (`f_squeeze`, `keccakf1600`) and the spec's recursive
/// `squeeze_blocks`:
///
///   * `output_blocks == 0`: a single `f_squeeze` of `output_len` bytes.
///   * `output_blocks > 0`:
///       let `output1 = f_squeeze RATE s output 0 RATE`
///       let `(st_mid, out_mid) = squeeze_blocks output_len s.st RATE 1 output_blocks output1`
///       if `output_rem == 0`: `out_mid`
///       else: `f_squeeze RATE (keccakf1600 {st = st_mid}) out_mid (output_len - output_rem) output_rem`
///
/// This is a *direct* consequence of the loop's semantics and does not
/// require buffer-locality reasoning: the first and last blocks are
/// stated in impl primitives, and the middle loop's invariant tracks
/// (state, output) through `squeeze_blocks` anchored at `output1`.
/// Preservation is discharged by the spec-side `lemma_squeeze_blocks_tail`
/// (right-extends the recursion) together with the per-block impl-to-spec
/// bridge `lemma_squeeze_block_portable`. An external lemma
/// (`EquivImplSpec.Sponge.Portable.API.lemma_squeeze_portable`) then
/// reconciles this composition with `Hacspec_sha3.Sponge.squeeze`.
#[hax_lib::requires(
    valid_rate(RATE) &&
    output.len() < usize::MAX - 200
)]
#[hax_lib::ensures(|_| (future(output).len() == output.len()).to_prop() & {
    fstar!(r#"(output_future <: t_Slice u8) ==
              (EquivImplSpec.Sponge.Portable.Steps.portable_squeeze_composed
                 $RATE $s $output <: t_Slice u8)"#)
})]
#[hax_lib::fstar::options("--fuel 0 --ifuel 1 --z3rlimit 800 --split_queries always")]
#[inline]
pub(crate) fn squeeze<const RATE: usize>(mut s: KeccakState<1, u64>, output: &mut [u8]) {
    let output_len = output.len();
    let output_blocks = output_len / RATE;
    let output_rem = output_len % RATE;

    #[cfg(hax)]
    let s_init_st = s.st;

    if output_blocks == 0 {
        s.squeeze::<RATE>(output, 0, output_len);
    } else {
        s.squeeze::<RATE>(output, 0, RATE);

        // Ghost snapshot of [output] after the first block write. Used as
        // the anchor for the spec's [squeeze_blocks] in the loop invariant
        // and in the ensures clause.
        #[cfg(hax)]
        let out1 = output.to_vec();

        // Establish the loop invariant at entry (i == 1):
        //   squeeze_blocks ... 1 1 out1_arr == (s_init_st, out1_arr)
        // via the base case of [squeeze_blocks].  Needed because the
        // function is verified at fuel 0 and does not unfold the spec
        // recursion implicitly.
        hax_lib::fstar!(
            r#"let out1_arr : t_Array u8 $output_len =
                  Alloc.Vec.impl_1__as_slice $out1 <: t_Slice _ in
               Libcrux_sha3.Proof_utils.Lemmas.lemma_div_mul_mod $output_len $RATE;
               Hacspec_sha3.Sponge.Lemmas.lemma_squeeze_blocks_base
                   $output_len $s_init_st $RATE (mk_usize 1) out1_arr"#
        );

        for i in 1..output_blocks {
            hax_lib::loop_invariant!(|i: usize| (output.len() == output_len).to_prop() & {
                fstar!(
                    r#"let out1_arr : t_Array u8 $output_len =
                             Alloc.Vec.impl_1__as_slice $out1 <: t_Slice _ in
                         let (st, out) =
                             Hacspec_sha3.Sponge.squeeze_blocks $output_len $s_init_st $RATE
                                 (mk_usize 1) $i out1_arr in
                         $s.st == st /\
                         ($output <: t_Slice u8) == (out <: t_Slice u8)"#
                )
            });

            #[cfg(hax)]
            lemma_mul_succ_le(i, output_blocks, RATE);
            // Compose two facts for preservation at i -> i+1:
            //   (a) spec-side right-tail: squeeze_blocks ... 1 (i+1) out1 unfolds
            //       to one more keccak_f/squeeze_state step after ... 1 i out1.
            //   (b) impl-to-spec per-block bridge: keccakf1600 ; f_squeeze RATE
            //       equals keccak_f ; squeeze_state RATE, at the current offset.
            // Pre-assertion pins [v i * v RATE < 2^64] so the [i *! RATE]
            // argument typechecks: [lemma_div_mul_mod] gives
            // [v output_blocks * v RATE <= v output_len], and
            // [lemma_mul_succ_le] gives [v i * v RATE <= v output_blocks * v RATE].
            hax_lib::fstar!(
                r#"let out1_arr : t_Array u8 $output_len =
                      Alloc.Vec.impl_1__as_slice $out1 <: t_Slice _ in
                   Libcrux_sha3.Proof_utils.Lemmas.lemma_div_mul_mod $output_len $RATE;
                   Libcrux_sha3.Proof_utils.Lemmas.lemma_mul_succ_le $i $output_blocks $RATE;
                   assert (v $i * v $RATE + v $RATE <= v $output_len);
                   let start : usize = $i *! $RATE in
                   Hacspec_sha3.Sponge.Lemmas.lemma_squeeze_blocks_tail $output_len
                       $s_init_st $RATE (mk_usize 1) $i ($i +! mk_usize 1) out1_arr;
                   EquivImplSpec.Sponge.Portable.Steps.lemma_squeeze_block_portable
                       $RATE $s $output start"#
            );

            s.keccakf1600();
            s.squeeze::<RATE>(output, i * RATE, RATE);
        }
        if output_rem != 0 {
            s.keccakf1600();
            s.squeeze::<RATE>(output, output_len - output_rem, output_rem);
        }
    }
}

#[hax_lib::requires(
    valid_rate(RATE) &&
    output.len() < usize::MAX - 200
)]
#[hax_lib::ensures(|_| future(output).len() == output.len())]
#[inline]
pub(crate) fn keccak1<const RATE: usize, const DELIM: u8>(input: &[u8], output: &mut [u8]) {
    let s = absorb::<RATE, DELIM>(input);
    squeeze::<RATE>(s, output);
}
