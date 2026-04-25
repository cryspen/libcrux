use super::*;

#[cfg(hax)]
use crate::proof_utils::{lemma_mul_succ_le, valid_rate};

use libcrux_intrinsics::avx2::Vec256;

/// Absorb phase of `keccak4`: initialise a four-lane Keccak state,
/// absorb all full rate-byte blocks of `data[0..4]` in parallel,
/// then pad and absorb each lane's final partial block with
/// domain-separation byte `DELIM` and the pad10*1 terminator.
///
/// The ensures clause asserts per-lane equality with the scalar spec
/// function `Hacspec_sha3.Sponge.absorb`.  The loop invariant uses
/// `absorb_blocks` per lane, mirroring the Arm64 backend at N=2.
#[inline]
#[hax_lib::requires(
    valid_rate(RATE) &&
    data[0].len() == data[1].len() &&
    data[0].len() == data[2].len() &&
    data[0].len() == data[3].len()
)]
#[hax_lib::ensures(|result| fstar!(r#"
    (EquivImplSpec.Keccakf.Generic.extract_lane (mk_usize 4)
       EquivImplSpec.Keccakf.Avx2.lc_avx2 $result.st 0) ==
      Hacspec_sha3.Sponge.absorb $RATE $DELIM (Core_models.Ops.Index.f_index $data (mk_usize 0)) /\
    (EquivImplSpec.Keccakf.Generic.extract_lane (mk_usize 4)
       EquivImplSpec.Keccakf.Avx2.lc_avx2 $result.st 1) ==
      Hacspec_sha3.Sponge.absorb $RATE $DELIM (Core_models.Ops.Index.f_index $data (mk_usize 1)) /\
    (EquivImplSpec.Keccakf.Generic.extract_lane (mk_usize 4)
       EquivImplSpec.Keccakf.Avx2.lc_avx2 $result.st 2) ==
      Hacspec_sha3.Sponge.absorb $RATE $DELIM (Core_models.Ops.Index.f_index $data (mk_usize 2)) /\
    (EquivImplSpec.Keccakf.Generic.extract_lane (mk_usize 4)
       EquivImplSpec.Keccakf.Avx2.lc_avx2 $result.st 3) ==
      Hacspec_sha3.Sponge.absorb $RATE $DELIM (Core_models.Ops.Index.f_index $data (mk_usize 3))
"#))]
#[hax_lib::fstar::options("--fuel 1 --ifuel 1 --z3rlimit 800 --split_queries always")]
pub(crate) fn absorb4<const RATE: usize, const DELIM: u8>(
    data: &[&[u8]; 4],
) -> KeccakState<4, Vec256> {
    let mut s = KeccakState::<4, Vec256>::new();
    let data_len = data[0].len();
    let data_blocks = data_len / RATE;
    let rem = data_len % RATE;
    hax_lib::fstar!(
        r#"let zeros : t_Array u64 (mk_usize 25) =
               Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 25) in
           EquivImplSpec.Keccakf.Avx2.lemma_extract_lane_zero_avx2 0;
           EquivImplSpec.Keccakf.Avx2.lemma_extract_lane_zero_avx2 1;
           EquivImplSpec.Keccakf.Avx2.lemma_extract_lane_zero_avx2 2;
           EquivImplSpec.Keccakf.Avx2.lemma_extract_lane_zero_avx2 3;
           Hacspec_sha3.Sponge.Lemmas.lemma_absorb_blocks_base
               zeros $RATE (mk_usize 0) (Core_models.Ops.Index.f_index $data (mk_usize 0));
           Hacspec_sha3.Sponge.Lemmas.lemma_absorb_blocks_base
               zeros $RATE (mk_usize 0) (Core_models.Ops.Index.f_index $data (mk_usize 1));
           Hacspec_sha3.Sponge.Lemmas.lemma_absorb_blocks_base
               zeros $RATE (mk_usize 0) (Core_models.Ops.Index.f_index $data (mk_usize 2));
           Hacspec_sha3.Sponge.Lemmas.lemma_absorb_blocks_base
               zeros $RATE (mk_usize 0) (Core_models.Ops.Index.f_index $data (mk_usize 3))"#
    );
    for i in 0..data_blocks {
        hax_lib::loop_invariant!(|i: usize| {
            fstar!(
                r#"let zeros : t_Array u64 (mk_usize 25) =
                       Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 25) in
                   v $i <= v $data_blocks /\
                   (EquivImplSpec.Keccakf.Generic.extract_lane (mk_usize 4)
                      EquivImplSpec.Keccakf.Avx2.lc_avx2 $s.st 0) ==
                     Hacspec_sha3.Sponge.absorb_blocks
                       zeros $RATE (mk_usize 0) $i (Core_models.Ops.Index.f_index $data (mk_usize 0)) /\
                   (EquivImplSpec.Keccakf.Generic.extract_lane (mk_usize 4)
                      EquivImplSpec.Keccakf.Avx2.lc_avx2 $s.st 1) ==
                     Hacspec_sha3.Sponge.absorb_blocks
                       zeros $RATE (mk_usize 0) $i (Core_models.Ops.Index.f_index $data (mk_usize 1)) /\
                   (EquivImplSpec.Keccakf.Generic.extract_lane (mk_usize 4)
                      EquivImplSpec.Keccakf.Avx2.lc_avx2 $s.st 2) ==
                     Hacspec_sha3.Sponge.absorb_blocks
                       zeros $RATE (mk_usize 0) $i (Core_models.Ops.Index.f_index $data (mk_usize 2)) /\
                   (EquivImplSpec.Keccakf.Generic.extract_lane (mk_usize 4)
                      EquivImplSpec.Keccakf.Avx2.lc_avx2 $s.st 3) ==
                     Hacspec_sha3.Sponge.absorb_blocks
                       zeros $RATE (mk_usize 0) $i (Core_models.Ops.Index.f_index $data (mk_usize 3))"#
            )
        });
        #[cfg(hax)]
        lemma_mul_succ_le(i, data_blocks, RATE);

        hax_lib::fstar!(
            r#"let zeros : t_Array u64 (mk_usize 25) =
                   Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 25) in
               assert (Libcrux_sha3.Proof_utils.slices_same_len (mk_usize 4) $data);
               EquivImplSpec.Sponge.Avx2.Steps.lemma_absorb_block_avx2
                   $RATE $s $data ($i *! $RATE) 0;
               EquivImplSpec.Sponge.Avx2.Steps.lemma_absorb_block_avx2
                   $RATE $s $data ($i *! $RATE) 1;
               EquivImplSpec.Sponge.Avx2.Steps.lemma_absorb_block_avx2
                   $RATE $s $data ($i *! $RATE) 2;
               EquivImplSpec.Sponge.Avx2.Steps.lemma_absorb_block_avx2
                   $RATE $s $data ($i *! $RATE) 3;
               Hacspec_sha3.Sponge.Lemmas.lemma_absorb_blocks_tail
                   zeros $RATE (mk_usize 0) $i ($i +! mk_usize 1)
                   (Core_models.Ops.Index.f_index $data (mk_usize 0));
               Hacspec_sha3.Sponge.Lemmas.lemma_absorb_blocks_tail
                   zeros $RATE (mk_usize 0) $i ($i +! mk_usize 1)
                   (Core_models.Ops.Index.f_index $data (mk_usize 1));
               Hacspec_sha3.Sponge.Lemmas.lemma_absorb_blocks_tail
                   zeros $RATE (mk_usize 0) $i ($i +! mk_usize 1)
                   (Core_models.Ops.Index.f_index $data (mk_usize 2));
               Hacspec_sha3.Sponge.Lemmas.lemma_absorb_blocks_tail
                   zeros $RATE (mk_usize 0) $i ($i +! mk_usize 1)
                   (Core_models.Ops.Index.f_index $data (mk_usize 3))"#
        );

        s.absorb_block::<RATE>(data, i * RATE);
    }
    hax_lib::fstar!(
        r#"let zeros : t_Array u64 (mk_usize 25) =
               Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 25) in
           assert (Libcrux_sha3.Proof_utils.slices_same_len (mk_usize 4) $data);
           EquivImplSpec.Sponge.Avx2.Steps.lemma_absorb_last_avx2
               $RATE $DELIM $s $data ($data_len -! $rem) $rem 0;
           EquivImplSpec.Sponge.Avx2.Steps.lemma_absorb_last_avx2
               $RATE $DELIM $s $data ($data_len -! $rem) $rem 1;
           EquivImplSpec.Sponge.Avx2.Steps.lemma_absorb_last_avx2
               $RATE $DELIM $s $data ($data_len -! $rem) $rem 2;
           EquivImplSpec.Sponge.Avx2.Steps.lemma_absorb_last_avx2
               $RATE $DELIM $s $data ($data_len -! $rem) $rem 3;
           Hacspec_sha3.Sponge.Lemmas.lemma_absorb_rec_via_blocks
               zeros $RATE $DELIM (Core_models.Ops.Index.f_index $data (mk_usize 0));
           Hacspec_sha3.Sponge.Lemmas.lemma_absorb_rec_via_blocks
               zeros $RATE $DELIM (Core_models.Ops.Index.f_index $data (mk_usize 1));
           Hacspec_sha3.Sponge.Lemmas.lemma_absorb_rec_via_blocks
               zeros $RATE $DELIM (Core_models.Ops.Index.f_index $data (mk_usize 2));
           Hacspec_sha3.Sponge.Lemmas.lemma_absorb_rec_via_blocks
               zeros $RATE $DELIM (Core_models.Ops.Index.f_index $data (mk_usize 3))"#
    );
    s.absorb_final::<RATE, DELIM>(data, data_len - rem, rem);
    s
}

/// Squeeze phase of `keccak4`: extract `out0.len()` bytes from each
/// lane of `s` into `out0..out3`, applying Keccak-f between each
/// full rate-byte block of output.
#[inline]
#[hax_lib::requires(valid_rate(RATE)
    && out0.len() == out1.len()
    && out0.len() == out2.len()
    && out0.len() == out3.len())]
#[hax_lib::ensures(|_|
    future(out0).len() == out0.len() &&
    future(out1).len() == out1.len() &&
    future(out2).len() == out2.len() &&
    future(out3).len() == out3.len()
)]
#[hax_lib::fstar::options("--z3rlimit 600 --split_queries always")]
pub(crate) fn squeeze4<const RATE: usize>(
    mut s: KeccakState<4, Vec256>,
    out0: &mut [u8],
    out1: &mut [u8],
    out2: &mut [u8],
    out3: &mut [u8],
) {
    #[cfg(hax)]
    let out0_len = out0.len();
    #[cfg(hax)]
    let out1_len = out1.len();
    #[cfg(hax)]
    let out2_len = out2.len();
    #[cfg(hax)]
    let out3_len = out3.len();

    let outlen = out0.len();
    let blocks = outlen / RATE;
    let last = outlen - (outlen % RATE);

    if blocks == 0 {
        s.squeeze4::<RATE>(out0, out1, out2, out3, 0, outlen);
    } else {
        s.squeeze4::<RATE>(out0, out1, out2, out3, 0, RATE);
        for i in 1..blocks {
            hax_lib::loop_invariant!(|_: usize|
                out0.len() == out0_len && out1.len() == out1_len &&
                out2.len() == out2_len && out3.len() == out3_len);
            #[cfg(hax)]
            lemma_mul_succ_le(i, blocks, RATE);

            s.keccakf1600();
            s.squeeze4::<RATE>(out0, out1, out2, out3, i * RATE, RATE);
        }
        if last < outlen {
            s.keccakf1600();
            s.squeeze4::<RATE>(out0, out1, out2, out3, last, outlen - last);
        }
    }
}

#[inline(always)]
#[hax_lib::requires(
    valid_rate(RATE) &&
    out0.len() == out1.len() &&
    out0.len() == out2.len() &&
    out0.len() == out3.len() &&
    data[0].len() == data[1].len() &&
    data[0].len() == data[2].len() &&
    data[0].len() == data[3].len()
)]
#[hax_lib::ensures(|_|
    future(out0).len() == out0.len() &&
    future(out1).len() == out1.len() &&
    future(out2).len() == out2.len() &&
    future(out3).len() == out3.len()
)]
pub(crate) fn keccak4<const RATE: usize, const DELIM: u8>(
    data: &[&[u8]; 4],
    out0: &mut [u8],
    out1: &mut [u8],
    out2: &mut [u8],
    out3: &mut [u8],
) {
    #[cfg(not(eurydice))]
    debug_assert!(out0.len() == out1.len() && out0.len() == out2.len() && out0.len() == out3.len());
    #[cfg(not(eurydice))]
    debug_assert!(
        data[0].len() == data[1].len()
            && data[0].len() == data[2].len()
            && data[0].len() == data[3].len()
    );

    let s = absorb4::<RATE, DELIM>(data);
    squeeze4::<RATE>(s, out0, out1, out2, out3);
}

#[hax_lib::attributes]
impl KeccakState<4, Vec256> {
    #[inline(always)]
    #[hax_lib::requires(
        valid_rate(RATE) &&
        start.to_int() + RATE.to_int() <= out0.len().to_int() &&
        out0.len() == out1.len() &&
        out0.len() == out2.len() &&
        out0.len() == out3.len()
    )]
    #[hax_lib::ensures(|_|
        future(out0).len() == out0.len() &&
        future(out1).len() == out1.len() &&
        future(out2).len() == out2.len() &&
        future(out3).len() == out3.len()
    )]
    pub(crate) fn squeeze_next_block<const RATE: usize>(
        &mut self,
        out0: &mut [u8],
        out1: &mut [u8],
        out2: &mut [u8],
        out3: &mut [u8],
        start: usize,
    ) {
        self.keccakf1600();
        self.squeeze4::<RATE>(out0, out1, out2, out3, start, RATE);
    }

    /// Write out the first block of Keccak output.
    ///
    /// This function MUST NOT be called after any of the other `squeeze_*`
    /// functions have been called, since that would result in a duplicate output
    /// block.
    #[hax_lib::requires(
        valid_rate(RATE) &&
        RATE <= out0.len() &&
        out0.len() == out1.len() &&
        out0.len() == out2.len() &&
        out0.len() == out3.len()
    )]
    #[hax_lib::ensures(|_|
        future(out0).len() == out0.len() &&
        future(out1).len() == out1.len() &&
        future(out2).len() == out2.len() &&
        future(out3).len() == out3.len()
    )]
    pub(crate) fn squeeze_first_block<const RATE: usize>(
        &self,
        out0: &mut [u8],
        out1: &mut [u8],
        out2: &mut [u8],
        out3: &mut [u8],
    ) {
        self.squeeze4::<RATE>(out0, out1, out2, out3, 0, RATE);
    }

    #[inline(always)]
    #[hax_lib::requires(
        valid_rate(RATE) &&
        3 * RATE <= out0.len() &&
        out0.len() == out1.len() &&
        out0.len() == out2.len() &&
        out0.len() == out3.len()
    )]
    #[hax_lib::ensures(|_|
        future(out0).len() == out0.len() &&
        future(out1).len() == out1.len() &&
        future(out2).len() == out2.len() &&
        future(out3).len() == out3.len()
    )]
    pub(crate) fn squeeze_first_three_blocks<const RATE: usize>(
        &mut self,
        out0: &mut [u8],
        out1: &mut [u8],
        out2: &mut [u8],
        out3: &mut [u8],
    ) {
        self.squeeze4::<RATE>(out0, out1, out2, out3, 0, RATE);

        self.keccakf1600();
        self.squeeze4::<RATE>(out0, out1, out2, out3, RATE, RATE);

        self.keccakf1600();
        self.squeeze4::<RATE>(out0, out1, out2, out3, 2 * RATE, RATE);
    }

    #[inline(always)]
    #[hax_lib::requires(
        valid_rate(RATE) &&
        5 * RATE <= out0.len() &&
        out0.len() == out1.len() &&
        out0.len() == out2.len() &&
        out0.len() == out3.len()
    )]
    #[hax_lib::ensures(|_|
        future(out0).len() == out0.len() &&
        future(out1).len() == out1.len() &&
        future(out2).len() == out2.len() &&
        future(out3).len() == out3.len()
    )]
    pub(crate) fn squeeze_first_five_blocks<const RATE: usize>(
        &mut self,
        out0: &mut [u8],
        out1: &mut [u8],
        out2: &mut [u8],
        out3: &mut [u8],
    ) {
        self.squeeze4::<RATE>(out0, out1, out2, out3, 0, RATE);

        self.keccakf1600();
        self.squeeze4::<RATE>(out0, out1, out2, out3, RATE, RATE);

        self.keccakf1600();
        self.squeeze4::<RATE>(out0, out1, out2, out3, 2 * RATE, RATE);

        self.keccakf1600();
        self.squeeze4::<RATE>(out0, out1, out2, out3, 3 * RATE, RATE);

        self.keccakf1600();
        self.squeeze4::<RATE>(out0, out1, out2, out3, 4 * RATE, RATE);
    }
}
