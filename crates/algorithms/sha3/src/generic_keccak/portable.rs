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

    /// Final partial-block step of the squeeze phase: if `output_rem != 0`,
    /// apply one Keccak-f permutation and then extract the trailing
    /// `output_rem` bytes of output into the tail of `out`; otherwise
    /// a no-op.  Factored out of `squeeze` so the final post-condition
    /// reconciling impl vs spec is proved within a small dedicated VC.
    #[inline(always)]
    #[hax_lib::requires(
        valid_rate(RATE) &&
        out.len() < usize::MAX - 200 &&
        output_rem < RATE &&
        output_rem <= out.len()
    )]
    #[hax_lib::ensures(|_| (future(out).len() == out.len()).to_prop() & {
        fstar!(r#"
            let out_len = Core_models.Slice.impl__len #u8 $out in
            let (st_spec, out_spec) =
                Hacspec_sha3.Sponge.squeeze_last out_len $self_.st $out
                    $RATE $output_rem in
            self_e_future.Libcrux_sha3.Generic_keccak.f_st == st_spec /\
            (out_future <: Seq.seq u8) == (out_spec <: Seq.seq u8)
        "#)
    })]
    pub(crate) fn squeeze_last<const RATE: usize>(&mut self, out: &mut [u8], output_rem: usize) {
        #[cfg(hax)]
        let out_original = out.to_vec();
        #[cfg(hax)]
        let self_original_st = self.st;
        if output_rem != 0 {
            hax_lib::fstar!(r#"EquivImplSpec.Keccakf.Portable.lemma_keccakf1600_portable $self"#);
            self.keccakf1600();
            self.squeeze::<RATE>(out, out.len() - output_rem, output_rem);
            hax_lib::fstar!(
                r#"let out_len = Core_models.Slice.impl__len #u8 $out in
                   let offset = out_len -! $output_rem in
                   let out_orig_arr : t_Array u8 out_len =
                     Alloc.Vec.impl_1__as_slice $out_original <: t_Slice _ in
                   let new_state = Hacspec_sha3.Keccak_f.keccak_f $self_original_st in
                   assert (v $RATE <= 200);
                   assert ($self.st == new_state);
                   let aux (k: nat{k < v out_len})
                     : Lemma (Seq.index ($out <: Seq.seq u8) k ==
                              Seq.index ((Hacspec_sha3.Sponge.squeeze_state out_len
                                 new_state
                                 out_orig_arr offset $output_rem) <: Seq.seq u8) k)
                     = let i : usize = mk_usize k in
                       assert (v i == k);
                       if k < v offset then ()
                       else begin
                         assert (v i - v offset < v $output_rem);
                         assert ((v i - v offset) / 8 < 25)
                       end
                   in
                   FStar.Classical.forall_intro aux;
                   Seq.lemma_eq_intro ($out <: Seq.seq u8)
                     ((Hacspec_sha3.Sponge.squeeze_state out_len
                        new_state
                        out_orig_arr offset $output_rem) <: Seq.seq u8)"#
            );
        }
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
///
/// The ensures clause asserts direct equality with the spec function
/// `Hacspec_sha3.Sponge.absorb`. The loop invariant uses the spec helper
/// `absorb_blocks` (block-indexed analogue of `absorb_rec`, avoiding the
/// slice-of-slice reasoning that triggers a Z3 4.13.3 LP-solver bug in
/// older proofs based on `absorb_rec` recursion).
#[hax_lib::requires(valid_rate(RATE))]
#[hax_lib::ensures(|result| fstar!(r#"
    $result.st ==
      Hacspec_sha3.Sponge.absorb $RATE $DELIM $input
"#))]
#[hax_lib::fstar::options("--fuel 1 --ifuel 1 --z3rlimit 800 --split_queries always")]
#[inline]
pub(crate) fn absorb<const RATE: usize, const DELIM: u8>(input: &[u8]) -> KeccakState<1, u64> {
    let mut s = KeccakState::<1, u64>::new();
    let input_len = input.len();
    let input_blocks = input_len / RATE;
    let input_rem = input_len % RATE;
    hax_lib::fstar!(
        r#"let zeros : t_Array u64 (mk_usize 25) =
               Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 25) in
           Hacspec_sha3.Sponge.Lemmas.lemma_absorb_blocks_base
               zeros $RATE (mk_usize 0) $input"#
    );
    for i in 0..input_blocks {
        hax_lib::loop_invariant!(|i: usize| {
            fstar!(
                r#"let zeros : t_Array u64 (mk_usize 25) =
                       Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 25) in
                   v $i <= v $input_blocks /\
                   $s.st ==
                     Hacspec_sha3.Sponge.absorb_blocks
                       zeros $RATE (mk_usize 0) $i $input"#
            )
        });
        #[cfg(hax)]
        lemma_mul_succ_le(i, input_blocks, RATE);

        hax_lib::fstar!(
            r#"let zeros : t_Array u64 (mk_usize 25) =
                   Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 25) in
               let inputs : t_Array (t_Slice u8) (mk_usize 1) =
                   let list = [ $input ] in
                   FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                   Rust_primitives.Hax.array_of_list 1 list in
               assert (inputs.[ mk_usize 0 ] == $input);
               EquivImplSpec.Sponge.Portable.Steps.lemma_absorb_block_portable
                   $RATE $s inputs ($i *! $RATE);
               Hacspec_sha3.Sponge.Lemmas.lemma_absorb_blocks_tail
                   zeros $RATE (mk_usize 0) $i ($i +! mk_usize 1) $input"#
        );

        s.absorb_block::<RATE>(&[input], i * RATE);
    }
    hax_lib::fstar!(
        r#"let zeros : t_Array u64 (mk_usize 25) =
               Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 25) in
           let inputs : t_Array (t_Slice u8) (mk_usize 1) =
               let list = [ $input ] in
               FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
               Rust_primitives.Hax.array_of_list 1 list in
           assert (inputs.[ mk_usize 0 ] == $input);
           EquivImplSpec.Sponge.Portable.Steps.lemma_absorb_last_portable
               $RATE $DELIM $s inputs ($input_len -! $input_rem) $input_rem;
           Hacspec_sha3.Sponge.Lemmas.lemma_absorb_rec_via_blocks
               zeros $RATE $DELIM $input"#
    );
    s.absorb_final::<RATE, DELIM>(&[input], input_len - input_rem, input_rem);
    s
}

/// Squeeze phase of `keccak1`: extract `output.len()` bytes from `s`,
/// applying Keccak-f between each full rate-byte block of output.
///
/// The ensures clause asserts direct equality with the spec function
/// `Hacspec_sha3.Sponge.squeeze`.  Buffer-independence is proved
/// *inline* through the loop invariant: at iteration `i`, the impl's
/// output agrees with the spec's run (anchored on a zeros buffer) on
/// the already-written prefix `[0, i*RATE)` and preserves the initial
/// input buffer on the tail `[i*RATE, output_len)`.  The per-byte
/// ensures clause of `f_squeeze` (bytes inside the write range are
/// determined by state, bytes outside are preserved) makes the
/// block-by-block step go through without needing a separate
/// buffer-independence lemma.
#[hax_lib::requires(
    valid_rate(RATE) &&
    output.len() < usize::MAX - 200
)]
#[hax_lib::ensures(|_| (future(output).len() == output.len()).to_prop() & {
    fstar!(r#"(output_future <: t_Slice u8) ==
              (Hacspec_sha3.Sponge.squeeze
                 (Core_models.Slice.impl__len #u8 $output)
                 $s.st
                 $RATE <: t_Slice u8)"#)
})]
#[hax_lib::fstar::options("--fuel 1 --ifuel 1 --z3rlimit 800 --split_queries always")]
#[inline]
pub(crate) fn squeeze<const RATE: usize>(mut s: KeccakState<1, u64>, output: &mut [u8]) {
    let output_len = output.len();
    let output_blocks = output_len / RATE;
    let output_rem = output_len % RATE;

    #[cfg(hax)]
    let s_init_st = s.st;
    #[cfg(hax)]
    let output_initial = output.to_vec();

    if output_blocks == 0 {
        s.squeeze::<RATE>(output, 0, output_len);
        hax_lib::fstar!(
            r#"let zeros : t_Array u8 $output_len =
                   Rust_primitives.Hax.repeat (mk_u8 0) $output_len in
               let spec_out : t_Array u8 $output_len =
                   Hacspec_sha3.Sponge.squeeze_state $output_len $s_init_st
                       zeros (mk_usize 0) $output_len in
               assert (v $output_len < v $RATE);
               assert (v $RATE <= 200);
               let aux (k: nat{k < v $output_len })
                 : Lemma (Seq.index ($output <: Seq.seq u8) k ==
                          Seq.index (spec_out <: Seq.seq u8) k)
                 = let i : usize = mk_usize k in
                   assert (v i == k);
                   assert (v i / 8 < 25)
               in
               FStar.Classical.forall_intro aux;
               Seq.lemma_eq_intro ($output <: Seq.seq u8) (spec_out <: Seq.seq u8)"#
        );
    } else {
        s.squeeze::<RATE>(output, 0, RATE);

        hax_lib::fstar!(
            r#"let output_initial_arr : t_Array u8 $output_len =
                   Alloc.Vec.impl_1__as_slice $output_initial <: t_Slice _ in
               let zeros : t_Array u8 $output_len =
                   Rust_primitives.Hax.repeat (mk_u8 0) $output_len in
               let out0 = Hacspec_sha3.Sponge.squeeze_state $output_len
                   $s_init_st zeros (mk_usize 0) $RATE in
               Libcrux_sha3.Proof_utils.Lemmas.lemma_div_mul_mod $output_len $RATE;
               Hacspec_sha3.Sponge.Lemmas.lemma_squeeze_blocks_base
                   $output_len $s_init_st $RATE (mk_usize 1) out0;
               assert (v $RATE <= 200);
               let aux_write (k: nat)
                 : Lemma
                     (ensures
                        (k < v $RATE /\ k < v $output_len ==>
                           Seq.index ($output <: Seq.seq u8) k ==
                           Seq.index (out0 <: Seq.seq u8) k))
                 = if k < v $RATE && k < v $output_len then begin
                     let i : usize = mk_usize k in
                     assert (v i == k);
                     assert (v i / 8 < 25)
                   end
               in
               let aux_tail (k: nat)
                 : Lemma
                     (ensures
                        (v $RATE <= k /\ k < v $output_len ==>
                           Seq.index ($output <: Seq.seq u8) k ==
                           Seq.index (output_initial_arr <: Seq.seq u8) k))
                 = if v $RATE <= k && k < v $output_len then begin
                     let i : usize = mk_usize k in
                     assert (v i == k)
                   end
               in
               FStar.Classical.forall_intro aux_write;
               FStar.Classical.forall_intro aux_tail"#
        );

        for i in 1..output_blocks {
            hax_lib::loop_invariant!(|i: usize| (output.len() == output_len).to_prop() & {
                fstar!(
                    r#"let output_initial_arr : t_Array u8 $output_len =
                           Alloc.Vec.impl_1__as_slice $output_initial <: t_Slice _ in
                       let zeros : t_Array u8 $output_len =
                           Rust_primitives.Hax.repeat (mk_u8 0) $output_len in
                       let out0 = Hacspec_sha3.Sponge.squeeze_state $output_len
                           $s_init_st zeros (mk_usize 0) $RATE in
                       let (spec_st, spec_out) =
                           Hacspec_sha3.Sponge.squeeze_blocks $output_len $s_init_st
                               $RATE (mk_usize 1) $i out0 in
                       v $i >= 1 /\ v $i <= v $output_blocks /\
                       v $i * v $RATE <= v $output_len /\
                       $s.st == spec_st /\
                       (forall (k: nat). k < v $i * v $RATE /\ k < v $output_len ==>
                          Seq.index ($output <: Seq.seq u8) k ==
                          Seq.index (spec_out <: Seq.seq u8) k) /\
                       (forall (k: nat). v $i * v $RATE <= k /\ k < v $output_len ==>
                          Seq.index ($output <: Seq.seq u8) k ==
                          Seq.index (output_initial_arr <: Seq.seq u8) k)"#
                )
            });

            #[cfg(hax)]
            lemma_mul_succ_le(i, output_blocks, RATE);
            hax_lib::fstar!(
                r#"let output_initial_arr : t_Array u8 $output_len =
                       Alloc.Vec.impl_1__as_slice $output_initial <: t_Slice _ in
                   let zeros : t_Array u8 $output_len =
                       Rust_primitives.Hax.repeat (mk_u8 0) $output_len in
                   let out0 = Hacspec_sha3.Sponge.squeeze_state $output_len
                       $s_init_st zeros (mk_usize 0) $RATE in
                   Libcrux_sha3.Proof_utils.Lemmas.lemma_div_mul_mod $output_len $RATE;
                   Libcrux_sha3.Proof_utils.Lemmas.lemma_mul_succ_le $i $output_blocks $RATE;
                   assert (v $i * v $RATE + v $RATE <= v $output_len);
                   Hacspec_sha3.Sponge.Lemmas.lemma_squeeze_blocks_tail $output_len
                       $s_init_st $RATE (mk_usize 1) $i ($i +! mk_usize 1) out0;
                   EquivImplSpec.Keccakf.Portable.lemma_keccakf1600_portable $s"#
            );

            s.keccakf1600();
            s.squeeze::<RATE>(output, i * RATE, RATE);

            hax_lib::fstar!(
                r#"let output_initial_arr : t_Array u8 $output_len =
                       Alloc.Vec.impl_1__as_slice $output_initial <: t_Slice _ in
                   let zeros : t_Array u8 $output_len =
                       Rust_primitives.Hax.repeat (mk_u8 0) $output_len in
                   let out0 = Hacspec_sha3.Sponge.squeeze_state $output_len
                       $s_init_st zeros (mk_usize 0) $RATE in
                   FStar.Math.Lemmas.distributivity_add_left (v $i) 1 (v $RATE);
                   let aux_write_step (k: nat{k < v $output_len })
                       : Lemma
                         (ensures
                            (k < (v $i + 1) * v $RATE ==>
                              (let (_, spec_out_new) =
                                  Hacspec_sha3.Sponge.squeeze_blocks $output_len $s_init_st $RATE
                                    (mk_usize 1) ($i +! mk_usize 1) out0
                                in
                                Seq.index ($output <: Seq.seq u8) k ==
                                Seq.index (spec_out_new <: Seq.seq u8) k))) =
                     if k < (v $i + 1) * v $RATE
                     then
                       let ii:usize = mk_usize k in
                       assert (v ii == k);
                       if k < v $i * v $RATE
                       then ()
                       else
                         (assert (v $i * v $RATE <= k);
                          assert ((v $i + 1) * v $RATE == v $i * v $RATE + v $RATE);
                          assert (k - v $i * v $RATE < v $RATE);
                          assert ((k - v $i * v $RATE) / 8 < 25))
                   in
                   let aux_tail_step (k: nat{k < v $output_len })
                       : Lemma
                         (ensures
                            ((v $i + 1) * v $RATE <= k ==>
                              Seq.index ($output <: Seq.seq u8) k ==
                              Seq.index (output_initial_arr <: Seq.seq u8) k)) =
                     if (v $i + 1) * v $RATE <= k
                     then
                       let ii:usize = mk_usize k in
                       assert (v ii == k);
                       assert ((v $i + 1) * v $RATE == v $i * v $RATE + v $RATE);
                       assert (v $i * v $RATE + v $RATE <= k)
                   in
                   FStar.Classical.forall_intro aux_write_step;
                   FStar.Classical.forall_intro aux_tail_step"#
            );
        }
        hax_lib::fstar!(
            r#"let out0 = Hacspec_sha3.Sponge.squeeze_state $output_len
                   $s_init_st (Rust_primitives.Hax.repeat (mk_u8 0) $output_len)
                   (mk_usize 0) $RATE in
               let (spec_st, spec_out) =
                   Hacspec_sha3.Sponge.squeeze_blocks $output_len $s_init_st
                       $RATE (mk_usize 1) $output_blocks out0 in
               Libcrux_sha3.Proof_utils.Lemmas.lemma_div_mul_mod $output_len $RATE;
               Hacspec_sha3.Sponge.Lemmas.lemma_squeeze_last_extensional
                   $output_len spec_st $output spec_out $RATE $output_rem"#
        );
        s.squeeze_last::<RATE>(output, output_rem);

        hax_lib::fstar!(
            r#"let out0 = Hacspec_sha3.Sponge.squeeze_state $output_len
                   $s_init_st (Rust_primitives.Hax.repeat (mk_u8 0) $output_len)
                   (mk_usize 0) $RATE in
               let (spec_st, spec_out) =
                   Hacspec_sha3.Sponge.squeeze_blocks $output_len $s_init_st
                       $RATE (mk_usize 1) $output_blocks out0 in
               let (_, final_spec) =
                   Hacspec_sha3.Sponge.squeeze_last $output_len
                       spec_st spec_out $RATE $output_rem in
               Libcrux_sha3.Proof_utils.Lemmas.lemma_div_mul_mod $output_len $RATE;
               Seq.lemma_eq_intro ($output <: Seq.seq u8) (final_spec <: Seq.seq u8);
               Hacspec_sha3.Sponge.Lemmas.lemma_squeeze_unfold $output_len $s_init_st $RATE;
               let spec_result : t_Array u8 $output_len =
                   Hacspec_sha3.Sponge.squeeze $output_len $s_init_st $RATE in
               Hacspec_sha3.Sponge.Lemmas.lemma_seq_trans #$output_len
                   ($output <: Seq.seq u8) final_spec spec_result"#
        );
    }
}

#[hax_lib::requires(
    valid_rate(RATE) &&
    output.len() < usize::MAX - 200
)]
#[hax_lib::ensures(|_| (future(output).len() == output.len()).to_prop() & {
    fstar!(r#"(output_future <: t_Slice u8) ==
              (Hacspec_sha3.Sponge.keccak
                 (Core_models.Slice.impl__len #u8 $output)
                 $RATE $DELIM $input <: t_Slice u8)"#)
})]
#[hax_lib::fstar::options("--fuel 1 --ifuel 1 --z3rlimit 200")]
#[inline]
pub(crate) fn keccak1<const RATE: usize, const DELIM: u8>(input: &[u8], output: &mut [u8]) {
    let s = absorb::<RATE, DELIM>(input);
    squeeze::<RATE>(s, output);
}
