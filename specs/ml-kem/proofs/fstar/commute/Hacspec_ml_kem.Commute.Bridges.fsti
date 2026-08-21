module Hacspec_ml_kem.Commute.Bridges
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models
open Libcrux_ml_kem.Vector.Traits.Spec
open Hacspec_ml_kem.Commute.Chunk

module P  = Hacspec_ml_kem.Parameters
module T  = Libcrux_ml_kem.Vector.Traits
module TS = Libcrux_ml_kem.Vector.Traits.Spec
module N  = Hacspec_ml_kem.Ntt
module IN = Hacspec_ml_kem.Invert_ntt
module VS = Libcrux_ml_kem.Vector.Spec
module VV = Libcrux_ml_kem.Vector

(* ============================================================================
   ABSTRACT INTERFACE for the commute-layer NTT/INTT hacspec bridges.

   Purpose (2026-08-21, ml-kem verification restore): consumers of this module
   (Libcrux_ml_kem.Ntt, Libcrux_ml_kem.Invert_ntt, Commute.Matrix_bridge, and
   transitively the impl Ntt/Invert_ntt/Polynomial) typecheck against this
   cheap, stable `.fsti.checked` — NOT against the heavy `Bridges.fst.checked`,
   whose per-lane `lemma_*_lane_bridge` proofs are not robustly cold-provable
   (symbolic i/4, i%4 + SIMD-helper opaque-reveal chains that hang cold).
   The 14 declarations below are exactly the ones referenced outside this
   module; the ~30 per-lane lane-bridge helpers + Level-B composition helpers
   stay module-private (absent from this interface).

   Declaration order MUST match the `let` order in the `.fst`, since interface
   `val` order gates the implementation match (Error 233 otherwise); none of
   these carry an SMTPat, so the order is a pure implementation-match concern.
   ============================================================================ *)

(*** Phase 7a (track A) — forward/inverse per-vector NTT layer hacspec bridges.
     Each lifts the trait's per-lane branch post to a single per-vector
     function-form equation against `N.ntt_layer_n` / `IN.ntt_inverse_layer_n`. ***)

val lemma_ntt_layer_1_step_to_hacspec
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) (zeta0 zeta1 zeta2 zeta3: i16) :
  Lemma
    (requires TS.ntt_layer_1_step_pre (T.f_repr vec) zeta0 zeta1 zeta2 zeta3)
    (ensures
       (let r = T.f_ntt_layer_1_step vec zeta0 zeta1 zeta2 zeta3 in
        mont_i16_to_spec_array (sz 16) (T.f_repr r) ==
          N.ntt_layer_n (mk_usize 16)
            (mont_i16_to_spec_array (sz 16) (T.f_repr vec))
            (mk_usize 2)
            (Rust_primitives.unsize (zetas_4_ zeta0 zeta1 zeta2 zeta3))))

val lemma_inv_ntt_layer_1_step_to_hacspec
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) (zeta0 zeta1 zeta2 zeta3: i16) :
  Lemma
    (requires TS.inv_ntt_layer_1_step_pre (T.f_repr vec) zeta0 zeta1 zeta2 zeta3)
    (ensures
       (let r = T.f_inv_ntt_layer_1_step vec zeta0 zeta1 zeta2 zeta3 in
        mont_i16_to_spec_array (sz 16) (T.f_repr r) ==
          IN.ntt_inverse_layer_n (mk_usize 16)
            (mont_i16_to_spec_array (sz 16) (T.f_repr vec))
            (mk_usize 2)
            (Rust_primitives.unsize (zetas_4_ zeta0 zeta1 zeta2 zeta3))))

val lemma_inv_ntt_layer_3_step_to_hacspec
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) (zeta0: i16) :
  Lemma
    (requires TS.inv_ntt_layer_3_step_pre (T.f_repr vec) zeta0)
    (ensures
       (let r = T.f_inv_ntt_layer_3_step vec zeta0 in
        mont_i16_to_spec_array (sz 16) (T.f_repr r) ==
          IN.ntt_inverse_layer_n (mk_usize 16)
            (mont_i16_to_spec_array (sz 16) (T.f_repr vec))
            (mk_usize 8)
            (Rust_primitives.unsize (zetas_1_ zeta0))))

val lemma_inv_ntt_layer_2_step_to_hacspec
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) (zeta0 zeta1: i16) :
  Lemma
    (requires TS.inv_ntt_layer_2_step_pre (T.f_repr vec) zeta0 zeta1)
    (ensures
       (let r = T.f_inv_ntt_layer_2_step vec zeta0 zeta1 in
        mont_i16_to_spec_array (sz 16) (T.f_repr r) ==
          IN.ntt_inverse_layer_n (mk_usize 16)
            (mont_i16_to_spec_array (sz 16) (T.f_repr vec))
            (mk_usize 4)
            (Rust_primitives.unsize (zetas_2_ zeta0 zeta1))))

val lemma_ntt_layer_2_step_to_hacspec
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) (zeta0 zeta1: i16) :
  Lemma
    (requires TS.ntt_layer_2_step_pre (T.f_repr vec) zeta0 zeta1)
    (ensures
       (let r = T.f_ntt_layer_2_step vec zeta0 zeta1 in
        mont_i16_to_spec_array (sz 16) (T.f_repr r) ==
          N.ntt_layer_n (mk_usize 16)
            (mont_i16_to_spec_array (sz 16) (T.f_repr vec))
            (mk_usize 4)
            (Rust_primitives.unsize (zetas_2_ zeta0 zeta1))))

val lemma_ntt_layer_3_step_to_hacspec
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) (zeta0: i16) :
  Lemma
    (requires TS.ntt_layer_3_step_pre (T.f_repr vec) zeta0)
    (ensures
       (let r = T.f_ntt_layer_3_step vec zeta0 in
        mont_i16_to_spec_array (sz 16) (T.f_repr r) ==
          N.ntt_layer_n (mk_usize 16)
            (mont_i16_to_spec_array (sz 16) (T.f_repr vec))
            (mk_usize 8)
            (Rust_primitives.unsize (zetas_1_ zeta0))))

(*** Layer 4+ chunk-pair inverse step -> per-lane inv_butterfly bridge. ***)
val lemma_inv_ntt_layer_int_vec_step_reduce_to_hacspec
    (a_arr b_arr r0_arr r1_arr: t_Array i16 (mk_usize 16))
    (zeta_r: i16) :
  Lemma
    (requires
       (forall (i: nat). i < 16 ==>
          mont_i16_to_spec_fe (Seq.index r0_arr i) ==
          P.impl_FieldElement__add
            (mont_i16_to_spec_fe (Seq.index a_arr i))
            (mont_i16_to_spec_fe (Seq.index b_arr i))) /\
       (forall (i: nat). i < 16 ==>
          mont_i16_to_spec_fe (Seq.index r1_arr i) ==
          P.impl_FieldElement__mul
            (mont_i16_to_spec_fe zeta_r)
            (P.impl_FieldElement__sub
              (mont_i16_to_spec_fe (Seq.index b_arr i))
              (mont_i16_to_spec_fe (Seq.index a_arr i)))))
    (ensures
       (forall (i: nat). i < 16 ==>
          mont_i16_to_spec_fe (Seq.index r0_arr i) ==
          (IN.inv_butterfly (mont_i16_to_spec_fe zeta_r)
                             (mont_i16_to_spec_fe (Seq.index a_arr i))
                             (mont_i16_to_spec_fe (Seq.index b_arr i)))._1) /\
       (forall (i: nat). i < 16 ==>
          mont_i16_to_spec_fe (Seq.index r1_arr i) ==
          (IN.inv_butterfly (mont_i16_to_spec_fe zeta_r)
                             (mont_i16_to_spec_fe (Seq.index a_arr i))
                             (mont_i16_to_spec_fe (Seq.index b_arr i)))._2))

(*** poly_to_spec = to_spec_poly_plain bridge (extraction-side lift == commute lift). ***)
val poly_to_spec_eq_to_spec_poly_plain
    (#vV: Type0) {| i0: T.t_Operations vV |}
    (p: VV.t_PolynomialRingElement vV)
  : Lemma
    (VS.poly_to_spec #vV p == to_spec_poly_plain #vV p)

(*** USER-14 — Layer 4+ cross-vector inverse-NTT composition.

     `cross_vec_hyp` is the flat per-vector hypothesis the inverse-NTT layer-4+
     loop accumulates.  It is kept `opaque_to_smt` (Z3 instantiates one flat
     quantifier at (m,l); the body is revealed only at the single instantiation
     site).  Exposed transparently here (not as an abstract `val`) because
     Libcrux_ml_kem.Invert_ntt reveal_opaque's it directly at its post-loop
     bridge. ***)
[@@ "opaque_to_smt"]
let cross_vec_hyp
    (#vV: Type0) {| iop: T.t_Operations vV |}
    (cin cout: t_Array vV (mk_usize 16)) (step_vec: pos) (zs: t_Slice P.t_FieldElement)
    (m: nat) (l: nat) : prop =
  (m < 16 /\ l < 16) ==>
    (let block : nat = m / (2 * step_vec) in
     let pos   : nat = m % (2 * step_vec) in
     block < Seq.length zs /\
     (pos < step_vec ==>
        m + step_vec < 16 /\
        mont_i16_to_spec_fe (Seq.index (T.f_repr (Seq.index cout m)) l) ==
          (IN.inv_butterfly (Seq.index zs block)
             (mont_i16_to_spec_fe (Seq.index (T.f_repr (Seq.index cin m)) l))
             (mont_i16_to_spec_fe (Seq.index (T.f_repr (Seq.index cin (m + step_vec))) l)))._1) /\
     (pos >= step_vec ==>
        m >= step_vec /\
        mont_i16_to_spec_fe (Seq.index (T.f_repr (Seq.index cout m)) l) ==
          (IN.inv_butterfly (Seq.index zs block)
             (mont_i16_to_spec_fe (Seq.index (T.f_repr (Seq.index cin (m - step_vec))) l))
             (mont_i16_to_spec_fe (Seq.index (T.f_repr (Seq.index cin m)) l)))._2))

(* === USER-14 zeta correspondence axiom (user-approved Option B, 2026-05-30) ===
   The impl Montgomery zeta `Libcrux_ml_kem.Polynomial.zeta` is exposed to clients
   as an `assume val` with a BOUND-ONLY postcondition (result in [-1664,1664]); its
   concrete value is opaque cross-module.  This axiom records its correspondence to
   the spec plain zeta table `N.v_ZETAS`, which is validated at runtime by
   `ntt_matches_spec` / `full_ntt_multiply_chain_matches_spec` in `src/ntt.rs`.
   Needed by the table-form posts of `invert_ntt_at_layer_4_plus` and (downstream)
   `invert_ntt_montgomery` (USER-15). *)
(* NOTE: this is an assumed axiom — its `.fst` implementation is `= admit ()`
   (F* forbids `assume val` in an interface).  Same trust as the prior
   `assume val`: no proof, correspondence validated at runtime in `src/ntt.rs`. *)
val lemma_zeta_eq_vzetas (k: usize)
  : Lemma (requires v k < 128)
          (ensures mont_i16_to_spec_fe (Libcrux_ml_kem.Polynomial.zeta k) == N.v_ZETAS.[ k ])

(*** USER-14 end-to-end: from the per-vector cross_vec_hyp forall, conclude the
     function's strengthened table-form post for layers 4..7. ***)
val lemma_layer_4_plus_post_from_cross_vec
    (#vV: Type0) {| iop: T.t_Operations vV |}
    (re_in re_out: VV.t_PolynomialRingElement vV)
    (layer len: usize)
    (step_vec: pos)
    (zs: t_Slice P.t_FieldElement)
  : Lemma
    (requires
      (v layer == 4 \/ v layer == 5 \/ v layer == 6 \/ v layer == 7) /\
      v len == pow2 (v layer) /\
      v len == 16 * step_vec /\
      Seq.length zs == 128 / pow2 (v layer) /\
      (let groups = 128 / pow2 (v layer) in
       forall (round: nat). round < groups ==>
         Seq.index zs round == N.v_ZETAS.[ sz (2 * groups - 1 - round) ]) /\
      (forall (m: nat) (l: nat).
         cross_vec_hyp #vV re_in.VV.f_coefficients re_out.VV.f_coefficients step_vec zs m l))
    (ensures
      to_spec_poly_mont #vV re_out ==
        IN.ntt_inverse_layer (to_spec_poly_mont #vV re_in) layer)

(*** USER-14 nonlinear index helper: partner j+sv sits in j's block, high half. ***)
val lemma_vec_partner_hi (j: nat) (sv: pos)
  : Lemma (requires j % (2 * sv) < sv)
          (ensures (j + sv) / (2 * sv) == j / (2 * sv) /\
                   (j + sv) % (2 * sv) == j % (2 * sv) + sv /\
                   j % (2 * sv) + sv >= sv)

(*** USER-14 keystone: one inv step (vectors j, j+step_vec) -> cross_vec_hyp for both. ***)
val lemma_cross_vec_from_step
    (#vV: Type0) {| iop: T.t_Operations vV |}
    (cin cout: t_Array vV (mk_usize 16))
    (step_vec: pos)
    (zs: t_Slice P.t_FieldElement)
    (j: nat)
    (zeta_r: i16)
  : Lemma
    (requires
      j + step_vec < 16 /\
      j % (2 * step_vec) < step_vec /\
      j / (2 * step_vec) < Seq.length zs /\
      Seq.index zs (j / (2 * step_vec)) == mont_i16_to_spec_fe zeta_r /\
      (forall (l: nat). l < 16 ==>
         mont_i16_to_spec_fe (Seq.index (T.f_repr (Seq.index cout j)) l) ==
           (IN.inv_butterfly (mont_i16_to_spec_fe zeta_r)
              (mont_i16_to_spec_fe (Seq.index (T.f_repr (Seq.index cin j)) l))
              (mont_i16_to_spec_fe (Seq.index (T.f_repr (Seq.index cin (j + step_vec))) l)))._1) /\
      (forall (l: nat). l < 16 ==>
         mont_i16_to_spec_fe (Seq.index (T.f_repr (Seq.index cout (j + step_vec))) l) ==
           (IN.inv_butterfly (mont_i16_to_spec_fe zeta_r)
              (mont_i16_to_spec_fe (Seq.index (T.f_repr (Seq.index cin j)) l))
              (mont_i16_to_spec_fe (Seq.index (T.f_repr (Seq.index cin (j + step_vec))) l)))._2))
    (ensures
      (forall (l: nat). l < 16 ==> cross_vec_hyp #vV cin cout step_vec zs j l) /\
      (forall (l: nat). l < 16 ==> cross_vec_hyp #vV cin cout step_vec zs (j + step_vec) l))

(*** USER-14 frame: cross_vec_hyp reads `cout` only at index m. ***)
val lemma_cross_vec_frame
    (#vV: Type0) {| iop: T.t_Operations vV |}
    (cin cout1 cout2: t_Array vV (mk_usize 16))
    (step_vec: pos)
    (zs: t_Slice P.t_FieldElement)
    (m l: nat)
  : Lemma
    (requires m < 16 /\ Seq.index cout1 m == Seq.index cout2 m)
    (ensures cross_vec_hyp #vV cin cout1 step_vec zs m l <==>
             cross_vec_hyp #vV cin cout2 step_vec zs m l)
