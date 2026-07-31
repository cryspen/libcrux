module Libcrux_core_models.Trusted.Intrinsics
#set-options "--fuel 0 --ifuel 1 --z3rlimit 30"
open FStar.Mul
open Core_models

(* ============================================================================
   THE TRUSTED INTRINSICS AXIOMS — hand-written.  AUDIT ENTRY POINT.

   POLICY: this module is the ONLY legal home for a hand-written intrinsics
   axiom.  Algorithm crates (libcrux-ml-kem, libcrux-ml-dsa, libcrux-sha3) MUST
   contain ZERO assumptions about intrinsics: they may define proven lemmas for
   convenience, but every axiom lives here (or is generated, see below).
   New axiom => add it HERE, with its differential-test justification.

   WHAT AN AUDITOR NEEDS TO READ (the whole x86 intrinsics trusted base):

     1. `src/core_arch/x86.rs`               — the bit-vector models, PLUS the
                                               opaque (un-modeled) stubs, which
                                               extract to ~88 `assume val
                                               e_mm256_OP'`.  Those are the
                                               uninterpreted primitives = "the
                                               CPU".
     2. `src/core_arch/x86/interpretations.rs`
                                             — the integer-vector models, and in
                                               its `lemmas` submodule the ~75
                                               `mk_lift_lemma!` declarations that
                                               extract to
                                               `…Interpretations.Int_vec.Lemmas`
                                               as `[@@ v_LIFT_LEMMA] assume val`.
     3. THIS FILE                            — the axioms that have no Rust
                                               counterpart, i.e. lifts for ops
                                               whose `mk_lift_lemma!` was never
                                               declared.
     4. `proofs/intrinsics-trust-index.{csv,md}` + the `mk!` / `assert_eq!`
                                               differential tests in (2)
                                             — the EVIDENCE.  Nothing in the F*
                                               proof chain consumes these; they
                                               are the justification for 1-3.
                                               NOTE: those tests are
                                               `#[cfg(any(target_arch = "x86",
                                               target_arch = "x86_64"))]`, so a
                                               green `cargo test` on arm64 proves
                                               NOTHING about them.  CI's
                                               `ubuntu-latest` is x86_64.

   WHY THESE ARE AXIOMS AND NOT PROOFS.  Each states that the raw bit-vector op
   (`Avx*.e_mm256_OP`, an uninterpreted `assume val` — see (1)) agrees with its
   int-vec / bit-level interpretation (`IV.e_mm256_OP`, a concrete definition).
   Nothing constrains the uninterpreted side, so this is exactly the point where
   the model meets the hardware: it is DISCHARGED BY DIFFERENTIAL TEST, not by
   proof.  Each entry below names its test.  This is the same trust class as the
   ~75 generated `Int_vec.Lemmas` lifts; these merely lack a `mk_lift_lemma!`.

   PREFERRED FIX for any entry here: declare `mk_lift_lemma!` in
   `interpretations.rs::lemmas` and delete the entry — then the axiom is
   generated from, and colocated with, the Rust model it is about.
   ============================================================================ *)

module BV   = Libcrux_core_models.Abstractions.Bitvec
module IV   = Libcrux_core_models.Core_arch.X86.Interpretations.Int_vec
module IVL  = Libcrux_core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas
module Avx  = Libcrux_core_models.Core_arch.X86.Avx
module Avx2 = Libcrux_core_models.Core_arch.X86.Avx2

(* ── bit-vector widths ─────────────────────────────────────────────────────── *)
let bv256 = BV.t_BitVec (mk_u64 256)
let bv128 = BV.t_BitVec (mk_u64 128)

(* ── bitwise ops.  Test: `mk!(_mm256_and_si256/_or_si256/_xor_si256(a: BitVec,
      b: BitVec))` in `interpretations.rs::tests`. ───────────────────────────── *)

[@@ IVL.v_LIFT_LEMMA]
assume
val lemma_and_si256_lift (a b: bv256)
    : Lemma (Avx2.e_mm256_and_si256 a b == IV.e_mm256_and_si256 a b)

[@@ IVL.v_LIFT_LEMMA]
assume
val lemma_xor_si256_lift (a b: bv256)
    : Lemma (Avx2.e_mm256_xor_si256 a b == IV.e_mm256_xor_si256 a b)

[@@ IVL.v_LIFT_LEMMA]
assume
val lemma_or_si256_lift (a b: bv256)
    : Lemma (Avx2.e_mm256_or_si256 a b == IV.e_mm256_or_si256 a b)

(* ── constructors / reinterpretations.  Test: `mk!(_mm256_setzero_si256())`,
      `mk!(_mm256_castsi128_si256(a: BitVec))`, `mk!(_mm256_set_m128i(..))`,
      `mk!(_mm256_castsi256_ps(..))`. ─────────────────────────────────────────── *)

[@@ IVL.v_LIFT_LEMMA]
assume
val lemma_setzero_si256_lift (u: Prims.unit)
    : Lemma (Avx.e_mm256_setzero_si256 () == IV.e_mm256_setzero_si256 ())

[@@ IVL.v_LIFT_LEMMA]
assume
val lemma_castsi128_si256_lift (a: bv128)
    : Lemma (Avx.e_mm256_castsi128_si256 a == IV.e_mm256_castsi128_si256 a)

[@@ IVL.v_LIFT_LEMMA]
assume
val lemma_set_m128i_lift (hi lo: bv128)
    : Lemma (Avx.e_mm256_set_m128i hi lo == IV.e_mm256_set_m128i hi lo)

(* `IV.e_mm256_castsi256_ps` / `castps_si256` are the IDENTITY on the bit vector
   (a float reinterpretation is a no-op on bits); the raw ops are uninterpreted,
   so the identity still has to be assumed here. *)
[@@ IVL.v_LIFT_LEMMA]
assume
val lemma_castsi256_ps_lift (a: bv256)
    : Lemma (Avx.e_mm256_castsi256_ps a == IV.e_mm256_castsi256_ps a)

[@@ IVL.v_LIFT_LEMMA]
assume
val lemma_castps_si256_lift (a: bv256)
    : Lemma (Avx.e_mm256_castps_si256 a == IV.e_mm256_castps_si256 a)

(* ── testz.  Test: the hand-rolled 1000-iteration `assert_eq!` against
      `upstream::_mm256_testz_si256` in `interpretations.rs::tests` (it predates
      `mk!` and is not written with that macro). ──────────────────────────────── *)

[@@ IVL.v_LIFT_LEMMA]
assume
val lemma_testz_si256_lift (a b: bv256)
    : Lemma (Avx.e_mm256_testz_si256 a b == IV.e_mm256_testz_si256 a b)
