module Hacspec_ml_dsa.Hash_functions
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// Hash function wrappers — FIPS 204, Section 3.7.
/// H(str, ℓ) = SHAKE256(str, 8ℓ)
/// G(str, ℓ) = SHAKE128(str, 8ℓ)
/// H: SHAKE256 of a single input, producing N bytes.
/// Kept opaque: cross-crate call to hacspec_sha3 does not extract.
assume
val h': v_N: usize -> input: t_Slice u8 -> t_Array u8 v_N

unfold
let h (v_N: usize) = h' v_N

/// G: SHAKE128 of a single input, producing N bytes.
/// Kept opaque: cross-crate call to hacspec_sha3 does not extract.
assume
val g': v_N: usize -> input: t_Slice u8 -> t_Array u8 v_N

unfold
let g (v_N: usize) = g' v_N

/// H applied to the concatenation of two byte strings.
/// Kept opaque: variable-length m_prime prevents fixed-size buffer.
assume
val h2': v_N: usize -> a: t_Slice u8 -> b: t_Slice u8 -> t_Array u8 v_N

unfold
let h2 (v_N: usize) = h2' v_N

/// H applied to the concatenation of [u8; 32] ++ [u8; 32] ++ [u8; 64] = 128 bytes.
let h3 (v_N: usize) (a b: t_Array u8 (mk_usize 32)) (c: t_Array u8 (mk_usize 64)) : t_Array u8 v_N =
  let input:t_Array u8 (mk_usize 128) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 128) in
  let input:t_Array u8 (mk_usize 128) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_to input
      ({ Core_models.Ops.Range.f_end = mk_usize 32 } <: Core_models.Ops.Range.t_RangeTo usize)
      (Core_models.Slice.impl__copy_from_slice #u8
          (input.[ { Core_models.Ops.Range.f_end = mk_usize 32 }
              <:
              Core_models.Ops.Range.t_RangeTo usize ]
            <:
            t_Slice u8)
          (a <: t_Slice u8)
        <:
        t_Slice u8)
  in
  let input:t_Array u8 (mk_usize 128) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range input
      ({ Core_models.Ops.Range.f_start = mk_usize 32; Core_models.Ops.Range.f_end = mk_usize 64 }
        <:
        Core_models.Ops.Range.t_Range usize)
      (Core_models.Slice.impl__copy_from_slice #u8
          (input.[ {
                Core_models.Ops.Range.f_start = mk_usize 32;
                Core_models.Ops.Range.f_end = mk_usize 64
              }
              <:
              Core_models.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (b <: t_Slice u8)
        <:
        t_Slice u8)
  in
  let input:t_Array u8 (mk_usize 128) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range input
      ({ Core_models.Ops.Range.f_start = mk_usize 64; Core_models.Ops.Range.f_end = mk_usize 128 }
        <:
        Core_models.Ops.Range.t_Range usize)
      (Core_models.Slice.impl__copy_from_slice #u8
          (input.[ {
                Core_models.Ops.Range.f_start = mk_usize 64;
                Core_models.Ops.Range.f_end = mk_usize 128
              }
              <:
              Core_models.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (c <: t_Slice u8)
        <:
        t_Slice u8)
  in
  h v_N (input <: t_Slice u8)
