module Libcrux_ml_dsa.Constants
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let t_Eta_cast_to_repr (x: t_Eta) =
  match x <: t_Eta with
  | Eta_Two  -> discriminant_Eta_Two
  | Eta_Four  -> discriminant_Eta_Four

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': Core.Clone.t_Clone t_Eta

let impl = impl'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core.Marker.t_Copy t_Eta

let impl_1 = impl_1'

let beta (ones_in_verifier_challenge: usize) (eta: t_Eta) =
  let (eta_val: usize):usize =
    match eta <: t_Eta with
    | Eta_Two  -> sz 2
    | Eta_Four  -> sz 4
  in
  cast (ones_in_verifier_challenge *! eta_val <: usize) <: i32

let error_ring_element_size (bits_per_error_coefficient: usize) =
  (bits_per_error_coefficient *! v_COEFFICIENTS_IN_RING_ELEMENT <: usize) /! sz 8

let gamma1_ring_element_size (bits_per_gamma1_coefficient: usize) =
  (bits_per_gamma1_coefficient *! v_COEFFICIENTS_IN_RING_ELEMENT <: usize) /! sz 8

let commitment_ring_element_size (bits_per_commitment_coefficient: usize) =
  (bits_per_commitment_coefficient *! v_COEFFICIENTS_IN_RING_ELEMENT <: usize) /! sz 8

let commitment_vector_size (bits_per_commitment_coefficient rows_in_a: usize) =
  (commitment_ring_element_size bits_per_commitment_coefficient <: usize) *! rows_in_a

let signing_key_size (rows_in_a columns_in_a error_ring_element_size: usize) =
  (((v_SEED_FOR_A_SIZE +! v_SEED_FOR_SIGNING_SIZE <: usize) +! v_BYTES_FOR_VERIFICATION_KEY_HASH
      <:
      usize) +!
    ((rows_in_a +! columns_in_a <: usize) *! error_ring_element_size <: usize)
    <:
    usize) +!
  (rows_in_a *! v_RING_ELEMENT_OF_T0S_SIZE <: usize)

let verification_key_size (rows_in_a: usize) =
  v_SEED_FOR_A_SIZE +!
  (((v_COEFFICIENTS_IN_RING_ELEMENT *! rows_in_a <: usize) *!
      (v_FIELD_MODULUS_MINUS_ONE_BIT_LENGTH -! v_BITS_IN_LOWER_PART_OF_T <: usize)
      <:
      usize) /!
    sz 8
    <:
    usize)

let signature_size
      (rows_in_a columns_in_a max_ones_in_hint commitment_hash_size bits_per_gamma1_coefficient:
          usize)
     =
  ((commitment_hash_size +!
      (columns_in_a *! (gamma1_ring_element_size bits_per_gamma1_coefficient <: usize) <: usize)
      <:
      usize) +!
    max_ones_in_hint
    <:
    usize) +!
  rows_in_a
