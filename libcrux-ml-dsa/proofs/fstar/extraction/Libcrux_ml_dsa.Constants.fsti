module Libcrux_ml_dsa.Constants
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let v_FIELD_MODULUS: i32 = 8380417l

let v_COEFFICIENTS_IN_RING_ELEMENT: usize = sz 256

let v_FIELD_MODULUS_MINUS_ONE_BIT_LENGTH: usize = sz 23

let v_BITS_IN_LOWER_PART_OF_T: usize = sz 13

let v_RING_ELEMENT_OF_T0S_SIZE: usize =
  (v_BITS_IN_LOWER_PART_OF_T *! v_COEFFICIENTS_IN_RING_ELEMENT <: usize) /! sz 8

let v_BITS_IN_UPPER_PART_OF_T: usize =
  v_FIELD_MODULUS_MINUS_ONE_BIT_LENGTH -! v_BITS_IN_LOWER_PART_OF_T

let v_RING_ELEMENT_OF_T1S_SIZE: usize =
  (v_BITS_IN_UPPER_PART_OF_T *! v_COEFFICIENTS_IN_RING_ELEMENT <: usize) /! sz 8

let v_SEED_FOR_A_SIZE: usize = sz 32

let v_SEED_FOR_ERROR_VECTORS_SIZE: usize = sz 64

let v_BYTES_FOR_VERIFICATION_KEY_HASH: usize = sz 64

let v_SEED_FOR_SIGNING_SIZE: usize = sz 32

/// Number of bytes of entropy required for key generation.
let v_KEY_GENERATION_RANDOMNESS_SIZE: usize = sz 32

/// Number of bytes of entropy required for signing.
let v_SIGNING_RANDOMNESS_SIZE: usize = sz 32

let v_MESSAGE_REPRESENTATIVE_SIZE: usize = sz 64

let v_MASK_SEED_SIZE: usize = sz 64

let v_REJECTION_SAMPLE_BOUND_SIGN: usize = sz 814

/// The length of `context` is serialized to a single `u8`.
let v_CONTEXT_MAX_LEN: usize = sz 255

/// Eta values
type t_Eta =
  | Eta_Two : t_Eta
  | Eta_Four : t_Eta

let discriminant_Eta_Two: isize = isz 2

let discriminant_Eta_Four: isize = isz 4

val t_Eta_cast_to_repr (x: t_Eta) : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:Core.Clone.t_Clone t_Eta

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1:Core.Marker.t_Copy t_Eta

let v_GAMMA2_V261_888_: i32 = 261888l

let v_GAMMA2_V95_232_: i32 = 95232l

val beta (ones_in_verifier_challenge: usize) (eta: t_Eta)
    : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

val error_ring_element_size (bits_per_error_coefficient: usize)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val gamma1_ring_element_size (bits_per_gamma1_coefficient: usize)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val commitment_ring_element_size (bits_per_commitment_coefficient: usize)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val commitment_vector_size (bits_per_commitment_coefficient rows_in_a: usize)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val signing_key_size (rows_in_a columns_in_a error_ring_element_size: usize)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val verification_key_size (rows_in_a: usize) : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val signature_size
      (rows_in_a columns_in_a max_ones_in_hint commitment_hash_size bits_per_gamma1_coefficient:
          usize)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)
