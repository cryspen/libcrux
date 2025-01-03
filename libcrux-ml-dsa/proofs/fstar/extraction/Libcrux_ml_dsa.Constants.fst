module Libcrux_ml_dsa.Constants
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let t_Eta_cast_to_repr (x: t_Eta) =
  match x <: t_Eta with
  | Eta_Two  -> discriminant_Eta_Two
  | Eta_Four  -> discriminant_Eta_Four

let t_Gamma2_cast_to_repr (x: t_Gamma2) =
  match x <: t_Gamma2 with
  | Gamma2_V95_232_  -> discriminant_Gamma2_V95_232_
  | Gamma2_V261_888_  -> discriminant_Gamma2_V261_888_

let error_ring_element_size (bits_per_error_coefficient: usize) =
  (bits_per_error_coefficient *! v_COEFFICIENTS_IN_RING_ELEMENT <: usize) /! sz 8

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

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': Core.Fmt.t_Debug t_Eta

let impl = impl'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core.Clone.t_Clone t_Eta

let impl_1 = impl_1'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': Core.Marker.t_Copy t_Eta

let impl_2 = impl_2'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': Core.Fmt.t_Debug t_Gamma2

let impl_3 = impl_3'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': Core.Clone.t_Clone t_Gamma2

let impl_4 = impl_4'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': Core.Marker.t_Copy t_Gamma2

let impl_5 = impl_5'
