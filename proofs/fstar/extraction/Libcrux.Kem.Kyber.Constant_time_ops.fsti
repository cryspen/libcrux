module Libcrux.Kem.Kyber.Constant_time_ops
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// Return 1 if `value` is not zero and 0 otherwise.
val is_non_zero (value: u8)
    : Prims.Pure u8
      Prims.l_True
      (ensures
        fun result ->
          let result:u8 = result in
          Hax_lib.implies (value =. 0uy <: bool)
            (fun temp_0_ ->
                let _:Prims.unit = temp_0_ in
                result =. 0uy <: bool) &&
          Hax_lib.implies (value <>. 0uy <: bool)
            (fun temp_0_ ->
                let _:Prims.unit = temp_0_ in
                result =. 1uy <: bool))

/// Return 1 if the bytes of `lhs` and `rhs` do not exactly
/// match and 0 otherwise.
val compare_ciphertexts_in_constant_time (v_CIPHERTEXT_SIZE: usize) (lhs rhs: t_Slice u8)
    : Prims.Pure u8
      Prims.l_True
      (ensures
        fun result ->
          let result:u8 = result in
          Hax_lib.implies (lhs =. rhs <: bool)
            (fun temp_0_ ->
                let _:Prims.unit = temp_0_ in
                result =. 0uy <: bool) &&
          Hax_lib.implies (lhs <>. rhs <: bool)
            (fun temp_0_ ->
                let _:Prims.unit = temp_0_ in
                result =. 1uy <: bool))

/// If `selector` is not zero, return the bytes in `rhs`; return the bytes in
/// `lhs` otherwise.
val select_shared_secret_in_constant_time (lhs rhs: t_Slice u8) (selector: u8)
    : Prims.Pure (t_Array u8 (sz 32))
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Array u8 (sz 32) = result in
          Hax_lib.implies (selector =. 0uy <: bool)
            (fun temp_0_ ->
                let _:Prims.unit = temp_0_ in
                result =. lhs <: bool) &&
          Hax_lib.implies (selector <>. 0uy <: bool)
            (fun temp_0_ ->
                let _:Prims.unit = temp_0_ in
                result =. rhs <: bool))
