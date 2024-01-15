module Libcrux.Kem.Kyber.Constant_time_ops
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

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

val compare_ciphertexts_in_constant_time (v_CIPHERTEXT_SIZE: usize) (lhs rhs: t_Slice u8)
    : Prims.Pure u8
      Prims.l_True
      (ensures
        fun result ->
          let result:u8 = result in
          Hax_lib.implies (lhs = rhs)
            (fun temp_0_ ->
                let _:Prims.unit = temp_0_ in
                v result = v 0uy <: bool) &&
          Hax_lib.implies (lhs <> rhs)
            (fun temp_0_ ->
                let _:Prims.unit = temp_0_ in
                v result = v 1uy <: bool))

val select_shared_secret_in_constant_time (lhs rhs: t_Slice u8) (selector: u8)
    : Prims.Pure (t_Array u8 (sz 32))
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Array u8 (sz 32) = result in
          Hax_lib.implies (selector =. 0uy <: bool)
            (fun temp_0_ ->
                let _:Prims.unit = temp_0_ in
                result = lhs <: bool) &&
          Hax_lib.implies (selector <>. 0uy <: bool)
            (fun temp_0_ ->
                let _:Prims.unit = temp_0_ in
                result = rhs <: bool))
