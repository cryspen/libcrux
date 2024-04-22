module Libcrux_ml_kem.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

unfold
let t_FieldElement = i32

unfold
let t_FieldElementTimesMontgomeryR = i32

unfold
let t_MontgomeryFieldElement = i32

let v_BARRETT_MULTIPLIER: i64 = 20159L

let v_BARRETT_SHIFT: i64 = 26L

let v_BARRETT_R: i64 = 1L <<! v_BARRETT_SHIFT

let v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u32 = 62209ul

let v_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS: i32 = 1353l

let v_MONTGOMERY_SHIFT: u8 = 16uy

let v_MONTGOMERY_R: i32 = 1l <<! v_MONTGOMERY_SHIFT

val get_n_least_significant_bits (n: u8) (value: u32)
    : Prims.Pure u32
      (requires n =. 4uy || n =. 5uy || n =. 10uy || n =. 11uy || n =. v_MONTGOMERY_SHIFT)
      (ensures
        fun result ->
          let result:u32 = result in
          result <. (Core.Num.impl__u32__pow 2ul (Core.Convert.f_into n <: u32) <: u32))

val v__to_unsigned_representative (fe: i32)
    : Prims.Pure u16
      (requires
        fe >=. (Core.Ops.Arith.Neg.neg Libcrux_ml_kem.Constants.v_FIELD_MODULUS <: i32) &&
        fe <. Libcrux_ml_kem.Constants.v_FIELD_MODULUS)
      (ensures
        fun result ->
          let result:u16 = result in
          result >=. 0us &&
          result <. (cast (Libcrux_ml_kem.Constants.v_FIELD_MODULUS <: i32) <: u16))

val barrett_reduce (value: i32)
    : Prims.Pure i32
      (requires
        (Core.Convert.f_from value <: i64) >. (Core.Ops.Arith.Neg.neg v_BARRETT_R <: i64) &&
        (Core.Convert.f_from value <: i64) <. v_BARRETT_R)
      (ensures
        fun result ->
          let result:i32 = result in
          result >. (Core.Ops.Arith.Neg.neg Libcrux_ml_kem.Constants.v_FIELD_MODULUS <: i32) &&
          result <. Libcrux_ml_kem.Constants.v_FIELD_MODULUS)

val montgomery_reduce (value: i32)
    : Prims.Pure i32
      (requires
        value >=.
        ((Core.Ops.Arith.Neg.neg Libcrux_ml_kem.Constants.v_FIELD_MODULUS <: i32) *! v_MONTGOMERY_R
          <:
          i32) &&
        value <=. (Libcrux_ml_kem.Constants.v_FIELD_MODULUS *! v_MONTGOMERY_R <: i32))
      (ensures
        fun result ->
          let result:i32 = result in
          result >=.
          ((Core.Ops.Arith.Neg.neg (3l *! Libcrux_ml_kem.Constants.v_FIELD_MODULUS <: i32) <: i32) /!
            2l
            <:
            i32) &&
          result <=. ((3l *! Libcrux_ml_kem.Constants.v_FIELD_MODULUS <: i32) /! 2l <: i32))

val v__to_standard_domain (mfe: i32) : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

val montgomery_multiply_fe_by_fer (fe fer: i32)
    : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

val ntt_multiply_binomials: (i32 & i32) -> (i32 & i32) -> zeta: i32
  -> Prims.Pure (i32 & i32) Prims.l_True (fun _ -> Prims.l_True)
