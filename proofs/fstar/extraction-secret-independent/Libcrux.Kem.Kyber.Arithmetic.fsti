module Libcrux.Kem.Kyber.Arithmetic
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

let v_BARRETT_SHIFT: pub_i64 = 26L

let v_BARRETT_R: i64 = 1L <<! v_BARRETT_SHIFT

let v_INVERSE_OF_MODULUS_MOD_R: u32 = 62209ul

let v_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS: i32 = 1353l

let v_MONTGOMERY_SHIFT: pub_u8 = 16uy

let v_MONTGOMERY_R: i32 = 1l <<! v_MONTGOMERY_SHIFT

val get_n_least_significant_bits (n: u8) (value: u32)
    : Prims.Pure u32
      (requires n =. 4uy || n =. 5uy || n =. 10uy || n =. 11uy || n =. v_MONTGOMERY_SHIFT)
      (ensures
        fun result ->
          let result:u32 = result in
          v result < v (Core.Num.impl__u32__pow 2ul (Core.Convert.f_into n <: u32) <: u32))

val barrett_reduce (value: i32)
    : Prims.Pure i32
      (requires
        v (Core.Convert.f_from value <: i64) > v (Core.Ops.Arith.Neg.neg v_BARRETT_R <: i64) &&
        v (Core.Convert.f_from value <: i64) < v v_BARRETT_R)
      (ensures
        fun result ->
          let result:i32 = result in
          v result > v (Core.Ops.Arith.Neg.neg Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) &&
          v result < v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS)

val montgomery_reduce (value: i32)
    : Prims.Pure i32
      (requires
       v value >=
       v ((Core.Ops.Arith.Neg.neg Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) *!
          v_MONTGOMERY_R
          <:
          i32) &&
        v value <= v (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS *! v_MONTGOMERY_R <: i32))
      (ensures
        fun result ->
          let result:i32 = result in
          v result >=
          v ((Core.Ops.Arith.Neg.neg (3l *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) <: i32
            ) /!
            2l
            <:
            i32) &&
          v result <= v ((3l *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) /! 2l <: i32))

val montgomery_multiply_sfe_by_fer (fe fer: i32)
    : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

val to_standard_domain (mfe: i32) : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

val to_unsigned_representative (fe: i32)
    : Prims.Pure u16
      (requires
        v fe >= v (Core.Ops.Arith.Neg.neg Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) &&
        v fe < v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS)
      (ensures
        fun result ->
          let result:u16 = result in
          v result >= v 0us &&
          v result < v (cast (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) <: u16))

type t_PolynomialRingElement = { f_coefficients:t_Array i32 (sz 256) }

let impl__PolynomialRingElement__ZERO: t_PolynomialRingElement =
  { f_coefficients = Rust_primitives.Hax.repeat 0l (sz 256) } <: t_PolynomialRingElement

val add_to_ring_element (v_K: usize) (lhs rhs: t_PolynomialRingElement)
    : Prims.Pure t_PolynomialRingElement
      (requires
        Hax_lib.v_forall (fun i ->
              let i:usize = i in
              Hax_lib.implies (i <. Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
                  <:
                  bool)
                (fun temp_0_ ->
                    let _:Prims.unit = temp_0_ in
                    let lhs_i = (lhs.f_coefficients.[ i ] <: i32) in
                    (v (Core.Num.impl__i32__abs lhs_i <: i32) <=
                      v (((cast (v_K <: usize) <: pub_i32) -! 1l <: i32) *!
                        Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
                        <:
                        i32)
                      <:
                      bool) &&
                    (v (Core.Num.impl__i32__abs (rhs.f_coefficients.[ i ] <: i32) <: i32) <=
                      v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
                      <:
                      bool))
              <:
              bool))
      (ensures
        fun result ->
          let result:t_PolynomialRingElement = result in
          Hax_lib.v_forall (fun i ->
                let i:usize = i in
                Hax_lib.implies (i <.
                    (Core.Slice.impl__len (Rust_primitives.unsize result.f_coefficients
                          <:
                          t_Slice i32)
                      <:
                      usize)
                    <:
                    bool)
                  (fun temp_0_ ->
                      let _:Prims.unit = temp_0_ in
                      v (Core.Num.impl__i32__abs (result.f_coefficients.[ i ] <: i32) <: i32) <=
                      v ((cast (v_K <: usize) <: pub_i32) *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
                        <:
                        i32)
                      <:
                      bool)
                <:
                bool))
