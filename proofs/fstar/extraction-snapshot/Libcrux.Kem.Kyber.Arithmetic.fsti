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

let v_BARRETT_SHIFT: i64 = 26L

let v_BARRETT_R: i64 = 1L <<! v_BARRETT_SHIFT

let v_INVERSE_OF_MODULUS_MOD_R: u32 = 62209ul

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

let barrett_pre (value:i32) = 
    v value > v (Core.Ops.Arith.Neg.neg v_BARRETT_R) &&
    v value < v v_BARRETT_R

val barrett_reduce (value: i32)
    : Prims.Pure i32
      (requires (barrett_pre value))
      (ensures
        fun result ->
          let result:i32 = result in
          result >. (Core.Ops.Arith.Neg.neg Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) &&
          result <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS)


let montgomery_pre (value:i32) =
        v value >=
        (v (Core.Ops.Arith.Neg.neg Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS) *
          v v_MONTGOMERY_R) /\
        v value <= (v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS * v v_MONTGOMERY_R)

val montgomery_reduce (value: i32)
    : Prims.Pure i32
      (requires (montgomery_pre value))
      (ensures
        fun result ->
          let result:i32 = result in
          result >=.
          ((Core.Ops.Arith.Neg.neg (3l *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) <: i32
            ) /!
            2l
            <:
            i32) &&
          result <=. ((3l *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) /! 2l <: i32))


val montgomery_multiply_sfe_by_fer (fe fer: i32) : i32

val to_standard_domain (mfe: i32) : i32

val to_unsigned_representative (fe: i32)
    : Prims.Pure u16
      (requires
        fe >=. (Core.Ops.Arith.Neg.neg Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) &&
        fe <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS)
      (ensures
        fun result ->
          let result:u16 = result in
          result >=. 0us &&
          result <. (cast (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) <: u16))

type t_PolynomialRingElement = { f_coefficients:t_Array i32 (sz 256) }

let impl__PolynomialRingElement__ZERO: t_PolynomialRingElement =
  { f_coefficients = Rust_primitives.Hax.repeat 0l (sz 256) } <: t_PolynomialRingElement

val add_to_ring_element (v_K: usize) (lhs rhs: t_PolynomialRingElement)
    : Prims.Pure t_PolynomialRingElement
      (requires
        v_K >. sz 1 /\
        v_K <=. sz 4)
      (ensures fun _ -> True)
(*
        Hax_lib.v_forall (fun i ->
              let i:usize = i in
              Hax_lib.implies (i <. Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
                  <:
                  bool)
                (fun _ -> ((Core.Num.impl__i32__abs (lhs.f_coefficients.[ i ] <: i32) <: i32) <=.
                    (((cast (v_K <: usize) <: i32) -! 1l <: i32) *!
                      Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
                      <:
                      i32)
                    <:
                    bool) &&
                  ((Core.Num.impl__i32__abs (rhs.f_coefficients.[ i ] <: i32) <: i32) <=.
                    Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
                    <:
                    bool))
              <:
              bool))
              *)
(*      
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
                  (fun _ -> (Core.Num.impl__i32__abs (result.f_coefficients.[ i ] <: i32) <: i32) <=.
                    ((cast (v_K <: usize) <: i32) *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
                      <:
                      i32)
                    <:
                    bool)
                <:
                bool))
*)
