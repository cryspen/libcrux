module Libcrux.Kem.Kyber.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 200"
open Core
open FStar.Mul

let v_BARRETT_MULTIPLIER: i64 = 20159L

let v_BARRETT_SHIFT: i64 = 26L
val v_BARRETT_R: x:i64{v x = pow2 26}
let v_BARRETT_R: i64 = 1L <<! v_BARRETT_SHIFT

let v_INVERSE_OF_MODULUS_MOD_R: u32 = 62209ul
let v_MONTGOMERY_SHIFT: u8 = 16uy
let v_MONTGOMERY_R: i32 = 1l <<! v_MONTGOMERY_SHIFT

let mont_to_spec_fe (m:t_FieldElement) = admit()

let get_n_least_significant_bits (n: u8) (value: u32) = 
  let _:Prims.unit = () <: Prims.unit in
  let res = value &. ((1ul <<! n <: u32) -! 1ul <: u32) in
  admit();
  res

let barrett_reduce (value: i32) = 
  let _:Prims.unit = () <: Prims.unit in
  let t:i64 =
    ((Core.Convert.f_from value <: i64) *! v_BARRETT_MULTIPLIER <: i64) +!
    (v_BARRETT_R >>! 1l <: i64)
  in
  let quotient:i32 = cast (t >>! v_BARRETT_SHIFT <: i64) <: i32 in
  admit(); // P-F
  let result:i32 = value -! (quotient *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) in
  let _:Prims.unit = () <: Prims.unit in
  result

let montgomery_reduce (value: i32) = 
  let _:i32 = v_MONTGOMERY_R in
  let _:Prims.unit = () <: Prims.unit in
  let t:u32 =
    (get_n_least_significant_bits v_MONTGOMERY_SHIFT (cast (value <: i32) <: u32) <: u32) *!
    v_INVERSE_OF_MODULUS_MOD_R
  in
  let k:i16 = cast (get_n_least_significant_bits v_MONTGOMERY_SHIFT t <: u32) <: i16 in
  let k_times_modulus:i32 =
    (cast (k <: i16) <: i32) *! Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
  in
  let c:i32 = k_times_modulus >>! v_MONTGOMERY_SHIFT in
  let value_high:i32 = value >>! v_MONTGOMERY_SHIFT in
  let res = value_high -! c in
  admit(); // P-F
  res

let montgomery_multiply_sfe_by_fer (fe fer: i32) =
  montgomery_reduce (fe *! fer <: i32)


let to_standard_domain (mfe: i32) =
  montgomery_reduce (mfe *! v_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS <: i32)

let to_unsigned_representative (fe: i32) =
  let _:Prims.unit = () <: Prims.unit in
  logand_lemma Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS (fe >>! 31l <: i32);
  let res =  
  cast (fe +! (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS &. (fe >>! 31l <: i32) <: i32) <: i32)
  <:
  u16
  in
  admit(); //P-F
  res

let add_to_ring_element (v_K: usize) (lhs rhs: t_PolynomialRingElement) = 
  let _:Prims.unit = () <: Prims.unit in
  let _:Prims.unit = () <: Prims.unit in
  let orig_lhs = lhs in
  [@ inline_let]
  let inv = fun (acc:t_PolynomialRingElement) (i:usize) ->
      (forall j. j <. i ==> acc.f_coefficients.[j] == lhs.f_coefficients.[j] +! rhs.f_coefficients.[j]) /\
      (forall j. j >=. i ==> acc.f_coefficients.[j] == orig_lhs.f_coefficients.[j]) in
  let lhs:t_PolynomialRingElement =
    Rust_primitives.Iterators.foldi_range #_ #(t_PolynomialRingElement)  #inv {
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end =
              Core.Slice.impl__len (Rust_primitives.unsize lhs.f_coefficients <: t_Slice i32)
            }
      lhs
      (fun lhs i ->
          let lhs:t_PolynomialRingElement = lhs in
          let i:usize = i in
          assert (orig_lhs.f_coefficients.[i] == lhs.f_coefficients.[i]);
          let lhs = 
          {
            lhs with
            f_coefficients
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs.f_coefficients
              i
              ((lhs.f_coefficients.[ i ] <: i32) +! (rhs.f_coefficients.[ i ] <: i32) <: i32)
            <:
            t_Array i32 (sz 256)
          }
          <:
          t_PolynomialRingElement
          in
          assert (forall j. (j >. i /\ j <. sz 256) ==> lhs.f_coefficients.[j] == orig_lhs.f_coefficients.[j]);
          lhs
          )
  in
  let _:Prims.unit = () <: Prims.unit in
  assert (forall j. j <. sz 256 ==> lhs.f_coefficients.[j] == orig_lhs.f_coefficients.[j] +! rhs.f_coefficients.[j]);
  lhs
  
