module Libcrux.Kem.Kyber.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let to_spec_fe (m:t_FieldElement) =
               admit()

let to_spec_poly (m:t_PolynomialRingElement) =
               admit()
                                    
let to_spec_vector (#p:Spec.Kyber.params) (m:t_Array t_PolynomialRingElement p.v_RANK) =
               admit()

let to_spec_matrix (#p:Spec.Kyber.params) (m:(t_Array (t_Array t_PolynomialRingElement p.v_RANK) p.v_RANK)) = 
               admit()

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
  admit();
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
  admit();
  res

#push-options "--z3rlimit 100"
let montgomery_multiply_sfe_by_fer (fe fer: i32) : i32 =
  admit();
  montgomery_reduce (fe *! fer <: i32)
#pop-options

let to_standard_domain (mfe: i32) : i32 =
  admit(); 
  montgomery_reduce (mfe *! v_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS <: i32)

let to_unsigned_representative (fe: i32) =
  let _:Prims.unit = () <: Prims.unit in
  admit();
  cast (fe +! (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS &. (fe >>! 31l <: i32) <: i32) <: i32)
  <:
  u16

let add_to_ring_element (v_K: usize) (lhs rhs: t_PolynomialRingElement) = 
  let _:Prims.unit = () <: Prims.unit in
  let _:Prims.unit = () <: Prims.unit in
  let lhs:t_PolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end
              =
              Core.Slice.impl__len (Rust_primitives.unsize lhs.f_coefficients <: t_Slice i32)
              <:
              usize
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      lhs
      (fun lhs i ->
          let lhs:t_PolynomialRingElement = lhs in
          let i:usize = i in
          assume (range (v #i32_inttype lhs.f_coefficients.[ i ] + v #i32_inttype rhs.f_coefficients.[ i ]) i32_inttype);
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
          t_PolynomialRingElement)
  in
  let _:Prims.unit = () <: Prims.unit in
  lhs
