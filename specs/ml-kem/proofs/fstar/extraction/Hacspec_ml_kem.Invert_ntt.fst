module Hacspec_ml_kem.Invert_ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let v_INVERSE_OF_128_: Hacspec_ml_kem.Parameters.t_FieldElement =
  Hacspec_ml_kem.Parameters.impl_FieldElement__new (mk_u16 3303)

#push-options "--z3rlimit 150"

/// Use the Gentleman-Sande butterfly to invert, in-place, the NTT representation
/// of a `Polynomial`.
/// This function implements <strong>Algorithm 9</strong> of the NIST FIPS 203 standard, which
/// is reproduced below:
/// ```plaintext
/// Input: array fˆ ∈ ℤ₂₅₆.
/// Output: array f ∈ ℤ₂₅₆.
/// f ← fˆ
/// k ← 127
/// for (len ← 2; len ≤ 128; len ← 2·len)
///     for (start ← 0; start < 256; start ← start + 2·len)
///         zeta ← ζ^(BitRev₇(k)) mod q
///         k ← k − 1
///         for (j ← start; j < start + len; j++)
///             t ← f[j]
///             f[j] ← t + f[j + len]
///             f[j + len] ← zeta·(f[j+len] − t)
///         end for
///     end for
/// end for
/// f ← f·3303 mod q
/// return f
/// ```
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
let ntt_inverse_layer
      (p: t_Array Hacspec_ml_kem.Parameters.t_FieldElement (mk_usize 256))
      (layer: usize)
    : Prims.Pure (t_Array Hacspec_ml_kem.Parameters.t_FieldElement (mk_usize 256))
      (requires layer >=. mk_usize 1 && layer <=. mk_usize 7)
      (fun _ -> Prims.l_True) =
  let _:Prims.unit = () <: Prims.unit in
  let len:usize = mk_usize 1 <<! layer in
  let _:Prims.unit = assert (v len == pow2 (v layer)) in
  let k:usize = (mk_usize 256 /! len <: usize) -! mk_usize 1 in
  let _:Prims.unit = assert (v k == 256 / (v len) - 1) in
  Hacspec_ml_kem.Parameters.createi #Hacspec_ml_kem.Parameters.t_FieldElement
    (mk_usize 256)
    #(usize -> Hacspec_ml_kem.Parameters.t_FieldElement)
    (fun i ->
        let i:usize = i in
        let round:usize = i /! (mk_usize 2 *! len <: usize) in
        let _:Prims.unit = assert (v round < 128 / (v len)) in
        let _:Prims.unit = assert (v len >= 2) in
        let idx:usize = i %! (mk_usize 2 *! len <: usize) in
        let q:u32 = cast (Hacspec_ml_kem.Parameters.v_FIELD_MODULUS <: u16) <: u32 in
        if idx <. len
        then
          Hacspec_ml_kem.Parameters.impl_FieldElement__new (cast (((cast ((p.[ i ]
                            <:
                            Hacspec_ml_kem.Parameters.t_FieldElement)
                            .Hacspec_ml_kem.Parameters.f_val
                          <:
                          u16)
                      <:
                      u32) +!
                    (cast ((p.[ i +! len <: usize ] <: Hacspec_ml_kem.Parameters.t_FieldElement)
                            .Hacspec_ml_kem.Parameters.f_val
                          <:
                          u16)
                      <:
                      u32)
                    <:
                    u32) %!
                  q
                  <:
                  u32)
              <:
              u16)
        else
          let diff:u32 =
            (((cast ((p.[ i ] <: Hacspec_ml_kem.Parameters.t_FieldElement)
                        .Hacspec_ml_kem.Parameters.f_val
                      <:
                      u16)
                  <:
                  u32) +!
                q
                <:
                u32) -!
              (cast ((p.[ i -! len <: usize ] <: Hacspec_ml_kem.Parameters.t_FieldElement)
                      .Hacspec_ml_kem.Parameters.f_val
                    <:
                    u16)
                <:
                u32)
              <:
              u32) %!
            q
          in
          Hacspec_ml_kem.Parameters.impl_FieldElement__new (cast (((cast ((Hacspec_ml_kem.Ntt.get_zeta
                              (k -! round <: usize)
                            <:
                            Hacspec_ml_kem.Parameters.t_FieldElement)
                            .Hacspec_ml_kem.Parameters.f_val
                          <:
                          u16)
                      <:
                      u32) *!
                    diff
                    <:
                    u32) %!
                  q
                  <:
                  u32)
              <:
              u16))

#pop-options

let reduce_polynomial (p: t_Array Hacspec_ml_kem.Parameters.t_FieldElement (mk_usize 256))
    : t_Array Hacspec_ml_kem.Parameters.t_FieldElement (mk_usize 256) =
  Hacspec_ml_kem.Parameters.createi #Hacspec_ml_kem.Parameters.t_FieldElement
    (mk_usize 256)
    #(usize -> Hacspec_ml_kem.Parameters.t_FieldElement)
    (fun i ->
        let i:usize = i in
        Hacspec_ml_kem.Parameters.impl_FieldElement__new (cast (((cast ((p.[ i ]
                          <:
                          Hacspec_ml_kem.Parameters.t_FieldElement)
                          .Hacspec_ml_kem.Parameters.f_val
                        <:
                        u16)
                    <:
                    u32) *!
                  (cast (v_INVERSE_OF_128_.Hacspec_ml_kem.Parameters.f_val <: u16) <: u32)
                  <:
                  u32) %!
                (cast (Hacspec_ml_kem.Parameters.v_FIELD_MODULUS <: u16) <: u32)
                <:
                u32)
            <:
            u16)
        <:
        Hacspec_ml_kem.Parameters.t_FieldElement)

#push-options "--z3rlimit 150"

let ntt_inverse (p: t_Array Hacspec_ml_kem.Parameters.t_FieldElement (mk_usize 256))
    : t_Array Hacspec_ml_kem.Parameters.t_FieldElement (mk_usize 256) =
  let p:t_Array Hacspec_ml_kem.Parameters.t_FieldElement (mk_usize 256) =
    ntt_inverse_layer p (mk_usize 1)
  in
  let p:t_Array Hacspec_ml_kem.Parameters.t_FieldElement (mk_usize 256) =
    ntt_inverse_layer p (mk_usize 2)
  in
  let p:t_Array Hacspec_ml_kem.Parameters.t_FieldElement (mk_usize 256) =
    ntt_inverse_layer p (mk_usize 3)
  in
  let p:t_Array Hacspec_ml_kem.Parameters.t_FieldElement (mk_usize 256) =
    ntt_inverse_layer p (mk_usize 4)
  in
  let p:t_Array Hacspec_ml_kem.Parameters.t_FieldElement (mk_usize 256) =
    ntt_inverse_layer p (mk_usize 5)
  in
  let p:t_Array Hacspec_ml_kem.Parameters.t_FieldElement (mk_usize 256) =
    ntt_inverse_layer p (mk_usize 6)
  in
  let p:t_Array Hacspec_ml_kem.Parameters.t_FieldElement (mk_usize 256) =
    ntt_inverse_layer p (mk_usize 7)
  in
  reduce_polynomial p

#pop-options

/// Inverse NTT applied to each polynomial in a vector.
let vector_inverse_ntt
      (v_RANK: usize)
      (vector_as_ntt:
          t_Array (t_Array Hacspec_ml_kem.Parameters.t_FieldElement (mk_usize 256)) v_RANK)
    : t_Array (t_Array Hacspec_ml_kem.Parameters.t_FieldElement (mk_usize 256)) v_RANK =
  Hacspec_ml_kem.Parameters.createi #(t_Array Hacspec_ml_kem.Parameters.t_FieldElement
        (mk_usize 256))
    v_RANK
    #(usize -> t_Array Hacspec_ml_kem.Parameters.t_FieldElement (mk_usize 256))
    (fun i ->
        let i:usize = i in
        ntt_inverse (vector_as_ntt.[ i ]
            <:
            t_Array Hacspec_ml_kem.Parameters.t_FieldElement (mk_usize 256))
        <:
        t_Array Hacspec_ml_kem.Parameters.t_FieldElement (mk_usize 256))

/// Performs Barrett reduction on all coefficients of a polynomial.
/// This is the spec equivalent of `poly_barrett_reduce` in the implementation.
let poly_barrett_reduce (p: t_Array Hacspec_ml_kem.Parameters.t_FieldElement (mk_usize 256))
    : t_Array Hacspec_ml_kem.Parameters.t_FieldElement (mk_usize 256) =
  Hacspec_ml_kem.Parameters.createi #Hacspec_ml_kem.Parameters.t_FieldElement
    (mk_usize 256)
    #(usize -> Hacspec_ml_kem.Parameters.t_FieldElement)
    (fun i ->
        let i:usize = i in
        Hacspec_ml_kem.Parameters.impl_FieldElement__new ((p.[ i ]
              <:
              Hacspec_ml_kem.Parameters.t_FieldElement)
              .Hacspec_ml_kem.Parameters.f_val %!
            Hacspec_ml_kem.Parameters.v_FIELD_MODULUS
            <:
            u16)
        <:
        Hacspec_ml_kem.Parameters.t_FieldElement)
