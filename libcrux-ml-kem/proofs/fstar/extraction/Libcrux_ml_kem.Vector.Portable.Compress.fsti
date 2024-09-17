module Libcrux_ml_kem.Vector.Portable.Compress
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val compress_ciphertext_coefficient (coefficient_bits: u8) (fe: u16)
    : Prims.Pure i16
      (requires
        (coefficient_bits =. 4uy || coefficient_bits =. 5uy || coefficient_bits =. 10uy ||
        coefficient_bits =. 11uy) &&
        fe <. (cast (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS <: i16) <: u16))
      (ensures
        fun result ->
          let result:i16 = result in
          result >=. 0s &&
          result <. (Core.Num.impl__i16__pow 2s (cast (coefficient_bits <: u8) <: u32) <: i16))

/// The `compress_*` functions implement the `Compress` function specified in the NIST FIPS
/// 203 standard (Page 18, Expression 4.5), which is defined as:
/// ```plaintext
/// Compress_d: ℤq -> ℤ_{2ᵈ}
/// Compress_d(x) = ⌈(2ᵈ/q)·x⌋
/// ```
/// Since `⌈x⌋ = ⌊x + 1/2⌋` we have:
/// ```plaintext
/// Compress_d(x) = ⌊(2ᵈ/q)·x + 1/2⌋
///               = ⌊(2^{d+1}·x + q) / 2q⌋
/// ```
/// For further information about the function implementations, consult the
/// `implementation_notes.pdf` document in this directory.
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
val compress_message_coefficient (fe: u16)
    : Prims.Pure u8
      (requires fe <. (cast (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS <: i16) <: u16))
      (ensures
        fun result ->
          let result:u8 = result in
          Hax_lib.implies ((833us <=. fe <: bool) && (fe <=. 2596us <: bool))
            (fun temp_0_ ->
                let _:Prims.unit = temp_0_ in
                result =. 1uy <: bool) &&
          Hax_lib.implies (~.((833us <=. fe <: bool) && (fe <=. 2596us <: bool)) <: bool)
            (fun temp_0_ ->
                let _:Prims.unit = temp_0_ in
                result =. 0uy <: bool))

val compress
      (v_COEFFICIENT_BITS: i32)
      (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires
        (v v_COEFFICIENT_BITS == 4 \/ v v_COEFFICIENT_BITS == 5 \/ v v_COEFFICIENT_BITS == 10 \/
          v v_COEFFICIENT_BITS == 11) /\
        (forall (i: nat).
            i < 16 ==>
            v (Seq.index a.f_elements i) >= 0 /\
            v (Seq.index a.f_elements i) < v Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS))
      (ensures
        fun result ->
          let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = result in
          forall (i: nat).
            i < 16 ==>
            v (result.f_elements.[ sz i ] <: i16) >= 0 /\
            v (result.f_elements.[ sz i ] <: i16) < pow2 (v v_COEFFICIENT_BITS))

val compress_1_ (a: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires
        forall (i: nat).
          i < 16 ==>
          v (Seq.index a.f_elements i) >= 0 /\
          v (Seq.index a.f_elements i) < v Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS)
      (ensures
        fun result ->
          let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = result in
          forall (i: nat).
            i < 16 ==>
            v (result.f_elements.[ sz i ] <: i16) >= 0 /\ v (result.f_elements.[ sz i ] <: i16) < 2)

val decompress_ciphertext_coefficient
      (v_COEFFICIENT_BITS: i32)
      (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      Prims.l_True
      (fun _ -> Prims.l_True)
