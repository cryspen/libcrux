module Libcrux.Kem.Kyber.Compress
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val compress_ciphertext_coefficient (coefficient_bits: u8) (fe: u16)
    : Prims.Pure i32
      (requires
        (coefficient_bits =. 4uy || coefficient_bits =. 5uy || coefficient_bits =. 10uy ||
        coefficient_bits =. 11uy) &&
        fe <. (cast (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) <: u16))
      (ensures
        fun result ->
          let result:i32 = result in
          result >=. 0l &&
          result <. (Core.Num.impl__i32__pow 2l (cast (coefficient_bits <: u8) <: u32) <: i32))

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
      (requires fe <. (cast (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) <: u16))
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

val decompress_ciphertext_coefficient (coefficient_bits: u8) (fe: i32)
    : Prims.Pure i32
      (requires
        (coefficient_bits =. 4uy || coefficient_bits =. 5uy || coefficient_bits =. 10uy ||
        coefficient_bits =. 11uy) &&
        fe >=. 0l &&
        fe <. (Core.Num.impl__i32__pow 2l (cast (coefficient_bits <: u8) <: u32) <: i32))
      (ensures
        fun result ->
          let result:i32 = result in
          result <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS)

/// The `decompress_*` functions implement the `Decompress` function specified in the NIST FIPS
/// 203 standard (Page 18, Expression 4.6), which is defined as:
/// ```plaintext
/// Decompress_d: ℤ_{2ᵈ} -> ℤq
/// Decompress_d(y) = ⌈(q/2ᵈ)·y⌋
/// ```
/// Since `⌈x⌋ = ⌊x + 1/2⌋` we have:
/// ```plaintext
/// Decompress_d(y) = ⌊(q/2ᵈ)·y + 1/2⌋
///                 = ⌊(2·y·q + 2ᵈ) / 2^{d+1})⌋
/// ```
/// For further information about the function implementations, consult the
/// `implementation_notes.pdf` document in this directory.
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
val decompress_message_coefficient (fe: i32)
    : Prims.Pure i32 (requires fe =. 0l || fe =. 1l) (fun _ -> Prims.l_True)
