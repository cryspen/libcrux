module Libcrux.Kem.Kyber.Compress
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

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

let decompress_pre (coefficient_bits: u8) (fe: i32) = 
        (coefficient_bits =. 4uy || coefficient_bits =. 5uy || coefficient_bits =. 10uy ||
        coefficient_bits =. 11uy) &&
        v fe >= 0 &&
        v fe < pow2 (v coefficient_bits)

val decompress_ciphertext_coefficient (coefficient_bits: u8) (fe: i32)
    : Prims.Pure i32
      (requires (decompress_pre coefficient_bits fe))
      (ensures
        fun result ->
          let result:i32 = result in
          result <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS)

val decompress_message_coefficient (fe: i32)
    : Prims.Pure i32 (requires fe =. 0l || fe =. 1l) (fun _ -> Prims.l_True)
