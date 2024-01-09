module Libcrux.Kem.Kyber.Compress
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val compress_message_coefficient (fe: u16)
    : Prims.Pure u8
      (requires v fe < 3329)
      (ensures
        fun result ->
          let result:u8 = result in
          if 833 <= v fe && v fe <=  2496
          then result =. 1uy
          else result =. 0uy)


val compress_ciphertext_coefficient (coefficient_bits: u8 {v coefficient_bits > 0 /\ v coefficient_bits <= 32}) (fe: u16)
    : Prims.Pure (int_t_d i32_inttype (v coefficient_bits))
      (requires
        (coefficient_bits =. 4uy || coefficient_bits =. 5uy || coefficient_bits =. 10uy ||
        coefficient_bits =. 11uy) &&
        fe <. (cast (Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS <: i32) <: u16))
      (ensures
        fun result ->
          let result:i32 = result in
          result >=. 0l &&
          result <. (Core.Num.impl__i32__pow 2l (cast (coefficient_bits <: u8) <: u32) <: i32))

open Rust_primitives.Integers

val decompress_ciphertext_coefficient
    (coefficient_bits: u8 {coefficient_bits =. 4uy || coefficient_bits =. 5uy || coefficient_bits =. 10uy || coefficient_bits =. 11uy})
    (fe: int_t_d i32_inttype (v coefficient_bits))
    : Prims.Pure (Libcrux.Kem.Kyber.Arithmetic.i32_b (v Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS - 1))
      (requires True)
      (ensures
        fun result ->
          let result:i32 = result in
          result <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS)

val decompress_message_coefficient (fe: i32)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.wfFieldElement
      (requires fe =. 0l || fe =. 1l) 
      (fun result -> v result >= 0 /\ v result < 3329)
