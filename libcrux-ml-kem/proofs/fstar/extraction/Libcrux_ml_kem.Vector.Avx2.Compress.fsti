module Libcrux_ml_kem.Vector.Avx2.Compress
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val mulhi_mm256_epi32 (lhs rhs: u8) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val compress_ciphertext_coefficient (v_COEFFICIENT_BITS: i32) (vector: u8)
    : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val compress_message_coefficient (vector: u8) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val decompress_ciphertext_coefficient (v_COEFFICIENT_BITS: i32) (vector: u8)
    : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)
