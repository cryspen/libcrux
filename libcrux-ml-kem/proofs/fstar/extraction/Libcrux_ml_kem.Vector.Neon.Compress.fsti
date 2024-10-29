module Libcrux_ml_kem.Vector.Neon.Compress
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val compress_int32x4_t (v_COEFFICIENT_BITS: i32) (v: u8)
    : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val mask_n_least_significant_bits (coefficient_bits: i16)
    : Prims.Pure i16 Prims.l_True (fun _ -> Prims.l_True)

val decompress_uint32x4_t (v_COEFFICIENT_BITS: i32) (v: u8)
    : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val compress (v_COEFFICIENT_BITS: i32) (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
    : Prims.Pure Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
      Prims.l_True
      (fun _ -> Prims.l_True)

val compress_1_ (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
    : Prims.Pure Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
      Prims.l_True
      (fun _ -> Prims.l_True)

val decompress_ciphertext_coefficient
      (v_COEFFICIENT_BITS: i32)
      (v: Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector)
    : Prims.Pure Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
      Prims.l_True
      (fun _ -> Prims.l_True)
