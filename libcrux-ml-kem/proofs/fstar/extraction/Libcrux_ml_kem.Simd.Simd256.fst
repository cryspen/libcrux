module Libcrux_ml_kem.Simd.Simd256
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let impl__SIMD256Vector__add (self rhs: t_SIMD256Vector) =
  { f_elements = Libcrux_ml_kem.Simd.Simd256.X64_avx2.add self.f_elements rhs.f_elements }
  <:
  t_SIMD256Vector

let impl__SIMD256Vector__add_constant (self: t_SIMD256Vector) (c: i32) =
  {
    f_elements
    =
    Libcrux_ml_kem.Simd.Simd256.X64_avx2.add self.f_elements
      (Libcrux_ml_kem.Simd.Simd256.X64_avx2.load c <: Core.Core_arch.X86.t____m256i)
  }
  <:
  t_SIMD256Vector

let impl__SIMD256Vector__sub (self rhs: t_SIMD256Vector) =
  { f_elements = Libcrux_ml_kem.Simd.Simd256.X64_avx2.sub self.f_elements rhs.f_elements }
  <:
  t_SIMD256Vector

let bitwise_and_with_constant (v: t_SIMD256Vector) (c: i32) =
  {
    f_elements
    =
    Libcrux_ml_kem.Simd.Simd256.X64_avx2.v_and v.f_elements
      (Libcrux_ml_kem.Simd.Simd256.X64_avx2.load c <: Core.Core_arch.X86.t____m256i)
  }
  <:
  t_SIMD256Vector

let compress_1_ (v: t_SIMD256Vector) =
  let field_modulus_halved:Core.Core_arch.X86.t____m256i =
    Libcrux_ml_kem.Simd.Simd256.X64_avx2.load compress_1___FIELD_MODULUS_HAVLED
  in
  let field_modulus_quartered:Core.Core_arch.X86.t____m256i =
    Libcrux_ml_kem.Simd.Simd256.X64_avx2.load compress_1___FIELD_MODULUS_QUARTERED
  in
  let subtracted:Core.Core_arch.X86.t____m256i =
    Libcrux_ml_kem.Simd.Simd256.X64_avx2.sub field_modulus_halved v.f_elements
  in
  let mask:Core.Core_arch.X86.t____m256i =
    Libcrux_ml_kem.Simd.Simd256.X64_avx2.shr 31l subtracted
  in
  let value:Core.Core_arch.X86.t____m256i =
    Libcrux_ml_kem.Simd.Simd256.X64_avx2.shrli 31l
      (Libcrux_ml_kem.Simd.Simd256.X64_avx2.sub (Libcrux_ml_kem.Simd.Simd256.X64_avx2.xor mask
              subtracted
            <:
            Core.Core_arch.X86.t____m256i)
          field_modulus_quartered
        <:
        Core.Core_arch.X86.t____m256i)
  in
  { f_elements = value } <: t_SIMD256Vector

let cond_subtract_3329_ (v: t_SIMD256Vector) =
  let field_modulus:Core.Core_arch.X86.t____m256i =
    Libcrux_ml_kem.Simd.Simd256.X64_avx2.load Libcrux_ml_kem.Constants.v_FIELD_MODULUS
  in
  let subtracted:Core.Core_arch.X86.t____m256i =
    Libcrux_ml_kem.Simd.Simd256.X64_avx2.sub v.f_elements field_modulus
  in
  let mask:Core.Core_arch.X86.t____m256i =
    Libcrux_ml_kem.Simd.Simd256.X64_avx2.v_and (Libcrux_ml_kem.Simd.Simd256.X64_avx2.shr 31l
          subtracted
        <:
        Core.Core_arch.X86.t____m256i)
      field_modulus
  in
  { f_elements = Libcrux_ml_kem.Simd.Simd256.X64_avx2.add subtracted mask } <: t_SIMD256Vector

let deserialize_1_ (a: u8) =
  let a:i32 = cast (a <: u8) <: i32 in
  let deserialized:Core.Core_arch.X86.t____m256i =
    Libcrux_ml_kem.Simd.Simd256.X64_avx2.load_i32s ((a >>! 7l <: i32) &. 1l <: i32)
      ((a >>! 6l <: i32) &. 1l <: i32)
      ((a >>! 5l <: i32) &. 1l <: i32)
      ((a >>! 4l <: i32) &. 1l <: i32)
      ((a >>! 3l <: i32) &. 1l <: i32)
      ((a >>! 2l <: i32) &. 1l <: i32)
      ((a >>! 1l <: i32) &. 1l <: i32)
      (a &. 1l <: i32)
  in
  { f_elements = deserialized } <: t_SIMD256Vector

let deserialize_4_ (v: t_Slice u8) =
  let shifts:Core.Core_arch.X86.t____m256i =
    Libcrux_ml_kem.Simd.Simd256.X64_avx2.load_i32s 4l 0l 4l 0l 4l 0l 4l 0l
  in
  let last_4_bits_mask:Core.Core_arch.X86.t____m256i =
    Libcrux_ml_kem.Simd.Simd256.X64_avx2.load 15l
  in
  let deserialized:Core.Core_arch.X86.t____m256i =
    Libcrux_ml_kem.Simd.Simd256.X64_avx2.load_i32s (cast (v.[ sz 3 ] <: u8) <: i32)
      (cast (v.[ sz 3 ] <: u8) <: i32)
      (cast (v.[ sz 2 ] <: u8) <: i32)
      (cast (v.[ sz 2 ] <: u8) <: i32)
      (cast (v.[ sz 1 ] <: u8) <: i32)
      (cast (v.[ sz 1 ] <: u8) <: i32)
      (cast (v.[ sz 0 ] <: u8) <: i32)
      (cast (v.[ sz 0 ] <: u8) <: i32)
  in
  let deserialized:Core.Core_arch.X86.t____m256i =
    Libcrux_ml_kem.Simd.Simd256.X64_avx2.v_and (Libcrux_ml_kem.Simd.Simd256.X64_avx2.shrllv deserialized
          shifts
        <:
        Core.Core_arch.X86.t____m256i)
      last_4_bits_mask
  in
  { f_elements = deserialized } <: t_SIMD256Vector

let from_i32_array (array: t_Array i32 (sz 8)) =
  { f_elements = Libcrux_ml_kem.Simd.Simd256.X64_avx2.load_vec array } <: t_SIMD256Vector

let multiply_by_constant (v: t_SIMD256Vector) (c: i32) =
  {
    f_elements
    =
    Libcrux_ml_kem.Simd.Simd256.X64_avx2.mul v.f_elements
      (Libcrux_ml_kem.Simd.Simd256.X64_avx2.load c <: Core.Core_arch.X86.t____m256i)
  }
  <:
  t_SIMD256Vector

let serialize_1_ (v: t_SIMD256Vector) =
  let vv_bytes:t_Array i32 (sz 8) = Libcrux_ml_kem.Simd.Simd256.X64_avx2.store v.f_elements in
  cast ((((((((vv_bytes.[ sz 0 ] <: i32) |. ((vv_bytes.[ sz 1 ] <: i32) <<! 1l <: i32) <: i32) |.
                ((vv_bytes.[ sz 2 ] <: i32) <<! 2l <: i32)
                <:
                i32) |.
              ((vv_bytes.[ sz 3 ] <: i32) <<! 3l <: i32)
              <:
              i32) |.
            ((vv_bytes.[ sz 4 ] <: i32) <<! 4l <: i32)
            <:
            i32) |.
          ((vv_bytes.[ sz 5 ] <: i32) <<! 5l <: i32)
          <:
          i32) |.
        ((vv_bytes.[ sz 6 ] <: i32) <<! 6l <: i32)
        <:
        i32) |.
      ((vv_bytes.[ sz 7 ] <: i32) <<! 7l <: i32)
      <:
      i32)
  <:
  u8

let serialize_4_ (v: t_SIMD256Vector) =
  let shifts:Core.Core_arch.X86.t____m256i =
    Libcrux_ml_kem.Simd.Simd256.X64_avx2.load_i32s 0l 4l 0l 4l 0l 4l 0l 4l
  in
  let shuffle_to:Core.Core_arch.X86.t____m256i =
    Libcrux_ml_kem.Simd.Simd256.X64_avx2.load_i8s 31y 30y 29y 28y 27y 26y 25y 24y 23y 22y 21y 20y
      12y 8y 4y 0y 15y 14y 13y 12y 11y 10y 9y 8y 7y 6y 5y 4y 12y 8y 4y 0y
  in
  let value:Core.Core_arch.X86.t____m256i =
    Libcrux_ml_kem.Simd.Simd256.X64_avx2.shrli16 4l
      (Libcrux_ml_kem.Simd.Simd256.X64_avx2.shuffle (Libcrux_ml_kem.Simd.Simd256.X64_avx2.shllv v
                .f_elements
              shifts
            <:
            Core.Core_arch.X86.t____m256i)
          shuffle_to
        <:
        Core.Core_arch.X86.t____m256i)
  in
  let list =
    [
      cast (Libcrux_ml_kem.Simd.Simd256.X64_avx2.storei16 0l value <: i32) <: u8;
      cast (Libcrux_ml_kem.Simd.Simd256.X64_avx2.storei16 1l value <: i32) <: u8;
      cast (Libcrux_ml_kem.Simd.Simd256.X64_avx2.storei16 8l value <: i32) <: u8;
      cast (Libcrux_ml_kem.Simd.Simd256.X64_avx2.storei16 9l value <: i32) <: u8
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
  Rust_primitives.Hax.array_of_list 4 list

let shift_left (v_SHIFT_BY: i32) (v: t_SIMD256Vector) =
  { f_elements = Libcrux_ml_kem.Simd.Simd256.X64_avx2.shlli v_SHIFT_BY v.f_elements }
  <:
  t_SIMD256Vector

let shift_right (v_SHIFT_BY: i32) (v: t_SIMD256Vector) =
  { f_elements = Libcrux_ml_kem.Simd.Simd256.X64_avx2.shr v_SHIFT_BY v.f_elements }
  <:
  t_SIMD256Vector

let to_i32_array (v: t_SIMD256Vector) = Libcrux_ml_kem.Simd.Simd256.X64_avx2.store v.f_elements

let barrett_reduce (v: t_SIMD256Vector) =
  let input:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_from_i32_array (to_i32_array v <: t_Array i32 (sz 8))
  in
  let output:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_barrett_reduce input
  in
  from_i32_array (Libcrux_ml_kem.Simd.Simd_trait.f_to_i32_array output <: t_Array i32 (sz 8))

let compress (v_COEFFICIENT_BITS: i32) (v: t_SIMD256Vector) =
  let input:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_from_i32_array (to_i32_array v <: t_Array i32 (sz 8))
  in
  let output:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_compress v_COEFFICIENT_BITS input
  in
  from_i32_array (Libcrux_ml_kem.Simd.Simd_trait.f_to_i32_array output <: t_Array i32 (sz 8))

let deserialize_10_ (v: t_Slice u8) =
  let output:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_deserialize_10_ v
  in
  from_i32_array (Libcrux_ml_kem.Simd.Simd_trait.f_to_i32_array output <: t_Array i32 (sz 8))

let deserialize_11_ (v: t_Slice u8) =
  let output:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_deserialize_11_ v
  in
  from_i32_array (Libcrux_ml_kem.Simd.Simd_trait.f_to_i32_array output <: t_Array i32 (sz 8))

let deserialize_12_ (v: t_Slice u8) =
  let output:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_deserialize_12_ v
  in
  from_i32_array (Libcrux_ml_kem.Simd.Simd_trait.f_to_i32_array output <: t_Array i32 (sz 8))

let deserialize_5_ (v: t_Slice u8) =
  let output:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_deserialize_5_ v
  in
  from_i32_array (Libcrux_ml_kem.Simd.Simd_trait.f_to_i32_array output <: t_Array i32 (sz 8))

let inv_ntt_layer_1_step (v: t_SIMD256Vector) (zeta1 zeta2: i32) =
  let input:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_from_i32_array (to_i32_array v <: t_Array i32 (sz 8))
  in
  let output:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_inv_ntt_layer_1_step input zeta1 zeta2
  in
  from_i32_array (Libcrux_ml_kem.Simd.Simd_trait.f_to_i32_array output <: t_Array i32 (sz 8))

let inv_ntt_layer_2_step (v: t_SIMD256Vector) (zeta: i32) =
  let input:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_from_i32_array (to_i32_array v <: t_Array i32 (sz 8))
  in
  let output:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_inv_ntt_layer_2_step input zeta
  in
  from_i32_array (Libcrux_ml_kem.Simd.Simd_trait.f_to_i32_array output <: t_Array i32 (sz 8))

let montgomery_reduce (v: t_SIMD256Vector) =
  let input:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_from_i32_array (to_i32_array v <: t_Array i32 (sz 8))
  in
  let output:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_montgomery_reduce input
  in
  from_i32_array (Libcrux_ml_kem.Simd.Simd_trait.f_to_i32_array output <: t_Array i32 (sz 8))

let ntt_layer_1_step (v: t_SIMD256Vector) (zeta1 zeta2: i32) =
  let input:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_from_i32_array (to_i32_array v <: t_Array i32 (sz 8))
  in
  let output:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_ntt_layer_1_step input zeta1 zeta2
  in
  from_i32_array (Libcrux_ml_kem.Simd.Simd_trait.f_to_i32_array output <: t_Array i32 (sz 8))

let ntt_layer_2_step (v: t_SIMD256Vector) (zeta: i32) =
  let input:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_from_i32_array (to_i32_array v <: t_Array i32 (sz 8))
  in
  let output:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_ntt_layer_2_step input zeta
  in
  from_i32_array (Libcrux_ml_kem.Simd.Simd_trait.f_to_i32_array output <: t_Array i32 (sz 8))

let ntt_multiply (lhs rhs: t_SIMD256Vector) (zeta0 zeta1: i32) =
  let input1:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_from_i32_array (to_i32_array lhs <: t_Array i32 (sz 8))
  in
  let input2:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_from_i32_array (to_i32_array rhs <: t_Array i32 (sz 8))
  in
  let output:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_ntt_multiply input1 input2 zeta0 zeta1
  in
  from_i32_array (Libcrux_ml_kem.Simd.Simd_trait.f_to_i32_array output <: t_Array i32 (sz 8))

let serialize_10_ (v: t_SIMD256Vector) =
  let input:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_from_i32_array (to_i32_array v <: t_Array i32 (sz 8))
  in
  Libcrux_ml_kem.Simd.Simd_trait.f_serialize_10_ input

let serialize_11_ (v: t_SIMD256Vector) =
  let input:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_from_i32_array (to_i32_array v <: t_Array i32 (sz 8))
  in
  Libcrux_ml_kem.Simd.Simd_trait.f_serialize_11_ input

let serialize_12_ (v: t_SIMD256Vector) =
  let input:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_from_i32_array (to_i32_array v <: t_Array i32 (sz 8))
  in
  Libcrux_ml_kem.Simd.Simd_trait.f_serialize_12_ input

let serialize_5_ (v: t_SIMD256Vector) =
  let input:Libcrux_ml_kem.Simd.Portable.t_PortableVector =
    Libcrux_ml_kem.Simd.Simd_trait.f_from_i32_array (to_i32_array v <: t_Array i32 (sz 8))
  in
  Libcrux_ml_kem.Simd.Simd_trait.f_serialize_5_ input
