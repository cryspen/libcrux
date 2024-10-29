module Libcrux_ml_kem.Vector.Portable.Compress
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let compress_ciphertext_coefficient (coefficient_bits: u8) (fe: u16) =
  let compressed:u64 = (cast (fe <: u16) <: u64) <<! coefficient_bits in
  let compressed:u64 = compressed +! 1664uL in
  let compressed:u64 = compressed *! 10321340uL in
  let compressed:u64 = compressed >>! 35l in
  cast (Libcrux_ml_kem.Vector.Portable.Arithmetic.get_n_least_significant_bits coefficient_bits
        (cast (compressed <: u64) <: u32)
      <:
      u32)
  <:
  i16

let compress_message_coefficient (fe: u16) =
  let (shifted: i16):i16 = 1664s -! (cast (fe <: u16) <: i16) in
  let mask:i16 = shifted >>! 15l in
  let shifted_to_positive:i16 = mask ^. shifted in
  let shifted_positive_in_range:i16 = shifted_to_positive -! 832s in
  cast ((shifted_positive_in_range >>! 15l <: i16) &. 1s <: i16) <: u8

let compress
      (v_COEFFICIENT_BITS: i32)
      (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
     =
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
      (fun v temp_1_ ->
          let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = v in
          let _:usize = temp_1_ in
          true)
      v
      (fun v i ->
          let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = v in
          let i:usize = i in
          {
            v with
            Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
                .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
              i
              (compress_ciphertext_coefficient (cast (v_COEFFICIENT_BITS <: i32) <: u8)
                  (cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16)
                    <:
                    u16)
                <:
                i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
  in
  v

let compress_1_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
      (fun v temp_1_ ->
          let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = v in
          let _:usize = temp_1_ in
          true)
      v
      (fun v i ->
          let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = v in
          let i:usize = i in
          {
            v with
            Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
                .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
              i
              (cast (compress_message_coefficient (cast (v
                              .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ]
                            <:
                            i16)
                        <:
                        u16)
                    <:
                    u8)
                <:
                i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
  in
  v

let decompress_ciphertext_coefficient
      (v_COEFFICIENT_BITS: i32)
      (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
     =
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
      (fun v temp_1_ ->
          let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = v in
          let _:usize = temp_1_ in
          true)
      v
      (fun v i ->
          let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = v in
          let i:usize = i in
          let decompressed:i32 =
            (cast (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16) <: i32) *!
            (cast (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS <: i16) <: i32)
          in
          let decompressed:i32 =
            (decompressed <<! 1l <: i32) +! (1l <<! v_COEFFICIENT_BITS <: i32)
          in
          let decompressed:i32 = decompressed >>! (v_COEFFICIENT_BITS +! 1l <: i32) in
          let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
            {
              v with
              Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
                  .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
                i
                (cast (decompressed <: i32) <: i16)
            }
            <:
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
          in
          v)
  in
  v
