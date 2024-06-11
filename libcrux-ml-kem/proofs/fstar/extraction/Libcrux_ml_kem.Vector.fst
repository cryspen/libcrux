module Libcrux_ml_kem.Vector
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Portable in
  ()

let barrett_reduce_element (value: i16) =
  let t:i32 =
    ((Core.Convert.f_from #i32 #i16 value <: i32) *! v_BARRETT_MULTIPLIER <: i32) +!
    (v_BARRETT_R >>! 1l <: i32)
  in
  let quotient:i16 = cast (t >>! v_BARRETT_SHIFT <: i32) <: i16 in
  value -! (quotient *! Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS <: i16)

let compress_message_coefficient (fe: u16) =
  let (shifted: i16):i16 = 1664s -! (cast (fe <: u16) <: i16) in
  let mask:i16 = shifted >>! 15l in
  let shifted_to_positive:i16 = mask ^. shifted in
  let shifted_positive_in_range:i16 = shifted_to_positive -! 832s in
  cast ((shifted_positive_in_range >>! 15l <: i16) &. 1s <: i16) <: u8

let get_n_least_significant_bits (n: u8) (value: u32) = value &. ((1ul <<! n <: u32) -! 1ul <: u32)

let compress_ciphertext_coefficient (coefficient_bits: u8) (fe: u16) =
  let compressed:u64 = (cast (fe <: u16) <: u64) <<! coefficient_bits in
  let compressed:u64 = compressed +! 1664uL in
  let compressed:u64 = compressed *! 10321340uL in
  let compressed:u64 = compressed >>! 35l in
  cast (get_n_least_significant_bits coefficient_bits (cast (compressed <: u64) <: u32) <: u32)
  <:
  i16

let montgomery_reduce_element (value: i32) =
  let _:i32 = v_MONTGOMERY_R in
  let k:i32 =
    (cast (cast (value <: i32) <: i16) <: i32) *!
    (cast (Libcrux_ml_kem.Vector.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R <: u32) <: i32)
  in
  let k_times_modulus:i32 =
    (cast (cast (k <: i32) <: i16) <: i32) *!
    (cast (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS <: i16) <: i32)
  in
  let c:i16 = cast (k_times_modulus >>! v_MONTGOMERY_SHIFT <: i32) <: i16 in
  let value_high:i16 = cast (value >>! v_MONTGOMERY_SHIFT <: i32) <: i16 in
  value_high -! c

let montgomery_multiply_fe_by_fer (fe fer: i16) =
  montgomery_reduce_element ((cast (fe <: i16) <: i32) *! (cast (fer <: i16) <: i32) <: i32)

let ntt_multiply_binomials (a0, a1: (i16 & i16)) (b0, b1: (i16 & i16)) (zeta: i16) =
  montgomery_reduce_element (((cast (a0 <: i16) <: i32) *! (cast (b0 <: i16) <: i32) <: i32) +!
      ((cast (montgomery_reduce_element ((cast (a1 <: i16) <: i32) *! (cast (b1 <: i16) <: i32)
                  <:
                  i32)
              <:
              i16)
          <:
          i32) *!
        (cast (zeta <: i16) <: i32)
        <:
        i32)
      <:
      i32),
  montgomery_reduce_element (((cast (a0 <: i16) <: i32) *! (cast (b1 <: i16) <: i32) <: i32) +!
      ((cast (a1 <: i16) <: i32) *! (cast (b0 <: i16) <: i32) <: i32)
      <:
      i32)
  <:
  (i16 & i16)

let rej_sample (a: t_Slice u8) (result: t_Slice i16) =
  let sampled:usize = sz 0 in
  let result, sampled:(t_Slice i16 & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Slice.Iter.t_Chunks
            u8)
          (Core.Slice.impl__chunks #u8 a (sz 3) <: Core.Slice.Iter.t_Chunks u8)
        <:
        Core.Slice.Iter.t_Chunks u8)
      (result, sampled <: (t_Slice i16 & usize))
      (fun temp_0_ bytes ->
          let result, sampled:(t_Slice i16 & usize) = temp_0_ in
          let bytes:t_Slice u8 = bytes in
          let b1:i16 = cast (bytes.[ sz 0 ] <: u8) <: i16 in
          let b2:i16 = cast (bytes.[ sz 1 ] <: u8) <: i16 in
          let b3:i16 = cast (bytes.[ sz 2 ] <: u8) <: i16 in
          let d1:i16 = ((b2 &. 15s <: i16) <<! 8l <: i16) |. b1 in
          let d2:i16 = (b3 <<! 4l <: i16) |. (b2 >>! 4l <: i16) in
          let result, sampled:(t_Slice i16 & usize) =
            if d1 <. Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS && sampled <. sz 16
            then
              let result:t_Slice i16 =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result sampled d1
              in
              result, sampled +! sz 1 <: (t_Slice i16 & usize)
            else result, sampled <: (t_Slice i16 & usize)
          in
          if d2 <. Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS && sampled <. sz 16
          then
            let result:t_Slice i16 =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result sampled d2
            in
            result, sampled +! sz 1 <: (t_Slice i16 & usize)
          else result, sampled <: (t_Slice i16 & usize))
  in
  let hax_temp_output:usize = sampled in
  result, hax_temp_output <: (t_Slice i16 & usize)

let add (lhs rhs: Libcrux_ml_kem.Vector.Portable.t_PortableVector) =
  let lhs:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      lhs
      (fun lhs i ->
          let lhs:Libcrux_ml_kem.Vector.Portable.t_PortableVector = lhs in
          let i:usize = i in
          {
            lhs with
            Libcrux_ml_kem.Vector.Portable.f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs
                .Libcrux_ml_kem.Vector.Portable.f_elements
              i
              ((lhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ i ] <: i16) +!
                (rhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ i ] <: i16)
                <:
                i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          Libcrux_ml_kem.Vector.Portable.t_PortableVector)
  in
  lhs

let barrett_reduce (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) =
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      v
      (fun v i ->
          let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector = v in
          let i:usize = i in
          {
            v with
            Libcrux_ml_kem.Vector.Portable.f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
                .Libcrux_ml_kem.Vector.Portable.f_elements
              i
              (barrett_reduce_element (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ i ] <: i16)
                <:
                i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          Libcrux_ml_kem.Vector.Portable.t_PortableVector)
  in
  v

let bitwise_and_with_constant (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (c: i16) =
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      v
      (fun v i ->
          let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector = v in
          let i:usize = i in
          {
            v with
            Libcrux_ml_kem.Vector.Portable.f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
                .Libcrux_ml_kem.Vector.Portable.f_elements
              i
              ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ i ] <: i16) &. c <: i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          Libcrux_ml_kem.Vector.Portable.t_PortableVector)
  in
  v

let compress (v_COEFFICIENT_BITS: i32) (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) =
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      v
      (fun v i ->
          let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector = v in
          let i:usize = i in
          {
            v with
            Libcrux_ml_kem.Vector.Portable.f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
                .Libcrux_ml_kem.Vector.Portable.f_elements
              i
              (compress_ciphertext_coefficient (cast (v_COEFFICIENT_BITS <: i32) <: u8)
                  (cast (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ i ] <: i16) <: u16)
                <:
                i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          Libcrux_ml_kem.Vector.Portable.t_PortableVector)
  in
  v

let compress_1_ (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) =
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      v
      (fun v i ->
          let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector = v in
          let i:usize = i in
          {
            v with
            Libcrux_ml_kem.Vector.Portable.f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
                .Libcrux_ml_kem.Vector.Portable.f_elements
              i
              (cast (compress_message_coefficient (cast (v.Libcrux_ml_kem.Vector.Portable.f_elements.[
                              i ]
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
          Libcrux_ml_kem.Vector.Portable.t_PortableVector)
  in
  v

let cond_subtract_3329_ (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) =
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      v
      (fun v i ->
          let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector = v in
          let i:usize = i in
          let _:Prims.unit =
            if true
            then
              let _:Prims.unit =
                if
                  ~.(((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ i ] <: i16) >=. 0s <: bool) &&
                    ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ i ] <: i16) <. 4096s <: bool))
                then
                  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: v.elements[i] >= 0 && v.elements[i] < 4096"

                      <:
                      Rust_primitives.Hax.t_Never)
              in
              ()
          in
          if (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ i ] <: i16) >=. 3329s
          then
            {
              v with
              Libcrux_ml_kem.Vector.Portable.f_elements
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
                  .Libcrux_ml_kem.Vector.Portable.f_elements
                i
                ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ i ] <: i16) -! 3329s <: i16)
            }
            <:
            Libcrux_ml_kem.Vector.Portable.t_PortableVector
          else v)
  in
  v

let decompress_ciphertext_coefficient
      (v_COEFFICIENT_BITS: i32)
      (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
     =
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      v
      (fun v i ->
          let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector = v in
          let i:usize = i in
          let decompressed:i32 =
            (cast (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ i ] <: i16) <: i32) *!
            (cast (Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS <: i16) <: i32)
          in
          let decompressed:i32 =
            (decompressed <<! 1l <: i32) +! (1l <<! v_COEFFICIENT_BITS <: i32)
          in
          let decompressed:i32 = decompressed >>! (v_COEFFICIENT_BITS +! 1l <: i32) in
          let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
            {
              v with
              Libcrux_ml_kem.Vector.Portable.f_elements
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
                  .Libcrux_ml_kem.Vector.Portable.f_elements
                i
                (cast (decompressed <: i32) <: i16)
            }
            <:
            Libcrux_ml_kem.Vector.Portable.t_PortableVector
          in
          v)
  in
  v

let from_i16_array (array: t_Slice i16) =
  {
    Libcrux_ml_kem.Vector.Portable.f_elements
    =
    Core.Result.impl__unwrap #(t_Array i16 (sz 16))
      #Core.Array.t_TryFromSliceError
      (Core.Convert.f_try_into #(t_Slice i16)
          #(t_Array i16 (sz 16))
          (array.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 16 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice i16)
        <:
        Core.Result.t_Result (t_Array i16 (sz 16)) Core.Array.t_TryFromSliceError)
  }
  <:
  Libcrux_ml_kem.Vector.Portable.t_PortableVector

let inv_ntt_layer_1_step
      (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
      (zeta0 zeta1 zeta2 zeta3: i16)
     =
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 2 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 0 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 0)
        (barrett_reduce_element ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 0 ] <: i16) +!
              (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 2 ] <: i16)
              <:
              i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 2)
        (montgomery_multiply_fe_by_fer a_minus_b zeta0 <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 3 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 1 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 1)
        (barrett_reduce_element ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 1 ] <: i16) +!
              (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 3 ] <: i16)
              <:
              i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 3)
        (montgomery_multiply_fe_by_fer a_minus_b zeta0 <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 6 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 4 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 4)
        (barrett_reduce_element ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 4 ] <: i16) +!
              (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 6 ] <: i16)
              <:
              i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 6)
        (montgomery_multiply_fe_by_fer a_minus_b zeta1 <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 7 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 5 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 5)
        (barrett_reduce_element ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 5 ] <: i16) +!
              (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 7 ] <: i16)
              <:
              i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 7)
        (montgomery_multiply_fe_by_fer a_minus_b zeta1 <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 0 <: usize)
        (barrett_reduce_element ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 0
                  <:
                  usize ]
                <:
                i16) +!
              (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16)
              <:
              i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 2 <: usize)
        (montgomery_multiply_fe_by_fer a_minus_b zeta2 <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 1 <: usize)
        (barrett_reduce_element ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 1
                  <:
                  usize ]
                <:
                i16) +!
              (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16)
              <:
              i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 3 <: usize)
        (montgomery_multiply_fe_by_fer a_minus_b zeta2 <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 4 <: usize)
        (barrett_reduce_element ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 4
                  <:
                  usize ]
                <:
                i16) +!
              (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16)
              <:
              i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 6 <: usize)
        (montgomery_multiply_fe_by_fer a_minus_b zeta3 <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 5 <: usize)
        (barrett_reduce_element ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 5
                  <:
                  usize ]
                <:
                i16) +!
              (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16)
              <:
              i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 7 <: usize)
        (montgomery_multiply_fe_by_fer a_minus_b zeta3 <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  v

let inv_ntt_layer_2_step (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (zeta0 zeta1: i16) =
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 4 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 0 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 0)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 0 ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 4 ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 4)
        (montgomery_multiply_fe_by_fer a_minus_b zeta0 <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 5 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 1 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 1)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 1 ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 5 ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 5)
        (montgomery_multiply_fe_by_fer a_minus_b zeta0 <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 6 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 2 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 2)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 2 ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 6 ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 6)
        (montgomery_multiply_fe_by_fer a_minus_b zeta0 <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 7 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 3 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 3)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 3 ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 7 ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 7)
        (montgomery_multiply_fe_by_fer a_minus_b zeta0 <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 0 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 4 <: usize)
        (montgomery_multiply_fe_by_fer a_minus_b zeta1 <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 1 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 5 <: usize)
        (montgomery_multiply_fe_by_fer a_minus_b zeta1 <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 2 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 6 <: usize)
        (montgomery_multiply_fe_by_fer a_minus_b zeta1 <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 3 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 7 <: usize)
        (montgomery_multiply_fe_by_fer a_minus_b zeta1 <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  v

let inv_ntt_layer_3_step (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (zeta: i16) =
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 0 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 0)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 0 ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8)
        (montgomery_multiply_fe_by_fer a_minus_b zeta <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 9 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 1 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 1)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 1 ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 9 ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 9)
        (montgomery_multiply_fe_by_fer a_minus_b zeta <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 10 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 2 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 2)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 2 ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 10 ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 10)
        (montgomery_multiply_fe_by_fer a_minus_b zeta <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 11 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 3 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 3)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 3 ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 11 ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 11)
        (montgomery_multiply_fe_by_fer a_minus_b zeta <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 12 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 4 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 4)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 4 ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 12 ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 12)
        (montgomery_multiply_fe_by_fer a_minus_b zeta <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 13 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 5 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 5)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 5 ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 13 ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 13)
        (montgomery_multiply_fe_by_fer a_minus_b zeta <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 14 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 6 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 6)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 6 ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 14 ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 14)
        (montgomery_multiply_fe_by_fer a_minus_b zeta <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 15 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 7 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 7)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 7 ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 15 ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 15)
        (montgomery_multiply_fe_by_fer a_minus_b zeta <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  v

let montgomery_multiply_by_constant (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (c: i16) =
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      v
      (fun v i ->
          let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector = v in
          let i:usize = i in
          {
            v with
            Libcrux_ml_kem.Vector.Portable.f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
                .Libcrux_ml_kem.Vector.Portable.f_elements
              i
              (montgomery_multiply_fe_by_fer (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ i ]
                    <:
                    i16)
                  c
                <:
                i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          Libcrux_ml_kem.Vector.Portable.t_PortableVector)
  in
  v

let multiply_by_constant (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (c: i16) =
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      v
      (fun v i ->
          let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector = v in
          let i:usize = i in
          {
            v with
            Libcrux_ml_kem.Vector.Portable.f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
                .Libcrux_ml_kem.Vector.Portable.f_elements
              i
              ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ i ] <: i16) *! c <: i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          Libcrux_ml_kem.Vector.Portable.t_PortableVector)
  in
  v

let ntt_layer_1_step
      (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
      (zeta0 zeta1 zeta2 zeta3: i16)
     =
  let t:i16 =
    montgomery_multiply_fe_by_fer (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 2 ] <: i16)
      zeta0
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 2)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 0 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 0)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 0 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let t:i16 =
    montgomery_multiply_fe_by_fer (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 3 ] <: i16)
      zeta0
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 3)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 1 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 1)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 1 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let t:i16 =
    montgomery_multiply_fe_by_fer (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 6 ] <: i16)
      zeta1
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 6)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 4 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 4)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 4 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let t:i16 =
    montgomery_multiply_fe_by_fer (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 7 ] <: i16)
      zeta1
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 7)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 5 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 5)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 5 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let t:i16 =
    montgomery_multiply_fe_by_fer (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 2
          <:
          usize ]
        <:
        i16)
      zeta2
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 2 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 0 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let t:i16 =
    montgomery_multiply_fe_by_fer (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 3
          <:
          usize ]
        <:
        i16)
      zeta2
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 3 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 1 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let t:i16 =
    montgomery_multiply_fe_by_fer (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 6
          <:
          usize ]
        <:
        i16)
      zeta3
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 6 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 4 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let t:i16 =
    montgomery_multiply_fe_by_fer (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 7
          <:
          usize ]
        <:
        i16)
      zeta3
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 7 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 5 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  v

let ntt_layer_2_step (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (zeta0 zeta1: i16) =
  let t:i16 =
    montgomery_multiply_fe_by_fer (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 4 ] <: i16)
      zeta0
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 4)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 0 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 0)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 0 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let t:i16 =
    montgomery_multiply_fe_by_fer (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 5 ] <: i16)
      zeta0
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 5)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 1 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 1)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 1 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let t:i16 =
    montgomery_multiply_fe_by_fer (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 6 ] <: i16)
      zeta0
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 6)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 2 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 2)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 2 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let t:i16 =
    montgomery_multiply_fe_by_fer (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 7 ] <: i16)
      zeta0
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 7)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 3 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 3)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 3 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let t:i16 =
    montgomery_multiply_fe_by_fer (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 4
          <:
          usize ]
        <:
        i16)
      zeta1
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 4 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 0 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let t:i16 =
    montgomery_multiply_fe_by_fer (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 5
          <:
          usize ]
        <:
        i16)
      zeta1
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 5 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 1 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let t:i16 =
    montgomery_multiply_fe_by_fer (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 6
          <:
          usize ]
        <:
        i16)
      zeta1
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 6 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 2 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let t:i16 =
    montgomery_multiply_fe_by_fer (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 7
          <:
          usize ]
        <:
        i16)
      zeta1
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 7 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 3 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  v

let ntt_layer_3_step (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) (zeta: i16) =
  let t:i16 =
    montgomery_multiply_fe_by_fer (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 ] <: i16) zeta
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 0 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 0)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 0 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let t:i16 =
    montgomery_multiply_fe_by_fer (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 9 ] <: i16) zeta
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 9)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 1 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 1)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 1 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let t:i16 =
    montgomery_multiply_fe_by_fer (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 10 ] <: i16)
      zeta
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 10)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 2 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 2)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 2 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let t:i16 =
    montgomery_multiply_fe_by_fer (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 11 ] <: i16)
      zeta
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 11)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 3 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 3)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 3 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let t:i16 =
    montgomery_multiply_fe_by_fer (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 12 ] <: i16)
      zeta
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 12)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 4 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 4)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 4 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let t:i16 =
    montgomery_multiply_fe_by_fer (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 13 ] <: i16)
      zeta
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 13)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 5 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 5)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 5 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let t:i16 =
    montgomery_multiply_fe_by_fer (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 14 ] <: i16)
      zeta
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 14)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 6 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 6)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 6 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let t:i16 =
    montgomery_multiply_fe_by_fer (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 15 ] <: i16)
      zeta
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 15)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 7 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 7)
        ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 7 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  v

let serialize_1_ (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) =
  let result:t_Array u8 (sz 2) = Rust_primitives.Hax.repeat 0uy (sz 2) in
  let result:t_Array u8 (sz 2) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 8 }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      result
      (fun result i ->
          let result:t_Array u8 (sz 2) = result in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
            (sz 0)
            ((result.[ sz 0 ] <: u8) |.
              ((cast (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ i ] <: i16) <: u8) <<! i <: u8)
              <:
              u8)
          <:
          t_Array u8 (sz 2))
  in
  let result:t_Array u8 (sz 2) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({ Core.Ops.Range.f_start = sz 8; Core.Ops.Range.f_end = sz 16 }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      result
      (fun result i ->
          let result:t_Array u8 (sz 2) = result in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
            (sz 1)
            ((result.[ sz 1 ] <: u8) |.
              ((cast (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ i ] <: i16) <: u8) <<!
                (i -! sz 8 <: usize)
                <:
                u8)
              <:
              u8)
          <:
          t_Array u8 (sz 2))
  in
  result

let serialize_10_ (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) =
  let result:t_Array u8 (sz 20) = Rust_primitives.Hax.repeat 0uy (sz 20) in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 0)
      (cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 0 ] <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 1)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 1 ] <: i16) &. 63s <: i16) <: u8) <<!
          2l
          <:
          u8) |.
        (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 0 ] <: i16) >>! 8l <: i16) &. 3s
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 2)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 2 ] <: i16) &. 15s <: i16) <: u8) <<!
          4l
          <:
          u8) |.
        (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 1 ] <: i16) >>! 6l <: i16) &. 15s
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 3)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 3 ] <: i16) &. 3s <: i16) <: u8) <<!
          6l
          <:
          u8) |.
        (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 2 ] <: i16) >>! 4l <: i16) &. 63s
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 4)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 3 ] <: i16) >>! 2l <: i16) &. 255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 5)
      (cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 4 ] <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 6)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 5 ] <: i16) &. 63s <: i16) <: u8) <<!
          2l
          <:
          u8) |.
        (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 4 ] <: i16) >>! 8l <: i16) &. 3s
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 7)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 6 ] <: i16) &. 15s <: i16) <: u8) <<!
          4l
          <:
          u8) |.
        (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 5 ] <: i16) >>! 6l <: i16) &. 15s
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 8)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 7 ] <: i16) &. 3s <: i16) <: u8) <<!
          6l
          <:
          u8) |.
        (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 6 ] <: i16) >>! 4l <: i16) &. 63s
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 9)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 7 ] <: i16) >>! 2l <: i16) &. 255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 10)
      (cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) &. 255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 11)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) &. 63s
                <:
                i16)
            <:
            u8) <<!
          2l
          <:
          u8) |.
        (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) >>!
                8l
                <:
                i16) &.
              3s
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 12)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) &. 15s
                <:
                i16)
            <:
            u8) <<!
          4l
          <:
          u8) |.
        (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) >>!
                6l
                <:
                i16) &.
              15s
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 13)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) &. 3s
                <:
                i16)
            <:
            u8) <<!
          6l
          <:
          u8) |.
        (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) >>!
                4l
                <:
                i16) &.
              63s
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 14)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) >>! 2l
              <:
              i16) &.
            255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 15)
      (cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) &. 255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 16)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) &. 63s
                <:
                i16)
            <:
            u8) <<!
          2l
          <:
          u8) |.
        (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) >>!
                8l
                <:
                i16) &.
              3s
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 17)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16) &. 15s
                <:
                i16)
            <:
            u8) <<!
          4l
          <:
          u8) |.
        (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) >>!
                6l
                <:
                i16) &.
              15s
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 18)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16) &. 3s
                <:
                i16)
            <:
            u8) <<!
          6l
          <:
          u8) |.
        (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16) >>!
                4l
                <:
                i16) &.
              63s
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 20) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 19)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16) >>! 2l
              <:
              i16) &.
            255s
            <:
            i16)
        <:
        u8)
  in
  result

let serialize_11_ (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) =
  let result:t_Array u8 (sz 22) = Rust_primitives.Hax.repeat 0uy (sz 22) in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 0)
      (cast (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 0 ] <: i16) <: u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 1)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 1 ] <: i16) &. 31s <: i16) <: u8) <<!
          3l
          <:
          u8) |.
        (cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 0 ] <: i16) >>! 8l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 2)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 2 ] <: i16) &. 3s <: i16) <: u8) <<!
          6l
          <:
          u8) |.
        (cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 1 ] <: i16) >>! 5l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 3)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 2 ] <: i16) >>! 2l <: i16) &. 255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 4)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 3 ] <: i16) &. 127s <: i16) <: u8) <<!
          1l
          <:
          u8) |.
        (cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 2 ] <: i16) >>! 10l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 5)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 4 ] <: i16) &. 15s <: i16) <: u8) <<!
          4l
          <:
          u8) |.
        (cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 3 ] <: i16) >>! 7l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 6)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 5 ] <: i16) &. 1s <: i16) <: u8) <<!
          7l
          <:
          u8) |.
        (cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 4 ] <: i16) >>! 4l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 7)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 5 ] <: i16) >>! 1l <: i16) &. 255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 8)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 6 ] <: i16) &. 63s <: i16) <: u8) <<!
          2l
          <:
          u8) |.
        (cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 5 ] <: i16) >>! 9l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 9)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 7 ] <: i16) &. 7s <: i16) <: u8) <<!
          5l
          <:
          u8) |.
        (cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 6 ] <: i16) >>! 6l <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 10)
      (cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 7 ] <: i16) >>! 3l <: i16) <: u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 11)
      (cast (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) <: u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 12)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) &. 31s
                <:
                i16)
            <:
            u8) <<!
          3l
          <:
          u8) |.
        (cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) >>! 8l
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 13)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) &. 3s
                <:
                i16)
            <:
            u8) <<!
          6l
          <:
          u8) |.
        (cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) >>! 5l
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 14)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) >>! 2l
              <:
              i16) &.
            255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 15)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) &.
                127s
                <:
                i16)
            <:
            u8) <<!
          1l
          <:
          u8) |.
        (cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) >>!
              10l
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 16)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) &. 15s
                <:
                i16)
            <:
            u8) <<!
          4l
          <:
          u8) |.
        (cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) >>! 7l
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 17)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) &. 1s
                <:
                i16)
            <:
            u8) <<!
          7l
          <:
          u8) |.
        (cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) >>! 4l
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 18)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) >>! 1l
              <:
              i16) &.
            255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 19)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16) &. 63s
                <:
                i16)
            <:
            u8) <<!
          2l
          <:
          u8) |.
        (cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) >>! 9l
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 20)
      (((cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16) &. 7s
                <:
                i16)
            <:
            u8) <<!
          5l
          <:
          u8) |.
        (cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16) >>! 6l
              <:
              i16)
          <:
          u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 22) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 21)
      (cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16) >>! 3l
            <:
            i16)
        <:
        u8)
  in
  result

let serialize_12_ (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) =
  let result:t_Array u8 (sz 24) = Rust_primitives.Hax.repeat 0uy (sz 24) in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 0)
      (cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 0 ] <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 1)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 0 ] <: i16) >>! 8l <: i16) |.
            (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 1 ] <: i16) &. 15s <: i16) <<! 4l
              <:
              i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 2)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 1 ] <: i16) >>! 4l <: i16) &. 255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 3)
      (cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 2 ] <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 4)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 2 ] <: i16) >>! 8l <: i16) |.
            (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 3 ] <: i16) &. 15s <: i16) <<! 4l
              <:
              i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 5)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 3 ] <: i16) >>! 4l <: i16) &. 255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 6)
      (cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 4 ] <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 7)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 4 ] <: i16) >>! 8l <: i16) |.
            (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 5 ] <: i16) &. 15s <: i16) <<! 4l
              <:
              i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 8)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 5 ] <: i16) >>! 4l <: i16) &. 255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 9)
      (cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 6 ] <: i16) &. 255s <: i16) <: u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 10)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 6 ] <: i16) >>! 8l <: i16) |.
            (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 7 ] <: i16) &. 15s <: i16) <<! 4l
              <:
              i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 11)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 7 ] <: i16) >>! 4l <: i16) &. 255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 12)
      (cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) &. 255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 13)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) >>! 8l
              <:
              i16) |.
            (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) &. 15s
                <:
                i16) <<!
              4l
              <:
              i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 14)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) >>! 4l
              <:
              i16) &.
            255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 15)
      (cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) &. 255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 16)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) >>! 8l
              <:
              i16) |.
            (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) &. 15s
                <:
                i16) <<!
              4l
              <:
              i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 17)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) >>! 4l
              <:
              i16) &.
            255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 18)
      (cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) &. 255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 19)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) >>! 8l
              <:
              i16) |.
            (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) &. 15s
                <:
                i16) <<!
              4l
              <:
              i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 20)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) >>! 4l
              <:
              i16) &.
            255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 21)
      (cast ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16) &. 255s
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 22)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16) >>! 8l
              <:
              i16) |.
            (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16) &. 15s
                <:
                i16) <<!
              4l
              <:
              i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 24) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 23)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16) >>! 4l
              <:
              i16) &.
            255s
            <:
            i16)
        <:
        u8)
  in
  result

let serialize_4_ (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) =
  let result:t_Array u8 (sz 8) = Rust_primitives.Hax.repeat 0uy (sz 8) in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 0)
      (((cast (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 1 ] <: i16) <: u8) <<! 4l <: u8) |.
        (cast (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 0 ] <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 1)
      (((cast (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 3 ] <: i16) <: u8) <<! 4l <: u8) |.
        (cast (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 2 ] <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 2)
      (((cast (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 5 ] <: i16) <: u8) <<! 4l <: u8) |.
        (cast (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 4 ] <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 3)
      (((cast (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 7 ] <: i16) <: u8) <<! 4l <: u8) |.
        (cast (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 6 ] <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 4)
      (((cast (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) <: u8) <<!
          4l
          <:
          u8) |.
        (cast (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 5)
      (((cast (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) <: u8) <<!
          4l
          <:
          u8) |.
        (cast (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 6)
      (((cast (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) <: u8) <<!
          4l
          <:
          u8) |.
        (cast (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 8) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 7)
      (((cast (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16) <: u8) <<!
          4l
          <:
          u8) |.
        (cast (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16) <: u8)
        <:
        u8)
  in
  result

let serialize_5_ (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) =
  let result:t_Array u8 (sz 10) = Rust_primitives.Hax.repeat 0uy (sz 10) in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 0)
      (cast ((((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 1 ] <: i16) &. 7s <: i16) <<! 5l
              <:
              i16) |.
            (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 0 ] <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 1)
      (cast (((((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 3 ] <: i16) &. 1s <: i16) <<! 7l
                <:
                i16) |.
              ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 2 ] <: i16) <<! 2l <: i16)
              <:
              i16) |.
            ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 1 ] <: i16) >>! 3l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 2)
      (cast ((((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 4 ] <: i16) &. 15s <: i16) <<! 4l
              <:
              i16) |.
            ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 3 ] <: i16) >>! 1l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 3)
      (cast (((((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 6 ] <: i16) &. 3s <: i16) <<! 6l
                <:
                i16) |.
              ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 5 ] <: i16) <<! 1l <: i16)
              <:
              i16) |.
            ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 4 ] <: i16) >>! 4l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 4)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 7 ] <: i16) <<! 3l <: i16) |.
            ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 6 ] <: i16) >>! 2l <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 5)
      (cast ((((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) &. 7s
                <:
                i16) <<!
              5l
              <:
              i16) |.
            (v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 6)
      (cast (((((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) &. 1s
                  <:
                  i16) <<!
                7l
                <:
                i16) |.
              ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) <<! 2l
                <:
                i16)
              <:
              i16) |.
            ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) >>! 3l
              <:
              i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 7)
      (cast ((((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) &. 15s
                <:
                i16) <<!
              4l
              <:
              i16) |.
            ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) >>! 1l
              <:
              i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 8)
      (cast (((((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16) &. 3s
                  <:
                  i16) <<!
                6l
                <:
                i16) |.
              ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) <<! 1l
                <:
                i16)
              <:
              i16) |.
            ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) >>! 4l
              <:
              i16)
            <:
            i16)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 9)
      (cast (((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16) <<! 3l
              <:
              i16) |.
            ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16) >>! 2l
              <:
              i16)
            <:
            i16)
        <:
        u8)
  in
  result

let shift_right (v_SHIFT_BY: i32) (v: Libcrux_ml_kem.Vector.Portable.t_PortableVector) =
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      v
      (fun v i ->
          let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector = v in
          let i:usize = i in
          {
            v with
            Libcrux_ml_kem.Vector.Portable.f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
                .Libcrux_ml_kem.Vector.Portable.f_elements
              i
              ((v.Libcrux_ml_kem.Vector.Portable.f_elements.[ i ] <: i16) >>! v_SHIFT_BY <: i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          Libcrux_ml_kem.Vector.Portable.t_PortableVector)
  in
  v

let sub (lhs rhs: Libcrux_ml_kem.Vector.Portable.t_PortableVector) =
  let lhs:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      lhs
      (fun lhs i ->
          let lhs:Libcrux_ml_kem.Vector.Portable.t_PortableVector = lhs in
          let i:usize = i in
          {
            lhs with
            Libcrux_ml_kem.Vector.Portable.f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs
                .Libcrux_ml_kem.Vector.Portable.f_elements
              i
              ((lhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ i ] <: i16) -!
                (rhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ i ] <: i16)
                <:
                i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          Libcrux_ml_kem.Vector.Portable.t_PortableVector)
  in
  lhs

let zero (_: Prims.unit) =
  { Libcrux_ml_kem.Vector.Portable.f_elements = Rust_primitives.Hax.repeat 0s (sz 16) }
  <:
  Libcrux_ml_kem.Vector.Portable.t_PortableVector

let deserialize_1_ (v: t_Slice u8) =
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector = zero () in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 8 }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      result
      (fun result i ->
          let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector = result in
          let i:usize = i in
          {
            result with
            Libcrux_ml_kem.Vector.Portable.f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
                .Libcrux_ml_kem.Vector.Portable.f_elements
              i
              (cast (((v.[ sz 0 ] <: u8) >>! i <: u8) &. 1uy <: u8) <: i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          Libcrux_ml_kem.Vector.Portable.t_PortableVector)
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          ({
              Core.Ops.Range.f_start = sz 8;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      result
      (fun result i ->
          let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector = result in
          let i:usize = i in
          {
            result with
            Libcrux_ml_kem.Vector.Portable.f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
                .Libcrux_ml_kem.Vector.Portable.f_elements
              i
              (cast (((v.[ sz 1 ] <: u8) >>! (i -! sz 8 <: usize) <: u8) &. 1uy <: u8) <: i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          Libcrux_ml_kem.Vector.Portable.t_PortableVector)
  in
  result

let deserialize_10_ (bytes: t_Slice u8) =
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector = zero () in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 0)
        ((((cast (bytes.[ sz 1 ] <: u8) <: i16) &. 3s <: i16) <<! 8l <: i16) |.
          ((cast (bytes.[ sz 0 ] <: u8) <: i16) &. 255s <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 1)
        ((((cast (bytes.[ sz 2 ] <: u8) <: i16) &. 15s <: i16) <<! 6l <: i16) |.
          ((cast (bytes.[ sz 1 ] <: u8) <: i16) >>! 2l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 2)
        ((((cast (bytes.[ sz 3 ] <: u8) <: i16) &. 63s <: i16) <<! 4l <: i16) |.
          ((cast (bytes.[ sz 2 ] <: u8) <: i16) >>! 4l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 3)
        (((cast (bytes.[ sz 4 ] <: u8) <: i16) <<! 2l <: i16) |.
          ((cast (bytes.[ sz 3 ] <: u8) <: i16) >>! 6l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 4)
        ((((cast (bytes.[ sz 6 ] <: u8) <: i16) &. 3s <: i16) <<! 8l <: i16) |.
          ((cast (bytes.[ sz 5 ] <: u8) <: i16) &. 255s <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 5)
        ((((cast (bytes.[ sz 7 ] <: u8) <: i16) &. 15s <: i16) <<! 6l <: i16) |.
          ((cast (bytes.[ sz 6 ] <: u8) <: i16) >>! 2l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 6)
        ((((cast (bytes.[ sz 8 ] <: u8) <: i16) &. 63s <: i16) <<! 4l <: i16) |.
          ((cast (bytes.[ sz 7 ] <: u8) <: i16) >>! 4l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 7)
        (((cast (bytes.[ sz 9 ] <: u8) <: i16) <<! 2l <: i16) |.
          ((cast (bytes.[ sz 8 ] <: u8) <: i16) >>! 6l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8)
        ((((cast (bytes.[ sz 10 +! sz 1 <: usize ] <: u8) <: i16) &. 3s <: i16) <<! 8l <: i16) |.
          ((cast (bytes.[ sz 10 +! sz 0 <: usize ] <: u8) <: i16) &. 255s <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 9)
        ((((cast (bytes.[ sz 10 +! sz 2 <: usize ] <: u8) <: i16) &. 15s <: i16) <<! 6l <: i16) |.
          ((cast (bytes.[ sz 10 +! sz 1 <: usize ] <: u8) <: i16) >>! 2l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 10)
        ((((cast (bytes.[ sz 10 +! sz 3 <: usize ] <: u8) <: i16) &. 63s <: i16) <<! 4l <: i16) |.
          ((cast (bytes.[ sz 10 +! sz 2 <: usize ] <: u8) <: i16) >>! 4l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 11)
        (((cast (bytes.[ sz 10 +! sz 4 <: usize ] <: u8) <: i16) <<! 2l <: i16) |.
          ((cast (bytes.[ sz 10 +! sz 3 <: usize ] <: u8) <: i16) >>! 6l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 12)
        ((((cast (bytes.[ sz 10 +! sz 6 <: usize ] <: u8) <: i16) &. 3s <: i16) <<! 8l <: i16) |.
          ((cast (bytes.[ sz 10 +! sz 5 <: usize ] <: u8) <: i16) &. 255s <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 13)
        ((((cast (bytes.[ sz 10 +! sz 7 <: usize ] <: u8) <: i16) &. 15s <: i16) <<! 6l <: i16) |.
          ((cast (bytes.[ sz 10 +! sz 6 <: usize ] <: u8) <: i16) >>! 2l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 14)
        ((((cast (bytes.[ sz 10 +! sz 8 <: usize ] <: u8) <: i16) &. 63s <: i16) <<! 4l <: i16) |.
          ((cast (bytes.[ sz 10 +! sz 7 <: usize ] <: u8) <: i16) >>! 4l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 15)
        (((cast (bytes.[ sz 10 +! sz 9 <: usize ] <: u8) <: i16) <<! 2l <: i16) |.
          ((cast (bytes.[ sz 10 +! sz 8 <: usize ] <: u8) <: i16) >>! 6l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  result

let deserialize_11_ (bytes: t_Slice u8) =
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector = zero () in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 0)
        ((((cast (bytes.[ sz 1 ] <: u8) <: i16) &. 7s <: i16) <<! 8l <: i16) |.
          (cast (bytes.[ sz 0 ] <: u8) <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 1)
        ((((cast (bytes.[ sz 2 ] <: u8) <: i16) &. 63s <: i16) <<! 5l <: i16) |.
          ((cast (bytes.[ sz 1 ] <: u8) <: i16) >>! 3l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 2)
        (((((cast (bytes.[ sz 4 ] <: u8) <: i16) &. 1s <: i16) <<! 10l <: i16) |.
            ((cast (bytes.[ sz 3 ] <: u8) <: i16) <<! 2l <: i16)
            <:
            i16) |.
          ((cast (bytes.[ sz 2 ] <: u8) <: i16) >>! 6l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 3)
        ((((cast (bytes.[ sz 5 ] <: u8) <: i16) &. 15s <: i16) <<! 7l <: i16) |.
          ((cast (bytes.[ sz 4 ] <: u8) <: i16) >>! 1l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 4)
        ((((cast (bytes.[ sz 6 ] <: u8) <: i16) &. 127s <: i16) <<! 4l <: i16) |.
          ((cast (bytes.[ sz 5 ] <: u8) <: i16) >>! 4l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 5)
        (((((cast (bytes.[ sz 8 ] <: u8) <: i16) &. 3s <: i16) <<! 9l <: i16) |.
            ((cast (bytes.[ sz 7 ] <: u8) <: i16) <<! 1l <: i16)
            <:
            i16) |.
          ((cast (bytes.[ sz 6 ] <: u8) <: i16) >>! 7l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 6)
        ((((cast (bytes.[ sz 9 ] <: u8) <: i16) &. 31s <: i16) <<! 6l <: i16) |.
          ((cast (bytes.[ sz 8 ] <: u8) <: i16) >>! 2l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 7)
        (((cast (bytes.[ sz 10 ] <: u8) <: i16) <<! 3l <: i16) |.
          ((cast (bytes.[ sz 9 ] <: u8) <: i16) >>! 5l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8)
        ((((cast (bytes.[ sz 11 +! sz 1 <: usize ] <: u8) <: i16) &. 7s <: i16) <<! 8l <: i16) |.
          (cast (bytes.[ sz 11 +! sz 0 <: usize ] <: u8) <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 9)
        ((((cast (bytes.[ sz 11 +! sz 2 <: usize ] <: u8) <: i16) &. 63s <: i16) <<! 5l <: i16) |.
          ((cast (bytes.[ sz 11 +! sz 1 <: usize ] <: u8) <: i16) >>! 3l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 10)
        (((((cast (bytes.[ sz 11 +! sz 4 <: usize ] <: u8) <: i16) &. 1s <: i16) <<! 10l <: i16) |.
            ((cast (bytes.[ sz 11 +! sz 3 <: usize ] <: u8) <: i16) <<! 2l <: i16)
            <:
            i16) |.
          ((cast (bytes.[ sz 11 +! sz 2 <: usize ] <: u8) <: i16) >>! 6l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 11)
        ((((cast (bytes.[ sz 11 +! sz 5 <: usize ] <: u8) <: i16) &. 15s <: i16) <<! 7l <: i16) |.
          ((cast (bytes.[ sz 11 +! sz 4 <: usize ] <: u8) <: i16) >>! 1l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 12)
        ((((cast (bytes.[ sz 11 +! sz 6 <: usize ] <: u8) <: i16) &. 127s <: i16) <<! 4l <: i16) |.
          ((cast (bytes.[ sz 11 +! sz 5 <: usize ] <: u8) <: i16) >>! 4l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 13)
        (((((cast (bytes.[ sz 11 +! sz 8 <: usize ] <: u8) <: i16) &. 3s <: i16) <<! 9l <: i16) |.
            ((cast (bytes.[ sz 11 +! sz 7 <: usize ] <: u8) <: i16) <<! 1l <: i16)
            <:
            i16) |.
          ((cast (bytes.[ sz 11 +! sz 6 <: usize ] <: u8) <: i16) >>! 7l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 14)
        ((((cast (bytes.[ sz 11 +! sz 9 <: usize ] <: u8) <: i16) &. 31s <: i16) <<! 6l <: i16) |.
          ((cast (bytes.[ sz 11 +! sz 8 <: usize ] <: u8) <: i16) >>! 2l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let result:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      result with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 15)
        (((cast (bytes.[ sz 11 +! sz 10 <: usize ] <: u8) <: i16) <<! 3l <: i16) |.
          ((cast (bytes.[ sz 11 +! sz 9 <: usize ] <: u8) <: i16) >>! 5l <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  result

let deserialize_12_ (bytes: t_Slice u8) =
  let re:Libcrux_ml_kem.Vector.Portable.t_PortableVector = zero () in
  let byte0:i16 = cast (bytes.[ sz 0 ] <: u8) <: i16 in
  let byte1:i16 = cast (bytes.[ sz 1 ] <: u8) <: i16 in
  let byte2:i16 = cast (bytes.[ sz 2 ] <: u8) <: i16 in
  let byte3:i16 = cast (bytes.[ sz 3 ] <: u8) <: i16 in
  let byte4:i16 = cast (bytes.[ sz 4 ] <: u8) <: i16 in
  let byte5:i16 = cast (bytes.[ sz 5 ] <: u8) <: i16 in
  let byte6:i16 = cast (bytes.[ sz 6 ] <: u8) <: i16 in
  let byte7:i16 = cast (bytes.[ sz 7 ] <: u8) <: i16 in
  let byte8:i16 = cast (bytes.[ sz 8 ] <: u8) <: i16 in
  let byte9:i16 = cast (bytes.[ sz 9 ] <: u8) <: i16 in
  let byte10:i16 = cast (bytes.[ sz 10 ] <: u8) <: i16 in
  let byte11:i16 = cast (bytes.[ sz 11 ] <: u8) <: i16 in
  let re:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 0)
        (((byte1 &. 15s <: i16) <<! 8l <: i16) |. (byte0 &. 255s <: i16) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let re:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 1)
        ((byte2 <<! 4l <: i16) |. ((byte1 >>! 4l <: i16) &. 15s <: i16) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let re:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 2)
        (((byte4 &. 15s <: i16) <<! 8l <: i16) |. (byte3 &. 255s <: i16) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let re:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 3)
        ((byte5 <<! 4l <: i16) |. ((byte4 >>! 4l <: i16) &. 15s <: i16) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let re:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 4)
        (((byte7 &. 15s <: i16) <<! 8l <: i16) |. (byte6 &. 255s <: i16) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let re:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 5)
        ((byte8 <<! 4l <: i16) |. ((byte7 >>! 4l <: i16) &. 15s <: i16) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let re:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 6)
        (((byte10 &. 15s <: i16) <<! 8l <: i16) |. (byte9 &. 255s <: i16) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let re:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 7)
        ((byte11 <<! 4l <: i16) |. ((byte10 >>! 4l <: i16) &. 15s <: i16) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let byte12:i16 = cast (bytes.[ sz 12 ] <: u8) <: i16 in
  let byte13:i16 = cast (bytes.[ sz 13 ] <: u8) <: i16 in
  let byte14:i16 = cast (bytes.[ sz 14 ] <: u8) <: i16 in
  let byte15:i16 = cast (bytes.[ sz 15 ] <: u8) <: i16 in
  let byte16:i16 = cast (bytes.[ sz 16 ] <: u8) <: i16 in
  let byte17:i16 = cast (bytes.[ sz 17 ] <: u8) <: i16 in
  let byte18:i16 = cast (bytes.[ sz 18 ] <: u8) <: i16 in
  let byte19:i16 = cast (bytes.[ sz 19 ] <: u8) <: i16 in
  let byte20:i16 = cast (bytes.[ sz 20 ] <: u8) <: i16 in
  let byte21:i16 = cast (bytes.[ sz 21 ] <: u8) <: i16 in
  let byte22:i16 = cast (bytes.[ sz 22 ] <: u8) <: i16 in
  let byte23:i16 = cast (bytes.[ sz 23 ] <: u8) <: i16 in
  let re:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8)
        (((byte13 &. 15s <: i16) <<! 8l <: i16) |. (byte12 &. 255s <: i16) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let re:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 9)
        ((byte14 <<! 4l <: i16) |. ((byte13 >>! 4l <: i16) &. 15s <: i16) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let re:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 10)
        (((byte16 &. 15s <: i16) <<! 8l <: i16) |. (byte15 &. 255s <: i16) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let re:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 11)
        ((byte17 <<! 4l <: i16) |. ((byte16 >>! 4l <: i16) &. 15s <: i16) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let re:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 12)
        (((byte19 &. 15s <: i16) <<! 8l <: i16) |. (byte18 &. 255s <: i16) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let re:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 13)
        ((byte20 <<! 4l <: i16) |. ((byte19 >>! 4l <: i16) &. 15s <: i16) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let re:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 14)
        (((byte22 &. 15s <: i16) <<! 8l <: i16) |. (byte21 &. 255s <: i16) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let re:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      re with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 15)
        ((byte23 <<! 4l <: i16) |. ((byte22 >>! 4l <: i16) &. 15s <: i16) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  re

let deserialize_4_ (bytes: t_Slice u8) =
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector = zero () in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 0)
        (cast ((bytes.[ sz 0 ] <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 1)
        (cast (((bytes.[ sz 0 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 2)
        (cast ((bytes.[ sz 1 ] <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 3)
        (cast (((bytes.[ sz 1 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 4)
        (cast ((bytes.[ sz 2 ] <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 5)
        (cast (((bytes.[ sz 2 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 6)
        (cast ((bytes.[ sz 3 ] <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 7)
        (cast (((bytes.[ sz 3 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8)
        (cast ((bytes.[ sz 4 ] <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 9)
        (cast (((bytes.[ sz 4 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 10)
        (cast ((bytes.[ sz 5 ] <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 11)
        (cast (((bytes.[ sz 5 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 12)
        (cast ((bytes.[ sz 6 ] <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 13)
        (cast (((bytes.[ sz 6 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 14)
        (cast ((bytes.[ sz 7 ] <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 15)
        (cast (((bytes.[ sz 7 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  v

let deserialize_5_ (bytes: t_Slice u8) =
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector = zero () in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 0)
        (cast ((bytes.[ sz 0 ] <: u8) &. 31uy <: u8) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 1)
        (cast ((((bytes.[ sz 1 ] <: u8) &. 3uy <: u8) <<! 3l <: u8) |.
              ((bytes.[ sz 0 ] <: u8) >>! 5l <: u8)
              <:
              u8)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 2)
        (cast (((bytes.[ sz 1 ] <: u8) >>! 2l <: u8) &. 31uy <: u8) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 3)
        (cast ((((bytes.[ sz 2 ] <: u8) &. 15uy <: u8) <<! 1l <: u8) |.
              ((bytes.[ sz 1 ] <: u8) >>! 7l <: u8)
              <:
              u8)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 4)
        (cast ((((bytes.[ sz 3 ] <: u8) &. 1uy <: u8) <<! 4l <: u8) |.
              ((bytes.[ sz 2 ] <: u8) >>! 4l <: u8)
              <:
              u8)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 5)
        (cast (((bytes.[ sz 3 ] <: u8) >>! 1l <: u8) &. 31uy <: u8) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 6)
        (cast ((((bytes.[ sz 4 ] <: u8) &. 7uy <: u8) <<! 2l <: u8) |.
              ((bytes.[ sz 3 ] <: u8) >>! 6l <: u8)
              <:
              u8)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 7)
        (cast ((bytes.[ sz 4 ] <: u8) >>! 3l <: u8) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8)
        (cast ((bytes.[ sz 5 +! sz 0 <: usize ] <: u8) &. 31uy <: u8) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 9)
        (cast ((((bytes.[ sz 5 +! sz 1 <: usize ] <: u8) &. 3uy <: u8) <<! 3l <: u8) |.
              ((bytes.[ sz 5 +! sz 0 <: usize ] <: u8) >>! 5l <: u8)
              <:
              u8)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 10)
        (cast (((bytes.[ sz 5 +! sz 1 <: usize ] <: u8) >>! 2l <: u8) &. 31uy <: u8) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 11)
        (cast ((((bytes.[ sz 5 +! sz 2 <: usize ] <: u8) &. 15uy <: u8) <<! 1l <: u8) |.
              ((bytes.[ sz 5 +! sz 1 <: usize ] <: u8) >>! 7l <: u8)
              <:
              u8)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 12)
        (cast ((((bytes.[ sz 5 +! sz 3 <: usize ] <: u8) &. 1uy <: u8) <<! 4l <: u8) |.
              ((bytes.[ sz 5 +! sz 2 <: usize ] <: u8) >>! 4l <: u8)
              <:
              u8)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 13)
        (cast (((bytes.[ sz 5 +! sz 3 <: usize ] <: u8) >>! 1l <: u8) &. 31uy <: u8) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 14)
        (cast ((((bytes.[ sz 5 +! sz 4 <: usize ] <: u8) &. 7uy <: u8) <<! 2l <: u8) |.
              ((bytes.[ sz 5 +! sz 3 <: usize ] <: u8) >>! 6l <: u8)
              <:
              u8)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 15)
        (cast ((bytes.[ sz 5 +! sz 4 <: usize ] <: u8) >>! 3l <: u8) <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  v

let ntt_multiply
      (lhs rhs: Libcrux_ml_kem.Vector.Portable.t_PortableVector)
      (zeta0 zeta1 zeta2 zeta3: i16)
     =
  let out:Libcrux_ml_kem.Vector.Portable.t_PortableVector = zero () in
  let product:(i16 & i16) =
    ntt_multiply_binomials ((lhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 0 ] <: i16),
        (lhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 1 ] <: i16)
        <:
        (i16 & i16))
      ((rhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 0 ] <: i16),
        (rhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 1 ] <: i16)
        <:
        (i16 & i16))
      zeta0
  in
  let out:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 0)
        product._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let out:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 1)
        product._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let product:(i16 & i16) =
    ntt_multiply_binomials ((lhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 2 ] <: i16),
        (lhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 3 ] <: i16)
        <:
        (i16 & i16))
      ((rhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 2 ] <: i16),
        (rhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 3 ] <: i16)
        <:
        (i16 & i16))
      (Core.Ops.Arith.Neg.neg zeta0 <: i16)
  in
  let out:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 2)
        product._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let out:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 3)
        product._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let product:(i16 & i16) =
    ntt_multiply_binomials ((lhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 4 ] <: i16),
        (lhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 5 ] <: i16)
        <:
        (i16 & i16))
      ((rhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 4 ] <: i16),
        (rhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 5 ] <: i16)
        <:
        (i16 & i16))
      zeta1
  in
  let out:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 4)
        product._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let out:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 5)
        product._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let product:(i16 & i16) =
    ntt_multiply_binomials ((lhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 6 ] <: i16),
        (lhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 7 ] <: i16)
        <:
        (i16 & i16))
      ((rhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 6 ] <: i16),
        (rhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 7 ] <: i16)
        <:
        (i16 & i16))
      (Core.Ops.Arith.Neg.neg zeta1 <: i16)
  in
  let out:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 6)
        product._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let out:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 7)
        product._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let product:(i16 & i16) =
    ntt_multiply_binomials ((lhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 0 <: usize ]
          <:
          i16),
        (lhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16)
        <:
        (i16 & i16))
      ((rhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16),
        (rhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16)
        <:
        (i16 & i16))
      zeta2
  in
  let out:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 0 <: usize)
        product._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let out:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 1 <: usize)
        product._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let product:(i16 & i16) =
    ntt_multiply_binomials ((lhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 2 <: usize ]
          <:
          i16),
        (lhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16)
        <:
        (i16 & i16))
      ((rhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16),
        (rhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16)
        <:
        (i16 & i16))
      (Core.Ops.Arith.Neg.neg zeta2 <: i16)
  in
  let out:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 2 <: usize)
        product._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let out:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 3 <: usize)
        product._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let product:(i16 & i16) =
    ntt_multiply_binomials ((lhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 4 <: usize ]
          <:
          i16),
        (lhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16)
        <:
        (i16 & i16))
      ((rhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16),
        (rhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16)
        <:
        (i16 & i16))
      zeta3
  in
  let out:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 4 <: usize)
        product._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let out:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 5 <: usize)
        product._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let product:(i16 & i16) =
    ntt_multiply_binomials ((lhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 6 <: usize ]
          <:
          i16),
        (lhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16)
        <:
        (i16 & i16))
      ((rhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16),
        (rhs.Libcrux_ml_kem.Vector.Portable.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16)
        <:
        (i16 & i16))
      (Core.Ops.Arith.Neg.neg zeta3 <: i16)
  in
  let out:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 6 <: usize)
        product._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  let out:Libcrux_ml_kem.Vector.Portable.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.f_elements
        (sz 8 +! sz 7 <: usize)
        product._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.t_PortableVector
  in
  out
