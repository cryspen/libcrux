module Libcrux_ml_kem.Simd.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_ZERO (_: Prims.unit) =
  { f_elements = Rust_primitives.Hax.repeat 0l (sz 8) } <: t_PortableVector

let add (lhs rhs: t_PortableVector) =
  let lhs:t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Simd.Simd_trait.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      lhs
      (fun lhs i ->
          let lhs:t_PortableVector = lhs in
          let i:usize = i in
          {
            lhs with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs.f_elements
              i
              ((lhs.f_elements.[ i ] <: i32) +! (rhs.f_elements.[ i ] <: i32) <: i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_PortableVector)
  in
  lhs

let add_constant (v: t_PortableVector) (c: i32) =
  let v:t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Simd.Simd_trait.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      v
      (fun v i ->
          let v:t_PortableVector = v in
          let i:usize = i in
          {
            v with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
              i
              ((v.f_elements.[ i ] <: i32) +! c <: i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_PortableVector)
  in
  v

let barrett_reduce (v: t_PortableVector) =
  let v:t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Simd.Simd_trait.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      v
      (fun v i ->
          let v:t_PortableVector = v in
          let i:usize = i in
          {
            v with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
              i
              (Libcrux_ml_kem.Arithmetic.barrett_reduce (v.f_elements.[ i ] <: i32) <: i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_PortableVector)
  in
  v

let bitwise_and_with_constant (v: t_PortableVector) (c: i32) =
  let v:t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Simd.Simd_trait.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      v
      (fun v i ->
          let v:t_PortableVector = v in
          let i:usize = i in
          {
            v with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
              i
              ((v.f_elements.[ i ] <: i32) &. c <: i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_PortableVector)
  in
  v

let compress (coefficient_bits: u8) (v: t_PortableVector) =
  let v:t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Simd.Simd_trait.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      v
      (fun v i ->
          let v:t_PortableVector = v in
          let i:usize = i in
          {
            v with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
              i
              (Libcrux_ml_kem.Compress.compress_ciphertext_coefficient coefficient_bits
                  (cast (v.f_elements.[ i ] <: i32) <: u16)
                <:
                i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_PortableVector)
  in
  v

let compress_1_ (v: t_PortableVector) =
  let v:t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Simd.Simd_trait.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      v
      (fun v i ->
          let v:t_PortableVector = v in
          let i:usize = i in
          {
            v with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
              i
              (cast (Libcrux_ml_kem.Compress.compress_message_coefficient (cast (v.f_elements.[ i ]
                            <:
                            i32)
                        <:
                        u16)
                    <:
                    u8)
                <:
                i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_PortableVector)
  in
  v

let cond_subtract_3329_ (v: t_PortableVector) =
  let v:t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Simd.Simd_trait.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      v
      (fun v i ->
          let v:t_PortableVector = v in
          let i:usize = i in
          let _:Prims.unit =
            if true
            then
              let _:Prims.unit =
                if
                  ~.(((v.f_elements.[ i ] <: i32) >=. 0l <: bool) &&
                    ((v.f_elements.[ i ] <: i32) <. 4096l <: bool))
                then
                  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: v.elements[i] >= 0 && v.elements[i] < 4096"

                      <:
                      Rust_primitives.Hax.t_Never)
              in
              ()
          in
          if (v.f_elements.[ i ] <: i32) >=. 3329l
          then
            {
              v with
              f_elements
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
                i
                ((v.f_elements.[ i ] <: i32) -! 3329l <: i32)
            }
            <:
            t_PortableVector
          else v)
  in
  v

let from_i32_array (array: t_Array i32 (sz 8)) = { f_elements = array } <: t_PortableVector

let inv_ntt_layer_1_step (v: t_PortableVector) (zeta1 zeta2: i32) =
  let a_minus_b:i32 = (v.f_elements.[ sz 2 ] <: i32) -! (v.f_elements.[ sz 0 ] <: i32) in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 0)
        ((v.f_elements.[ sz 0 ] <: i32) +! (v.f_elements.[ sz 2 ] <: i32) <: i32)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 2)
        (Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta1 <: i32)
    }
    <:
    t_PortableVector
  in
  let a_minus_b:i32 = (v.f_elements.[ sz 3 ] <: i32) -! (v.f_elements.[ sz 1 ] <: i32) in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 1)
        ((v.f_elements.[ sz 1 ] <: i32) +! (v.f_elements.[ sz 3 ] <: i32) <: i32)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 3)
        (Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta1 <: i32)
    }
    <:
    t_PortableVector
  in
  let a_minus_b:i32 = (v.f_elements.[ sz 6 ] <: i32) -! (v.f_elements.[ sz 4 ] <: i32) in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 4)
        ((v.f_elements.[ sz 4 ] <: i32) +! (v.f_elements.[ sz 6 ] <: i32) <: i32)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 6)
        (Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta2 <: i32)
    }
    <:
    t_PortableVector
  in
  let a_minus_b:i32 = (v.f_elements.[ sz 7 ] <: i32) -! (v.f_elements.[ sz 5 ] <: i32) in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 5)
        ((v.f_elements.[ sz 5 ] <: i32) +! (v.f_elements.[ sz 7 ] <: i32) <: i32)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 7)
        (Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta2 <: i32)
    }
    <:
    t_PortableVector
  in
  v

let inv_ntt_layer_2_step (v: t_PortableVector) (zeta: i32) =
  let a_minus_b:i32 = (v.f_elements.[ sz 4 ] <: i32) -! (v.f_elements.[ sz 0 ] <: i32) in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 0)
        ((v.f_elements.[ sz 0 ] <: i32) +! (v.f_elements.[ sz 4 ] <: i32) <: i32)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 4)
        (Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta <: i32)
    }
    <:
    t_PortableVector
  in
  let a_minus_b:i32 = (v.f_elements.[ sz 5 ] <: i32) -! (v.f_elements.[ sz 1 ] <: i32) in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 1)
        ((v.f_elements.[ sz 1 ] <: i32) +! (v.f_elements.[ sz 5 ] <: i32) <: i32)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 5)
        (Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta <: i32)
    }
    <:
    t_PortableVector
  in
  let a_minus_b:i32 = (v.f_elements.[ sz 6 ] <: i32) -! (v.f_elements.[ sz 2 ] <: i32) in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 2)
        ((v.f_elements.[ sz 2 ] <: i32) +! (v.f_elements.[ sz 6 ] <: i32) <: i32)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 6)
        (Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta <: i32)
    }
    <:
    t_PortableVector
  in
  let a_minus_b:i32 = (v.f_elements.[ sz 7 ] <: i32) -! (v.f_elements.[ sz 3 ] <: i32) in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 3)
        ((v.f_elements.[ sz 3 ] <: i32) +! (v.f_elements.[ sz 7 ] <: i32) <: i32)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 7)
        (Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta <: i32)
    }
    <:
    t_PortableVector
  in
  v

let montgomery_reduce (v: t_PortableVector) =
  let v:t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Simd.Simd_trait.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      v
      (fun v i ->
          let v:t_PortableVector = v in
          let i:usize = i in
          {
            v with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
              i
              (Libcrux_ml_kem.Arithmetic.montgomery_reduce (v.f_elements.[ i ] <: i32) <: i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_PortableVector)
  in
  v

let multiply_by_constant (v: t_PortableVector) (c: i32) =
  let v:t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Simd.Simd_trait.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      v
      (fun v i ->
          let v:t_PortableVector = v in
          let i:usize = i in
          {
            v with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
              i
              ((v.f_elements.[ i ] <: i32) *! c <: i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_PortableVector)
  in
  v

let ntt_layer_1_step (v: t_PortableVector) (zeta1 zeta2: i32) =
  let t:i32 =
    Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer (v.f_elements.[ sz 2 ] <: i32) zeta1
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 2)
        ((v.f_elements.[ sz 0 ] <: i32) -! t <: i32)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 0)
        ((v.f_elements.[ sz 0 ] <: i32) +! t <: i32)
    }
    <:
    t_PortableVector
  in
  let t:i32 =
    Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer (v.f_elements.[ sz 3 ] <: i32) zeta1
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 3)
        ((v.f_elements.[ sz 1 ] <: i32) -! t <: i32)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 1)
        ((v.f_elements.[ sz 1 ] <: i32) +! t <: i32)
    }
    <:
    t_PortableVector
  in
  let t:i32 =
    Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer (v.f_elements.[ sz 6 ] <: i32) zeta2
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 6)
        ((v.f_elements.[ sz 4 ] <: i32) -! t <: i32)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 4)
        ((v.f_elements.[ sz 4 ] <: i32) +! t <: i32)
    }
    <:
    t_PortableVector
  in
  let t:i32 =
    Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer (v.f_elements.[ sz 7 ] <: i32) zeta2
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 7)
        ((v.f_elements.[ sz 5 ] <: i32) -! t <: i32)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 5)
        ((v.f_elements.[ sz 5 ] <: i32) +! t <: i32)
    }
    <:
    t_PortableVector
  in
  v

let ntt_layer_2_step (v: t_PortableVector) (zeta: i32) =
  let t:i32 =
    Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer (v.f_elements.[ sz 4 ] <: i32) zeta
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 4)
        ((v.f_elements.[ sz 0 ] <: i32) -! t <: i32)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 0)
        ((v.f_elements.[ sz 0 ] <: i32) +! t <: i32)
    }
    <:
    t_PortableVector
  in
  let t:i32 =
    Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer (v.f_elements.[ sz 5 ] <: i32) zeta
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 5)
        ((v.f_elements.[ sz 1 ] <: i32) -! t <: i32)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 1)
        ((v.f_elements.[ sz 1 ] <: i32) +! t <: i32)
    }
    <:
    t_PortableVector
  in
  let t:i32 =
    Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer (v.f_elements.[ sz 6 ] <: i32) zeta
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 6)
        ((v.f_elements.[ sz 2 ] <: i32) -! t <: i32)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 2)
        ((v.f_elements.[ sz 2 ] <: i32) +! t <: i32)
    }
    <:
    t_PortableVector
  in
  let t:i32 =
    Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer (v.f_elements.[ sz 7 ] <: i32) zeta
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 7)
        ((v.f_elements.[ sz 3 ] <: i32) -! t <: i32)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 3)
        ((v.f_elements.[ sz 3 ] <: i32) +! t <: i32)
    }
    <:
    t_PortableVector
  in
  v

let serialize_1_ (v: t_PortableVector) =
  let result:u8 = 0uy in
  let result:u8 =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Simd.Simd_trait.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      result
      (fun result i ->
          let result:u8 = result in
          let i:usize = i in
          result |. ((cast (v.f_elements.[ i ] <: i32) <: u8) <<! i <: u8) <: u8)
  in
  result

let serialize_10_ (v: t_PortableVector) =
  let result:t_Array u8 (sz 10) = Rust_primitives.Hax.repeat 0uy (sz 10) in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 0)
      (cast ((v.f_elements.[ sz 0 ] <: i32) &. 255l <: i32) <: u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 1)
      (((cast ((v.f_elements.[ sz 1 ] <: i32) &. 63l <: i32) <: u8) <<! 2l <: u8) |.
        (cast (((v.f_elements.[ sz 0 ] <: i32) >>! 8l <: i32) &. 3l <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 2)
      (((cast ((v.f_elements.[ sz 2 ] <: i32) &. 15l <: i32) <: u8) <<! 4l <: u8) |.
        (cast (((v.f_elements.[ sz 1 ] <: i32) >>! 6l <: i32) &. 15l <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 3)
      (((cast ((v.f_elements.[ sz 3 ] <: i32) &. 3l <: i32) <: u8) <<! 6l <: u8) |.
        (cast (((v.f_elements.[ sz 2 ] <: i32) >>! 4l <: i32) &. 63l <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 4)
      (cast (((v.f_elements.[ sz 3 ] <: i32) >>! 2l <: i32) &. 255l <: i32) <: u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 5)
      (cast ((v.f_elements.[ sz 4 ] <: i32) &. 255l <: i32) <: u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 6)
      (((cast ((v.f_elements.[ sz 5 ] <: i32) &. 63l <: i32) <: u8) <<! 2l <: u8) |.
        (cast (((v.f_elements.[ sz 4 ] <: i32) >>! 8l <: i32) &. 3l <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 7)
      (((cast ((v.f_elements.[ sz 6 ] <: i32) &. 15l <: i32) <: u8) <<! 4l <: u8) |.
        (cast (((v.f_elements.[ sz 5 ] <: i32) >>! 6l <: i32) &. 15l <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 8)
      (((cast ((v.f_elements.[ sz 7 ] <: i32) &. 3l <: i32) <: u8) <<! 6l <: u8) |.
        (cast (((v.f_elements.[ sz 6 ] <: i32) >>! 4l <: i32) &. 63l <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 10) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 9)
      (cast (((v.f_elements.[ sz 7 ] <: i32) >>! 2l <: i32) &. 255l <: i32) <: u8)
  in
  result

let serialize_11_ (v: t_PortableVector) =
  let result:t_Array u8 (sz 11) = Rust_primitives.Hax.repeat 0uy (sz 11) in
  let result:t_Array u8 (sz 11) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 0)
      (cast (v.f_elements.[ sz 0 ] <: i32) <: u8)
  in
  let result:t_Array u8 (sz 11) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 1)
      (((cast ((v.f_elements.[ sz 1 ] <: i32) &. 31l <: i32) <: u8) <<! 3l <: u8) |.
        (cast ((v.f_elements.[ sz 0 ] <: i32) >>! 8l <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 11) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 2)
      (((cast ((v.f_elements.[ sz 2 ] <: i32) &. 3l <: i32) <: u8) <<! 6l <: u8) |.
        (cast ((v.f_elements.[ sz 1 ] <: i32) >>! 5l <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 11) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 3)
      (cast (((v.f_elements.[ sz 2 ] <: i32) >>! 2l <: i32) &. 255l <: i32) <: u8)
  in
  let result:t_Array u8 (sz 11) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 4)
      (((cast ((v.f_elements.[ sz 3 ] <: i32) &. 127l <: i32) <: u8) <<! 1l <: u8) |.
        (cast ((v.f_elements.[ sz 2 ] <: i32) >>! 10l <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 11) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 5)
      (((cast ((v.f_elements.[ sz 4 ] <: i32) &. 15l <: i32) <: u8) <<! 4l <: u8) |.
        (cast ((v.f_elements.[ sz 3 ] <: i32) >>! 7l <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 11) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 6)
      (((cast ((v.f_elements.[ sz 5 ] <: i32) &. 1l <: i32) <: u8) <<! 7l <: u8) |.
        (cast ((v.f_elements.[ sz 4 ] <: i32) >>! 4l <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 11) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 7)
      (cast (((v.f_elements.[ sz 5 ] <: i32) >>! 1l <: i32) &. 255l <: i32) <: u8)
  in
  let result:t_Array u8 (sz 11) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 8)
      (((cast ((v.f_elements.[ sz 6 ] <: i32) &. 63l <: i32) <: u8) <<! 2l <: u8) |.
        (cast ((v.f_elements.[ sz 5 ] <: i32) >>! 9l <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 11) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 9)
      (((cast ((v.f_elements.[ sz 7 ] <: i32) &. 7l <: i32) <: u8) <<! 5l <: u8) |.
        (cast ((v.f_elements.[ sz 6 ] <: i32) >>! 6l <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 11) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 10)
      (cast ((v.f_elements.[ sz 7 ] <: i32) >>! 3l <: i32) <: u8)
  in
  result

let serialize_12_ (v: t_PortableVector) =
  let result:t_Array u8 (sz 12) = Rust_primitives.Hax.repeat 0uy (sz 12) in
  let result:t_Array u8 (sz 12) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 0)
      (cast ((v.f_elements.[ sz 0 ] <: i32) &. 255l <: i32) <: u8)
  in
  let result:t_Array u8 (sz 12) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 1)
      (cast (((v.f_elements.[ sz 0 ] <: i32) >>! 8l <: i32) |.
            (((v.f_elements.[ sz 1 ] <: i32) &. 15l <: i32) <<! 4l <: i32)
            <:
            i32)
        <:
        u8)
  in
  let result:t_Array u8 (sz 12) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 2)
      (cast (((v.f_elements.[ sz 1 ] <: i32) >>! 4l <: i32) &. 255l <: i32) <: u8)
  in
  let result:t_Array u8 (sz 12) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 3)
      (cast ((v.f_elements.[ sz 2 ] <: i32) &. 255l <: i32) <: u8)
  in
  let result:t_Array u8 (sz 12) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 4)
      (cast (((v.f_elements.[ sz 2 ] <: i32) >>! 8l <: i32) |.
            (((v.f_elements.[ sz 3 ] <: i32) &. 15l <: i32) <<! 4l <: i32)
            <:
            i32)
        <:
        u8)
  in
  let result:t_Array u8 (sz 12) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 5)
      (cast (((v.f_elements.[ sz 3 ] <: i32) >>! 4l <: i32) &. 255l <: i32) <: u8)
  in
  let result:t_Array u8 (sz 12) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 6)
      (cast ((v.f_elements.[ sz 4 ] <: i32) &. 255l <: i32) <: u8)
  in
  let result:t_Array u8 (sz 12) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 7)
      (cast (((v.f_elements.[ sz 4 ] <: i32) >>! 8l <: i32) |.
            (((v.f_elements.[ sz 5 ] <: i32) &. 15l <: i32) <<! 4l <: i32)
            <:
            i32)
        <:
        u8)
  in
  let result:t_Array u8 (sz 12) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 8)
      (cast (((v.f_elements.[ sz 5 ] <: i32) >>! 4l <: i32) &. 255l <: i32) <: u8)
  in
  let result:t_Array u8 (sz 12) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 9)
      (cast ((v.f_elements.[ sz 6 ] <: i32) &. 255l <: i32) <: u8)
  in
  let result:t_Array u8 (sz 12) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 10)
      (cast (((v.f_elements.[ sz 6 ] <: i32) >>! 8l <: i32) |.
            (((v.f_elements.[ sz 7 ] <: i32) &. 15l <: i32) <<! 4l <: i32)
            <:
            i32)
        <:
        u8)
  in
  let result:t_Array u8 (sz 12) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 11)
      (cast (((v.f_elements.[ sz 7 ] <: i32) >>! 4l <: i32) &. 255l <: i32) <: u8)
  in
  result

let serialize_4_ (v: t_PortableVector) =
  let result:t_Array u8 (sz 4) = Rust_primitives.Hax.repeat 0uy (sz 4) in
  let result:t_Array u8 (sz 4) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 0)
      (((cast (v.f_elements.[ sz 1 ] <: i32) <: u8) <<! 4l <: u8) |.
        (cast (v.f_elements.[ sz 0 ] <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 4) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 1)
      (((cast (v.f_elements.[ sz 3 ] <: i32) <: u8) <<! 4l <: u8) |.
        (cast (v.f_elements.[ sz 2 ] <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 4) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 2)
      (((cast (v.f_elements.[ sz 5 ] <: i32) <: u8) <<! 4l <: u8) |.
        (cast (v.f_elements.[ sz 4 ] <: i32) <: u8)
        <:
        u8)
  in
  let result:t_Array u8 (sz 4) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 3)
      (((cast (v.f_elements.[ sz 7 ] <: i32) <: u8) <<! 4l <: u8) |.
        (cast (v.f_elements.[ sz 6 ] <: i32) <: u8)
        <:
        u8)
  in
  result

let serialize_5_ (v: t_PortableVector) =
  let result:t_Array u8 (sz 5) = Rust_primitives.Hax.repeat 0uy (sz 5) in
  let result:t_Array u8 (sz 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 0)
      (cast ((((v.f_elements.[ sz 1 ] <: i32) &. 7l <: i32) <<! 5l <: i32) |.
            (v.f_elements.[ sz 0 ] <: i32)
            <:
            i32)
        <:
        u8)
  in
  let result:t_Array u8 (sz 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 1)
      (cast (((((v.f_elements.[ sz 3 ] <: i32) &. 1l <: i32) <<! 7l <: i32) |.
              ((v.f_elements.[ sz 2 ] <: i32) <<! 2l <: i32)
              <:
              i32) |.
            ((v.f_elements.[ sz 1 ] <: i32) >>! 3l <: i32)
            <:
            i32)
        <:
        u8)
  in
  let result:t_Array u8 (sz 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 2)
      (cast ((((v.f_elements.[ sz 4 ] <: i32) &. 15l <: i32) <<! 4l <: i32) |.
            ((v.f_elements.[ sz 3 ] <: i32) >>! 1l <: i32)
            <:
            i32)
        <:
        u8)
  in
  let result:t_Array u8 (sz 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 3)
      (cast (((((v.f_elements.[ sz 6 ] <: i32) &. 3l <: i32) <<! 6l <: i32) |.
              ((v.f_elements.[ sz 5 ] <: i32) <<! 1l <: i32)
              <:
              i32) |.
            ((v.f_elements.[ sz 4 ] <: i32) >>! 4l <: i32)
            <:
            i32)
        <:
        u8)
  in
  let result:t_Array u8 (sz 5) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
      (sz 4)
      (cast (((v.f_elements.[ sz 7 ] <: i32) <<! 3l <: i32) |.
            ((v.f_elements.[ sz 6 ] <: i32) >>! 2l <: i32)
            <:
            i32)
        <:
        u8)
  in
  result

let shift_left (v_SHIFT_BY: i32) (lhs: t_PortableVector) =
  let lhs:t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Simd.Simd_trait.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      lhs
      (fun lhs i ->
          let lhs:t_PortableVector = lhs in
          let i:usize = i in
          {
            lhs with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs.f_elements
              i
              ((lhs.f_elements.[ i ] <: i32) <<! v_SHIFT_BY <: i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_PortableVector)
  in
  lhs

let shift_right (v_SHIFT_BY: i32) (v: t_PortableVector) =
  let v:t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Simd.Simd_trait.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      v
      (fun v i ->
          let v:t_PortableVector = v in
          let i:usize = i in
          {
            v with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
              i
              ((v.f_elements.[ i ] <: i32) >>! v_SHIFT_BY <: i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_PortableVector)
  in
  v

let sub (lhs rhs: t_PortableVector) =
  let lhs:t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Simd.Simd_trait.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      lhs
      (fun lhs i ->
          let lhs:t_PortableVector = lhs in
          let i:usize = i in
          {
            lhs with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs.f_elements
              i
              ((lhs.f_elements.[ i ] <: i32) -! (rhs.f_elements.[ i ] <: i32) <: i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_PortableVector)
  in
  lhs

let to_i32_array (v: t_PortableVector) = v.f_elements

let deserialize_1_ (v: u8) =
  let result:t_PortableVector = Libcrux_ml_kem.Simd.Simd_trait.f_ZERO () in
  let result:t_PortableVector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Libcrux_ml_kem.Simd.Simd_trait.v_FIELD_ELEMENTS_IN_VECTOR
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      result
      (fun result i ->
          let result:t_PortableVector = result in
          let i:usize = i in
          {
            result with
            f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
              i
              (cast ((v >>! i <: u8) &. 1uy <: u8) <: i32)
            <:
            t_Array i32 (sz 8)
          }
          <:
          t_PortableVector)
  in
  result

let deserialize_10_ (bytes: t_Slice u8) =
  let result:t_PortableVector = Libcrux_ml_kem.Simd.Simd_trait.f_ZERO () in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 0)
        ((((cast (bytes.[ sz 1 ] <: u8) <: i32) &. 3l <: i32) <<! 8l <: i32) |.
          ((cast (bytes.[ sz 0 ] <: u8) <: i32) &. 255l <: i32)
          <:
          i32)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 1)
        ((((cast (bytes.[ sz 2 ] <: u8) <: i32) &. 15l <: i32) <<! 6l <: i32) |.
          ((cast (bytes.[ sz 1 ] <: u8) <: i32) >>! 2l <: i32)
          <:
          i32)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 2)
        ((((cast (bytes.[ sz 3 ] <: u8) <: i32) &. 63l <: i32) <<! 4l <: i32) |.
          ((cast (bytes.[ sz 2 ] <: u8) <: i32) >>! 4l <: i32)
          <:
          i32)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 3)
        (((cast (bytes.[ sz 4 ] <: u8) <: i32) <<! 2l <: i32) |.
          ((cast (bytes.[ sz 3 ] <: u8) <: i32) >>! 6l <: i32)
          <:
          i32)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 4)
        ((((cast (bytes.[ sz 6 ] <: u8) <: i32) &. 3l <: i32) <<! 8l <: i32) |.
          ((cast (bytes.[ sz 5 ] <: u8) <: i32) &. 255l <: i32)
          <:
          i32)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 5)
        ((((cast (bytes.[ sz 7 ] <: u8) <: i32) &. 15l <: i32) <<! 6l <: i32) |.
          ((cast (bytes.[ sz 6 ] <: u8) <: i32) >>! 2l <: i32)
          <:
          i32)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 6)
        ((((cast (bytes.[ sz 8 ] <: u8) <: i32) &. 63l <: i32) <<! 4l <: i32) |.
          ((cast (bytes.[ sz 7 ] <: u8) <: i32) >>! 4l <: i32)
          <:
          i32)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 7)
        (((cast (bytes.[ sz 9 ] <: u8) <: i32) <<! 2l <: i32) |.
          ((cast (bytes.[ sz 8 ] <: u8) <: i32) >>! 6l <: i32)
          <:
          i32)
    }
    <:
    t_PortableVector
  in
  result

let deserialize_11_ (bytes: t_Slice u8) =
  let result:t_PortableVector = Libcrux_ml_kem.Simd.Simd_trait.f_ZERO () in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 0)
        ((((cast (bytes.[ sz 1 ] <: u8) <: i32) &. 7l <: i32) <<! 8l <: i32) |.
          (cast (bytes.[ sz 0 ] <: u8) <: i32)
          <:
          i32)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 1)
        ((((cast (bytes.[ sz 2 ] <: u8) <: i32) &. 63l <: i32) <<! 5l <: i32) |.
          ((cast (bytes.[ sz 1 ] <: u8) <: i32) >>! 3l <: i32)
          <:
          i32)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 2)
        (((((cast (bytes.[ sz 4 ] <: u8) <: i32) &. 1l <: i32) <<! 10l <: i32) |.
            ((cast (bytes.[ sz 3 ] <: u8) <: i32) <<! 2l <: i32)
            <:
            i32) |.
          ((cast (bytes.[ sz 2 ] <: u8) <: i32) >>! 6l <: i32)
          <:
          i32)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 3)
        ((((cast (bytes.[ sz 5 ] <: u8) <: i32) &. 15l <: i32) <<! 7l <: i32) |.
          ((cast (bytes.[ sz 4 ] <: u8) <: i32) >>! 1l <: i32)
          <:
          i32)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 4)
        ((((cast (bytes.[ sz 6 ] <: u8) <: i32) &. 127l <: i32) <<! 4l <: i32) |.
          ((cast (bytes.[ sz 5 ] <: u8) <: i32) >>! 4l <: i32)
          <:
          i32)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 5)
        (((((cast (bytes.[ sz 8 ] <: u8) <: i32) &. 3l <: i32) <<! 9l <: i32) |.
            ((cast (bytes.[ sz 7 ] <: u8) <: i32) <<! 1l <: i32)
            <:
            i32) |.
          ((cast (bytes.[ sz 6 ] <: u8) <: i32) >>! 7l <: i32)
          <:
          i32)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 6)
        ((((cast (bytes.[ sz 9 ] <: u8) <: i32) &. 31l <: i32) <<! 6l <: i32) |.
          ((cast (bytes.[ sz 8 ] <: u8) <: i32) >>! 2l <: i32)
          <:
          i32)
    }
    <:
    t_PortableVector
  in
  let result:t_PortableVector =
    {
      result with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result.f_elements
        (sz 7)
        (((cast (bytes.[ sz 10 ] <: u8) <: i32) <<! 3l <: i32) |.
          ((cast (bytes.[ sz 9 ] <: u8) <: i32) >>! 5l <: i32)
          <:
          i32)
    }
    <:
    t_PortableVector
  in
  result

let deserialize_12_ (bytes: t_Slice u8) =
  let re:t_PortableVector = Libcrux_ml_kem.Simd.Simd_trait.f_ZERO () in
  let byte0:i32 = cast (bytes.[ sz 0 ] <: u8) <: i32 in
  let byte1:i32 = cast (bytes.[ sz 1 ] <: u8) <: i32 in
  let byte2:i32 = cast (bytes.[ sz 2 ] <: u8) <: i32 in
  let byte3:i32 = cast (bytes.[ sz 3 ] <: u8) <: i32 in
  let byte4:i32 = cast (bytes.[ sz 4 ] <: u8) <: i32 in
  let byte5:i32 = cast (bytes.[ sz 5 ] <: u8) <: i32 in
  let byte6:i32 = cast (bytes.[ sz 6 ] <: u8) <: i32 in
  let byte7:i32 = cast (bytes.[ sz 7 ] <: u8) <: i32 in
  let byte8:i32 = cast (bytes.[ sz 8 ] <: u8) <: i32 in
  let byte9:i32 = cast (bytes.[ sz 9 ] <: u8) <: i32 in
  let byte10:i32 = cast (bytes.[ sz 10 ] <: u8) <: i32 in
  let byte11:i32 = cast (bytes.[ sz 11 ] <: u8) <: i32 in
  let re:t_PortableVector =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 0)
        (((byte1 &. 15l <: i32) <<! 8l <: i32) |. (byte0 &. 255l <: i32) <: i32)
    }
    <:
    t_PortableVector
  in
  let re:t_PortableVector =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 1)
        ((byte2 <<! 4l <: i32) |. ((byte1 >>! 4l <: i32) &. 15l <: i32) <: i32)
    }
    <:
    t_PortableVector
  in
  let re:t_PortableVector =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 2)
        (((byte4 &. 15l <: i32) <<! 8l <: i32) |. (byte3 &. 255l <: i32) <: i32)
    }
    <:
    t_PortableVector
  in
  let re:t_PortableVector =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 3)
        ((byte5 <<! 4l <: i32) |. ((byte4 >>! 4l <: i32) &. 15l <: i32) <: i32)
    }
    <:
    t_PortableVector
  in
  let re:t_PortableVector =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 4)
        (((byte7 &. 15l <: i32) <<! 8l <: i32) |. (byte6 &. 255l <: i32) <: i32)
    }
    <:
    t_PortableVector
  in
  let re:t_PortableVector =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 5)
        ((byte8 <<! 4l <: i32) |. ((byte7 >>! 4l <: i32) &. 15l <: i32) <: i32)
    }
    <:
    t_PortableVector
  in
  let re:t_PortableVector =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 6)
        (((byte10 &. 15l <: i32) <<! 8l <: i32) |. (byte9 &. 255l <: i32) <: i32)
    }
    <:
    t_PortableVector
  in
  let re:t_PortableVector =
    {
      re with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re.f_elements
        (sz 7)
        ((byte11 <<! 4l <: i32) |. ((byte10 >>! 4l <: i32) &. 15l <: i32) <: i32)
    }
    <:
    t_PortableVector
  in
  re

let deserialize_4_ (bytes: t_Slice u8) =
  let v:t_PortableVector = Libcrux_ml_kem.Simd.Simd_trait.f_ZERO () in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 0)
        (cast ((bytes.[ sz 0 ] <: u8) &. 15uy <: u8) <: i32)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 1)
        (cast (((bytes.[ sz 0 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i32)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 2)
        (cast ((bytes.[ sz 1 ] <: u8) &. 15uy <: u8) <: i32)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 3)
        (cast (((bytes.[ sz 1 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i32)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 4)
        (cast ((bytes.[ sz 2 ] <: u8) &. 15uy <: u8) <: i32)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 5)
        (cast (((bytes.[ sz 2 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i32)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 6)
        (cast ((bytes.[ sz 3 ] <: u8) &. 15uy <: u8) <: i32)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 7)
        (cast (((bytes.[ sz 3 ] <: u8) >>! 4l <: u8) &. 15uy <: u8) <: i32)
    }
    <:
    t_PortableVector
  in
  v

let deserialize_5_ (bytes: t_Slice u8) =
  let v:t_PortableVector = Libcrux_ml_kem.Simd.Simd_trait.f_ZERO () in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 0)
        (cast ((bytes.[ sz 0 ] <: u8) &. 31uy <: u8) <: i32)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 1)
        (cast ((((bytes.[ sz 1 ] <: u8) &. 3uy <: u8) <<! 3l <: u8) |.
              ((bytes.[ sz 0 ] <: u8) >>! 5l <: u8)
              <:
              u8)
          <:
          i32)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 2)
        (cast (((bytes.[ sz 1 ] <: u8) >>! 2l <: u8) &. 31uy <: u8) <: i32)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 3)
        (cast ((((bytes.[ sz 2 ] <: u8) &. 15uy <: u8) <<! 1l <: u8) |.
              ((bytes.[ sz 1 ] <: u8) >>! 7l <: u8)
              <:
              u8)
          <:
          i32)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 4)
        (cast ((((bytes.[ sz 3 ] <: u8) &. 1uy <: u8) <<! 4l <: u8) |.
              ((bytes.[ sz 2 ] <: u8) >>! 4l <: u8)
              <:
              u8)
          <:
          i32)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 5)
        (cast (((bytes.[ sz 3 ] <: u8) >>! 1l <: u8) &. 31uy <: u8) <: i32)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 6)
        (cast ((((bytes.[ sz 4 ] <: u8) &. 7uy <: u8) <<! 2l <: u8) |.
              ((bytes.[ sz 3 ] <: u8) >>! 6l <: u8)
              <:
              u8)
          <:
          i32)
    }
    <:
    t_PortableVector
  in
  let v:t_PortableVector =
    {
      v with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v.f_elements
        (sz 7)
        (cast ((bytes.[ sz 4 ] <: u8) >>! 3l <: u8) <: i32)
    }
    <:
    t_PortableVector
  in
  v

let ntt_multiply (lhs rhs: t_PortableVector) (zeta0 zeta1: i32) =
  let out:t_PortableVector = Libcrux_ml_kem.Simd.Simd_trait.f_ZERO () in
  let product:(i32 & i32) =
    Libcrux_ml_kem.Arithmetic.ntt_multiply_binomials ((lhs.f_elements.[ sz 0 ] <: i32),
        (lhs.f_elements.[ sz 1 ] <: i32)
        <:
        (i32 & i32))
      ((rhs.f_elements.[ sz 0 ] <: i32), (rhs.f_elements.[ sz 1 ] <: i32) <: (i32 & i32))
      zeta0
  in
  let out:t_PortableVector =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements (sz 0) product._1
    }
    <:
    t_PortableVector
  in
  let out:t_PortableVector =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements (sz 1) product._2
    }
    <:
    t_PortableVector
  in
  let product:(i32 & i32) =
    Libcrux_ml_kem.Arithmetic.ntt_multiply_binomials ((lhs.f_elements.[ sz 2 ] <: i32),
        (lhs.f_elements.[ sz 3 ] <: i32)
        <:
        (i32 & i32))
      ((rhs.f_elements.[ sz 2 ] <: i32), (rhs.f_elements.[ sz 3 ] <: i32) <: (i32 & i32))
      (Core.Ops.Arith.Neg.neg zeta0 <: i32)
  in
  let out:t_PortableVector =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements (sz 2) product._1
    }
    <:
    t_PortableVector
  in
  let out:t_PortableVector =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements (sz 3) product._2
    }
    <:
    t_PortableVector
  in
  let product:(i32 & i32) =
    Libcrux_ml_kem.Arithmetic.ntt_multiply_binomials ((lhs.f_elements.[ sz 4 ] <: i32),
        (lhs.f_elements.[ sz 5 ] <: i32)
        <:
        (i32 & i32))
      ((rhs.f_elements.[ sz 4 ] <: i32), (rhs.f_elements.[ sz 5 ] <: i32) <: (i32 & i32))
      zeta1
  in
  let out:t_PortableVector =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements (sz 4) product._1
    }
    <:
    t_PortableVector
  in
  let out:t_PortableVector =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements (sz 5) product._2
    }
    <:
    t_PortableVector
  in
  let product:(i32 & i32) =
    Libcrux_ml_kem.Arithmetic.ntt_multiply_binomials ((lhs.f_elements.[ sz 6 ] <: i32),
        (lhs.f_elements.[ sz 7 ] <: i32)
        <:
        (i32 & i32))
      ((rhs.f_elements.[ sz 6 ] <: i32), (rhs.f_elements.[ sz 7 ] <: i32) <: (i32 & i32))
      (Core.Ops.Arith.Neg.neg zeta1 <: i32)
  in
  let out:t_PortableVector =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements (sz 6) product._1
    }
    <:
    t_PortableVector
  in
  let out:t_PortableVector =
    {
      out with
      f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements (sz 7) product._2
    }
    <:
    t_PortableVector
  in
  out
