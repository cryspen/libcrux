module Libcrux_ml_kem.Vector.Portable.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let ntt_multiply_binomials (a0, a1: (i16 & i16)) (b0, b1: (i16 & i16)) (zeta: i16) =
  Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_reduce_element (((cast (a0 <: i16) <: i32) *!
        (cast (b0 <: i16) <: i32)
        <:
        i32) +!
      ((cast (Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_reduce_element ((cast (a1 <: i16)
                    <:
                    i32) *!
                  (cast (b1 <: i16) <: i32)
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
  Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_reduce_element (((cast (a0 <: i16) <: i32) *!
        (cast (b1 <: i16) <: i32)
        <:
        i32) +!
      ((cast (a1 <: i16) <: i32) *! (cast (b0 <: i16) <: i32) <: i32)
      <:
      i32)
  <:
  (i16 & i16)

let inv_ntt_layer_1_step
      (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta0 zeta1 zeta2 zeta3: i16)
     =
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 2 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 0 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 0)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.barrett_reduce_element ((v
                  .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 0 ]
                <:
                i16) +!
              (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 2 ] <: i16)
              <:
              i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 2)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta0
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 3 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 1 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 1)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.barrett_reduce_element ((v
                  .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 1 ]
                <:
                i16) +!
              (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 3 ] <: i16)
              <:
              i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 3)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta0
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 6 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 4 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 4)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.barrett_reduce_element ((v
                  .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 4 ]
                <:
                i16) +!
              (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 6 ] <: i16)
              <:
              i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 6)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta1
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 7 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 5 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 5)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.barrett_reduce_element ((v
                  .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 5 ]
                <:
                i16) +!
              (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 7 ] <: i16)
              <:
              i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 7)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta1
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 0 <: usize)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.barrett_reduce_element ((v
                  .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 0 <: usize ]
                <:
                i16) +!
              (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 2 <: usize ]
                <:
                i16)
              <:
              i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 2 <: usize)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta2
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 1 <: usize)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.barrett_reduce_element ((v
                  .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 1 <: usize ]
                <:
                i16) +!
              (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 3 <: usize ]
                <:
                i16)
              <:
              i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 3 <: usize)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta2
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 4 <: usize)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.barrett_reduce_element ((v
                  .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 4 <: usize ]
                <:
                i16) +!
              (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 6 <: usize ]
                <:
                i16)
              <:
              i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 6 <: usize)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta3
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 5 <: usize)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.barrett_reduce_element ((v
                  .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 5 <: usize ]
                <:
                i16) +!
              (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 7 <: usize ]
                <:
                i16)
              <:
              i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 7 <: usize)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta3
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  v

let inv_ntt_layer_2_step
      (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta0 zeta1: i16)
     =
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 4 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 0 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 0)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 0 ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 4 ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 4)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta0
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 5 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 1 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 1)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 1 ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 5 ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 5)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta0
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 6 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 2 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 2)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 2 ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 6 ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 6)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta0
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 7 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 3 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 3)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 3 ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 7 ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 7)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta0
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 0 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 4 <: usize)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta1
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 1 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 5 <: usize)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta1
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 2 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 6 <: usize)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta1
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 3 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 7 <: usize)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta1
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  v

let inv_ntt_layer_3_step
      (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta: i16)
     =
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 0 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 0)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 0 ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 9 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 1 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 1)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 1 ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 9 ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 9)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 10 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 2 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 2)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 2 ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 10 ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 10)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 11 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 3 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 3)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 3 ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 11 ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 11)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 12 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 4 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 4)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 4 ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 12 ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 12)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 13 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 5 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 5)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 5 ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 13 ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 13)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 14 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 6 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 6)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 6 ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 14 ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 14)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 15 ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 7 ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 7)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 7 ] <: i16) +!
          (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 15 ] <: i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 15)
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  v

let ntt_layer_1_step
      (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta0 zeta1 zeta2 zeta3: i16)
     =
  let t:i16 =
    Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer (v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 2 ]
        <:
        i16)
      zeta0
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 2)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 0 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 0)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 0 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let t:i16 =
    Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer (v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 3 ]
        <:
        i16)
      zeta0
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 3)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 1 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 1)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 1 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let t:i16 =
    Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer (v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 6 ]
        <:
        i16)
      zeta1
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 6)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 4 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 4)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 4 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let t:i16 =
    Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer (v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 7 ]
        <:
        i16)
      zeta1
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 7)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 5 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 5)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 5 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let t:i16 =
    Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer (v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 2 <: usize ]
        <:
        i16)
      zeta2
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 2 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) -!
          t
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 0 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) +!
          t
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let t:i16 =
    Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer (v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 3 <: usize ]
        <:
        i16)
      zeta2
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 3 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) -!
          t
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 1 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) +!
          t
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let t:i16 =
    Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer (v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 6 <: usize ]
        <:
        i16)
      zeta3
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 6 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) -!
          t
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 4 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16) +!
          t
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let t:i16 =
    Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer (v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 7 <: usize ]
        <:
        i16)
      zeta3
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 7 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) -!
          t
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 5 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16) +!
          t
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  v

let ntt_layer_2_step
      (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta0 zeta1: i16)
     =
  let t:i16 =
    Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer (v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 4 ]
        <:
        i16)
      zeta0
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 4)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 0 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 0)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 0 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let t:i16 =
    Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer (v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 5 ]
        <:
        i16)
      zeta0
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 5)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 1 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 1)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 1 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let t:i16 =
    Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer (v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 6 ]
        <:
        i16)
      zeta0
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 6)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 2 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 2)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 2 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let t:i16 =
    Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer (v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 7 ]
        <:
        i16)
      zeta0
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 7)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 3 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 3)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 3 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let t:i16 =
    Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer (v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 4 <: usize ]
        <:
        i16)
      zeta1
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 4 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) -!
          t
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 0 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16) +!
          t
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let t:i16 =
    Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer (v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 5 <: usize ]
        <:
        i16)
      zeta1
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 5 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) -!
          t
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 1 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16) +!
          t
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let t:i16 =
    Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer (v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 6 <: usize ]
        <:
        i16)
      zeta1
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 6 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) -!
          t
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 2 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16) +!
          t
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let t:i16 =
    Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer (v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 7 <: usize ]
        <:
        i16)
      zeta1
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 7 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) -!
          t
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 3 <: usize)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16) +!
          t
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  v

let ntt_layer_3_step (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (zeta: i16) =
  let t:i16 =
    Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer (v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 ]
        <:
        i16)
      zeta
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 0 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 0)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 0 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let t:i16 =
    Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer (v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 9 ]
        <:
        i16)
      zeta
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 9)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 1 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 1)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 1 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let t:i16 =
    Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer (v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 10 ]
        <:
        i16)
      zeta
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 10)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 2 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 2)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 2 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let t:i16 =
    Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer (v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 11 ]
        <:
        i16)
      zeta
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 11)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 3 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 3)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 3 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let t:i16 =
    Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer (v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 12 ]
        <:
        i16)
      zeta
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 12)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 4 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 4)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 4 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let t:i16 =
    Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer (v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 13 ]
        <:
        i16)
      zeta
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 13)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 5 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 5)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 5 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let t:i16 =
    Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer (v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 14 ]
        <:
        i16)
      zeta
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 14)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 6 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 6)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 6 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let t:i16 =
    Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer (v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 15 ]
        <:
        i16)
      zeta
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 15)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 7 ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 7)
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 7 ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  v

let ntt_multiply
      (lhs rhs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta0 zeta1 zeta2 zeta3: i16)
     =
  let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Libcrux_ml_kem.Vector.Portable.Vector_type.zero ()
  in
  let product:(i16 & i16) =
    ntt_multiply_binomials ((lhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 0 ]
          <:
          i16),
        (lhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 1 ] <: i16)
        <:
        (i16 & i16))
      ((rhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 0 ] <: i16),
        (rhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 1 ] <: i16)
        <:
        (i16 & i16))
      zeta0
  in
  let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 0)
        product._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 1)
        product._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let product:(i16 & i16) =
    ntt_multiply_binomials ((lhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 2 ]
          <:
          i16),
        (lhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 3 ] <: i16)
        <:
        (i16 & i16))
      ((rhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 2 ] <: i16),
        (rhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 3 ] <: i16)
        <:
        (i16 & i16))
      (Core.Ops.Arith.Neg.neg zeta0 <: i16)
  in
  let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 2)
        product._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 3)
        product._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let product:(i16 & i16) =
    ntt_multiply_binomials ((lhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 4 ]
          <:
          i16),
        (lhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 5 ] <: i16)
        <:
        (i16 & i16))
      ((rhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 4 ] <: i16),
        (rhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 5 ] <: i16)
        <:
        (i16 & i16))
      zeta1
  in
  let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 4)
        product._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 5)
        product._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let product:(i16 & i16) =
    ntt_multiply_binomials ((lhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 6 ]
          <:
          i16),
        (lhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 7 ] <: i16)
        <:
        (i16 & i16))
      ((rhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 6 ] <: i16),
        (rhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 7 ] <: i16)
        <:
        (i16 & i16))
      (Core.Ops.Arith.Neg.neg zeta1 <: i16)
  in
  let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 6)
        product._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 7)
        product._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let product:(i16 & i16) =
    ntt_multiply_binomials ((lhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +!
            sz 0
            <:
            usize ]
          <:
          i16),
        (lhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16)
        <:
        (i16 & i16))
      ((rhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 0 <: usize ] <: i16),
        (rhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 1 <: usize ] <: i16)
        <:
        (i16 & i16))
      zeta2
  in
  let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 0 <: usize)
        product._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 1 <: usize)
        product._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let product:(i16 & i16) =
    ntt_multiply_binomials ((lhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +!
            sz 2
            <:
            usize ]
          <:
          i16),
        (lhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16)
        <:
        (i16 & i16))
      ((rhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 2 <: usize ] <: i16),
        (rhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 3 <: usize ] <: i16)
        <:
        (i16 & i16))
      (Core.Ops.Arith.Neg.neg zeta2 <: i16)
  in
  let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 2 <: usize)
        product._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 3 <: usize)
        product._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let product:(i16 & i16) =
    ntt_multiply_binomials ((lhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +!
            sz 4
            <:
            usize ]
          <:
          i16),
        (lhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16)
        <:
        (i16 & i16))
      ((rhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 4 <: usize ] <: i16),
        (rhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 5 <: usize ] <: i16)
        <:
        (i16 & i16))
      zeta3
  in
  let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 4 <: usize)
        product._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 5 <: usize)
        product._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let product:(i16 & i16) =
    ntt_multiply_binomials ((lhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +!
            sz 6
            <:
            usize ]
          <:
          i16),
        (lhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16)
        <:
        (i16 & i16))
      ((rhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 6 <: usize ] <: i16),
        (rhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ sz 8 +! sz 7 <: usize ] <: i16)
        <:
        (i16 & i16))
      (Core.Ops.Arith.Neg.neg zeta3 <: i16)
  in
  let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 6 <: usize)
        product._1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        (sz 8 +! sz 7 <: usize)
        product._2
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  out
