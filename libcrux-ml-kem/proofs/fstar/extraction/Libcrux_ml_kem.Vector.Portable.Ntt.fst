module Libcrux_ml_kem.Vector.Portable.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let inv_ntt_step
      (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta: i16)
      (i j: usize)
     =
  let a_minus_b:i16 =
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ j ] <: i16) -!
    (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      v with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        i
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.barrett_reduce_element ((v
                  .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ]
                <:
                i16) +!
              (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ j ] <: i16)
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
        j
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  v

let inv_ntt_layer_1_step
      (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta0 zeta1 zeta2 zeta3: i16)
     =
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step v zeta0 (sz 0) (sz 2)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step v zeta0 (sz 1) (sz 3)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step v zeta1 (sz 4) (sz 6)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step v zeta1 (sz 5) (sz 7)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step v zeta2 (sz 8) (sz 10)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step v zeta2 (sz 9) (sz 11)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step v zeta3 (sz 12) (sz 14)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step v zeta3 (sz 13) (sz 15)
  in
  v

let inv_ntt_layer_2_step
      (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta0 zeta1: i16)
     =
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step v zeta0 (sz 0) (sz 4)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step v zeta0 (sz 1) (sz 5)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step v zeta0 (sz 2) (sz 6)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step v zeta0 (sz 3) (sz 7)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step v zeta1 (sz 8) (sz 12)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step v zeta1 (sz 9) (sz 13)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step v zeta1 (sz 10) (sz 14)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step v zeta1 (sz 11) (sz 15)
  in
  v

let inv_ntt_layer_3_step
      (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta: i16)
     =
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step v zeta (sz 0) (sz 8)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step v zeta (sz 1) (sz 9)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step v zeta (sz 2) (sz 10)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step v zeta (sz 3) (sz 11)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step v zeta (sz 4) (sz 12)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step v zeta (sz 5) (sz 13)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step v zeta (sz 6) (sz 14)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step v zeta (sz 7) (sz 15)
  in
  v

let ntt_multiply_binomials
      (a b: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta: i16)
      (i j: usize)
      (out: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
     =
  let o0:i16 =
    Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_reduce_element (((cast (a
                  .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ]
                <:
                i16)
            <:
            i32) *!
          (cast (b.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16) <: i32)
          <:
          i32) +!
        ((cast (Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_reduce_element ((cast (a
                            .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ j ]
                          <:
                          i16)
                      <:
                      i32) *!
                    (cast (b.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ j ] <: i16)
                      <:
                      i32)
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
        i32)
  in
  let o1:i16 =
    Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_reduce_element (((cast (a
                  .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ]
                <:
                i16)
            <:
            i32) *!
          (cast (b.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ j ] <: i16) <: i32)
          <:
          i32) +!
        ((cast (a.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ j ] <: i16) <: i32) *!
          (cast (b.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16) <: i32)
          <:
          i32)
        <:
        i32)
  in
  let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      out with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        i
        o0
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
        j
        o1
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  out

let ntt_step
      (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta: i16)
      (i j: usize)
     =
  let t:i16 =
    Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer (v
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ j ]
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
        j
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16) -! t <: i16)
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
        i
        ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  v

let ntt_layer_1_step
      (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta0 zeta1 zeta2 zeta3: i16)
     =
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step v zeta0 (sz 0) (sz 2)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step v zeta0 (sz 1) (sz 3)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step v zeta1 (sz 4) (sz 6)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step v zeta1 (sz 5) (sz 7)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step v zeta2 (sz 8) (sz 10)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step v zeta2 (sz 9) (sz 11)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step v zeta3 (sz 12) (sz 14)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step v zeta3 (sz 13) (sz 15)
  in
  v

let ntt_layer_2_step
      (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta0 zeta1: i16)
     =
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step v zeta0 (sz 0) (sz 4)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step v zeta0 (sz 1) (sz 5)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step v zeta0 (sz 2) (sz 6)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step v zeta0 (sz 3) (sz 7)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step v zeta1 (sz 8) (sz 12)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step v zeta1 (sz 9) (sz 13)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step v zeta1 (sz 10) (sz 14)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step v zeta1 (sz 11) (sz 15)
  in
  v

let ntt_layer_3_step (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (zeta: i16) =
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step v zeta (sz 0) (sz 8)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step v zeta (sz 1) (sz 9)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step v zeta (sz 2) (sz 10)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step v zeta (sz 3) (sz 11)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step v zeta (sz 4) (sz 12)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step v zeta (sz 5) (sz 13)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step v zeta (sz 6) (sz 14)
  in
  let v:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step v zeta (sz 7) (sz 15)
  in
  v

let ntt_multiply
      (lhs rhs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta0 zeta1 zeta2 zeta3: i16)
     =
  let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Libcrux_ml_kem.Vector.Portable.Vector_type.zero ()
  in
  let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_multiply_binomials lhs rhs zeta0 (sz 0) (sz 1) out
  in
  let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_multiply_binomials lhs rhs (Core.Ops.Arith.Neg.neg zeta0 <: i16) (sz 2) (sz 3) out
  in
  let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_multiply_binomials lhs rhs zeta1 (sz 4) (sz 5) out
  in
  let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_multiply_binomials lhs rhs (Core.Ops.Arith.Neg.neg zeta1 <: i16) (sz 6) (sz 7) out
  in
  let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_multiply_binomials lhs rhs zeta2 (sz 8) (sz 9) out
  in
  let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_multiply_binomials lhs rhs (Core.Ops.Arith.Neg.neg zeta2 <: i16) (sz 10) (sz 11) out
  in
  let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_multiply_binomials lhs rhs zeta3 (sz 12) (sz 13) out
  in
  let out:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_multiply_binomials lhs rhs (Core.Ops.Arith.Neg.neg zeta3 <: i16) (sz 14) (sz 15) out
  in
  out
