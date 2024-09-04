module Libcrux_ml_kem.Vector.Portable.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let inv_ntt_step
      (vec: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta: i16)
      (i j: usize)
     =
  let a_minus_b:i16 =
    (vec.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ j ] <: i16) -!
    (vec.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      vec with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize vec
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        i
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.barrett_reduce_element ((vec
                  .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ]
                <:
                i16) +!
              (vec.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ j ] <: i16)
              <:
              i16)
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      vec with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize vec
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        j
        (Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer a_minus_b zeta
          <:
          i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  vec

let inv_ntt_layer_1_step
      (vec: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta0 zeta1 zeta2 zeta3: i16)
     =
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta0 (sz 0) (sz 2)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta0 (sz 1) (sz 3)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta1 (sz 4) (sz 6)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta1 (sz 5) (sz 7)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta2 (sz 8) (sz 10)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta2 (sz 9) (sz 11)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta3 (sz 12) (sz 14)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta3 (sz 13) (sz 15)
  in
  vec

let inv_ntt_layer_2_step
      (vec: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta0 zeta1: i16)
     =
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta0 (sz 0) (sz 4)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta0 (sz 1) (sz 5)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta0 (sz 2) (sz 6)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta0 (sz 3) (sz 7)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta1 (sz 8) (sz 12)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta1 (sz 9) (sz 13)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta1 (sz 10) (sz 14)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta1 (sz 11) (sz 15)
  in
  vec

let inv_ntt_layer_3_step
      (vec: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta: i16)
     =
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta (sz 0) (sz 8)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta (sz 1) (sz 9)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta (sz 2) (sz 10)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta (sz 3) (sz 11)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta (sz 4) (sz 12)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta (sz 5) (sz 13)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta (sz 6) (sz 14)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    inv_ntt_step vec zeta (sz 7) (sz 15)
  in
  vec

let ntt_multiply_binomials
      (a b: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta: i16)
      (i j: usize)
      (out: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
     =
  let _:Prims.unit =
    Spec.Utils.lemma_mul_i16b 3328
      3328
      (Seq.index (a.f_elements) (v i))
      (Seq.index (b.f_elements) (v i))
  in
  let _:Prims.unit =
    Spec.Utils.lemma_mul_i16b 3328
      3328
      (Seq.index (a.f_elements) (v j))
      (Seq.index (b.f_elements) (v j))
  in
  let ai_bi:i32 =
    (cast (a.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16) <: i32) *!
    (cast (b.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16) <: i32)
  in
  let aj_bj:i16 =
    Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_reduce_element ((cast (a
                .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ j ]
              <:
              i16)
          <:
          i32) *!
        (cast (b.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ j ] <: i16) <: i32)
        <:
        i32)
  in
  let _:Prims.unit = Spec.Utils.lemma_mul_i16b 3328 1664 aj_bj zeta in
  let o0:i16 =
    Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_reduce_element (ai_bi +!
        ((cast (aj_bj <: i16) <: i32) *! (cast (zeta <: i16) <: i32) <: i32)
        <:
        i32)
  in
  let _:Prims.unit =
    Spec.Utils.lemma_mul_i16b 3328
      3328
      (Seq.index (a.f_elements) (v i))
      (Seq.index (b.f_elements) (v j))
  in
  let _:Prims.unit =
    Spec.Utils.lemma_mul_i16b 3328
      3328
      (Seq.index (a.f_elements) (v j))
      (Seq.index (b.f_elements) (v i))
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
      (vec: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta: i16)
      (i j: usize)
     =
  let t:i16 =
    Libcrux_ml_kem.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer (vec
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ j ]
        <:
        i16)
      zeta
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      vec with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize vec
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        j
        ((vec.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16) -! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    {
      vec with
      Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize vec
          .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
        i
        ((vec.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16) +! t <: i16)
    }
    <:
    Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
  in
  vec

let ntt_layer_1_step
      (vec: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta0 zeta1 zeta2 zeta3: i16)
     =
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta0 (sz 0) (sz 2)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta0 (sz 1) (sz 3)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta1 (sz 4) (sz 6)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta1 (sz 5) (sz 7)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta2 (sz 8) (sz 10)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta2 (sz 9) (sz 11)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta3 (sz 12) (sz 14)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta3 (sz 13) (sz 15)
  in
  vec

let ntt_layer_2_step
      (vec: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta0 zeta1: i16)
     =
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta0 (sz 0) (sz 4)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta0 (sz 1) (sz 5)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta0 (sz 2) (sz 6)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta0 (sz 3) (sz 7)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta1 (sz 8) (sz 12)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta1 (sz 9) (sz 13)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta1 (sz 10) (sz 14)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta1 (sz 11) (sz 15)
  in
  vec

let ntt_layer_3_step (vec: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (zeta: i16) =
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta (sz 0) (sz 8)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta (sz 1) (sz 9)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta (sz 2) (sz 10)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta (sz 3) (sz 11)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta (sz 4) (sz 12)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta (sz 5) (sz 13)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta (sz 6) (sz 14)
  in
  let vec:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    ntt_step vec zeta (sz 7) (sz 15)
  in
  vec

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
