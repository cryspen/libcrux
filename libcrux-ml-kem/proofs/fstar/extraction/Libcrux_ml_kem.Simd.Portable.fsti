module Libcrux_ml_kem.Simd.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_PortableVector = { f_elements:t_Array i32 (sz 8) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Libcrux_ml_kem.Simd.Simd_trait.t_ArrayOperations t_PortableVector =
  {
    f_ZERO_pre = (fun (_: Prims.unit) -> true);
    f_ZERO_post = (fun (_: Prims.unit) (out: t_PortableVector) -> true);
    f_ZERO
    =
    (fun (_: Prims.unit) ->
        { f_elements = Rust_primitives.Hax.repeat 0l (sz 8) } <: t_PortableVector);
    f_to_i32_array_pre = (fun (v: t_PortableVector) -> true);
    f_to_i32_array_post = (fun (v: t_PortableVector) (out: t_Array i32 (sz 8)) -> true);
    f_to_i32_array = (fun (v: t_PortableVector) -> v.f_elements);
    f_from_i32_array_pre = (fun (array: t_Array i32 (sz 8)) -> true);
    f_from_i32_array_post = (fun (array: t_Array i32 (sz 8)) (out: t_PortableVector) -> true);
    f_from_i32_array = fun (array: t_Array i32 (sz 8)) -> { f_elements = array } <: t_PortableVector
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Libcrux_ml_kem.Simd.Simd_trait.t_ArithmeticOperations t_PortableVector =
  {
    f_add_constant_pre = (fun (v: t_PortableVector) (c: i32) -> true);
    f_add_constant_post = (fun (v: t_PortableVector) (c: i32) (out: t_PortableVector) -> true);
    f_add_constant
    =
    (fun (v: t_PortableVector) (c: i32) ->
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
        v);
    f_add_pre = (fun (lhs: t_PortableVector) (rhs: t_PortableVector) -> true);
    f_add_post
    =
    (fun (lhs: t_PortableVector) (rhs: t_PortableVector) (out: t_PortableVector) -> true);
    f_add
    =
    (fun (lhs: t_PortableVector) (rhs: t_PortableVector) ->
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
        lhs);
    f_sub_pre = (fun (lhs: t_PortableVector) (rhs: t_PortableVector) -> true);
    f_sub_post
    =
    (fun (lhs: t_PortableVector) (rhs: t_PortableVector) (out: t_PortableVector) -> true);
    f_sub
    =
    (fun (lhs: t_PortableVector) (rhs: t_PortableVector) ->
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
        lhs);
    f_multiply_by_constant_pre = (fun (v: t_PortableVector) (c: i32) -> true);
    f_multiply_by_constant_post
    =
    (fun (v: t_PortableVector) (c: i32) (out: t_PortableVector) -> true);
    f_multiply_by_constant
    =
    fun (v: t_PortableVector) (c: i32) ->
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
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Libcrux_ml_kem.Simd.Simd_trait.t_BitwiseOperations t_PortableVector =
  {
    f_bitwise_and_with_constant_pre = (fun (v: t_PortableVector) (c: i32) -> true);
    f_bitwise_and_with_constant_post
    =
    (fun (v: t_PortableVector) (c: i32) (out: t_PortableVector) -> true);
    f_bitwise_and_with_constant
    =
    (fun (v: t_PortableVector) (c: i32) ->
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
        v);
    f_shift_right_pre = (fun (v: t_PortableVector) (shift_amount: u8) -> true);
    f_shift_right_post
    =
    (fun (v: t_PortableVector) (shift_amount: u8) (out: t_PortableVector) -> true);
    f_shift_right
    =
    (fun (v: t_PortableVector) (shift_amount: u8) ->
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
                    ((v.f_elements.[ i ] <: i32) >>! shift_amount <: i32)
                  <:
                  t_Array i32 (sz 8)
                }
                <:
                t_PortableVector)
        in
        v);
    f_shift_left_pre = (fun (lhs: t_PortableVector) (shift_amount: u8) -> true);
    f_shift_left_post
    =
    (fun (lhs: t_PortableVector) (shift_amount: u8) (out: t_PortableVector) -> true);
    f_shift_left
    =
    fun (lhs: t_PortableVector) (shift_amount: u8) ->
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
                  ((lhs.f_elements.[ i ] <: i32) <<! shift_amount <: i32)
                <:
                t_Array i32 (sz 8)
              }
              <:
              t_PortableVector)
      in
      lhs
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Libcrux_ml_kem.Simd.Simd_trait.t_ModularOperations t_PortableVector =
  {
    f_modulo_a_constant_pre = (fun (v: t_PortableVector) (modulus: i32) -> true);
    f_modulo_a_constant_post
    =
    (fun (v: t_PortableVector) (modulus: i32) (out: t_PortableVector) -> true);
    f_modulo_a_constant
    =
    (fun (v: t_PortableVector) (modulus: i32) ->
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
                    ((v.f_elements.[ i ] <: i32) %! modulus <: i32)
                  <:
                  t_Array i32 (sz 8)
                }
                <:
                t_PortableVector)
        in
        v);
    f_barrett_reduce_pre = (fun (v: t_PortableVector) -> true);
    f_barrett_reduce_post = (fun (v: t_PortableVector) (out: t_PortableVector) -> true);
    f_barrett_reduce
    =
    (fun (v: t_PortableVector) ->
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
        v);
    f_montgomery_reduce_pre = (fun (v: t_PortableVector) -> true);
    f_montgomery_reduce_post = (fun (v: t_PortableVector) (out: t_PortableVector) -> true);
    f_montgomery_reduce
    =
    fun (v: t_PortableVector) ->
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
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: Libcrux_ml_kem.Simd.Simd_trait.t_CompressionOperations t_PortableVector =
  {
    f_compress_1_pre = (fun (v: t_PortableVector) -> true);
    f_compress_1_post = (fun (v: t_PortableVector) (out: t_PortableVector) -> true);
    f_compress_1_
    =
    (fun (v: t_PortableVector) ->
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
                    (cast (Libcrux_ml_kem.Compress.compress_message_coefficient (cast (v.f_elements.[
                                    i ]
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
        v);
    f_compress_pre = (fun (coefficient_bits: u8) (v: t_PortableVector) -> true);
    f_compress_post
    =
    (fun (coefficient_bits: u8) (v: t_PortableVector) (out: t_PortableVector) -> true);
    f_compress
    =
    fun (coefficient_bits: u8) (v: t_PortableVector) ->
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
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: Libcrux_ml_kem.Simd.Simd_trait.t_NTTOperations t_PortableVector =
  {
    f_ntt_layer_1_step_pre = (fun (v: t_PortableVector) (zeta1: i32) (zeta2: i32) -> true);
    f_ntt_layer_1_step_post
    =
    (fun (v: t_PortableVector) (zeta1: i32) (zeta2: i32) (out: t_PortableVector) -> true);
    f_ntt_layer_1_step
    =
    (fun (v: t_PortableVector) (zeta1: i32) (zeta2: i32) ->
        let t:i32 =
          Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer (v.f_elements.[ sz 2 ] <: i32)
            zeta1
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
          Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer (v.f_elements.[ sz 3 ] <: i32)
            zeta1
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
          Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer (v.f_elements.[ sz 6 ] <: i32)
            zeta2
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
          Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer (v.f_elements.[ sz 7 ] <: i32)
            zeta2
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
        v);
    f_ntt_layer_2_step_pre = (fun (v: t_PortableVector) (zeta: i32) -> true);
    f_ntt_layer_2_step_post
    =
    (fun (v: t_PortableVector) (zeta: i32) (out: t_PortableVector) -> true);
    f_ntt_layer_2_step
    =
    (fun (v: t_PortableVector) (zeta: i32) ->
        let t:i32 =
          Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer (v.f_elements.[ sz 4 ] <: i32)
            zeta
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
          Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer (v.f_elements.[ sz 5 ] <: i32)
            zeta
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
          Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer (v.f_elements.[ sz 6 ] <: i32)
            zeta
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
          Libcrux_ml_kem.Arithmetic.montgomery_multiply_fe_by_fer (v.f_elements.[ sz 7 ] <: i32)
            zeta
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
        v);
    f_inv_ntt_layer_1_step_pre = (fun (v: t_PortableVector) (zeta1: i32) (zeta2: i32) -> true);
    f_inv_ntt_layer_1_step_post
    =
    (fun (v: t_PortableVector) (zeta1: i32) (zeta2: i32) (out: t_PortableVector) -> true);
    f_inv_ntt_layer_1_step
    =
    (fun (v: t_PortableVector) (zeta1: i32) (zeta2: i32) ->
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
        v);
    f_inv_ntt_layer_2_step_pre = (fun (v: t_PortableVector) (zeta: i32) -> true);
    f_inv_ntt_layer_2_step_post
    =
    (fun (v: t_PortableVector) (zeta: i32) (out: t_PortableVector) -> true);
    f_inv_ntt_layer_2_step
    =
    (fun (v: t_PortableVector) (zeta: i32) ->
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
        v);
    f_ntt_multiply_pre
    =
    (fun (lhs: t_PortableVector) (rhs: t_PortableVector) (zeta0: i32) (zeta1: i32) -> true);
    f_ntt_multiply_post
    =
    (fun
        (lhs: t_PortableVector)
        (rhs: t_PortableVector)
        (zeta0: i32)
        (zeta1: i32)
        (out1: t_PortableVector)
        ->
        true);
    f_ntt_multiply
    =
    fun (lhs: t_PortableVector) (rhs: t_PortableVector) (zeta0: i32) (zeta1: i32) ->
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
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements
            (sz 0)
            product._1
        }
        <:
        t_PortableVector
      in
      let out:t_PortableVector =
        {
          out with
          f_elements
          =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements
            (sz 1)
            product._2
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
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements
            (sz 2)
            product._1
        }
        <:
        t_PortableVector
      in
      let out:t_PortableVector =
        {
          out with
          f_elements
          =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements
            (sz 3)
            product._2
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
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements
            (sz 4)
            product._1
        }
        <:
        t_PortableVector
      in
      let out:t_PortableVector =
        {
          out with
          f_elements
          =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements
            (sz 5)
            product._2
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
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements
            (sz 6)
            product._1
        }
        <:
        t_PortableVector
      in
      let out:t_PortableVector =
        {
          out with
          f_elements
          =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out.f_elements
            (sz 7)
            product._2
        }
        <:
        t_PortableVector
      in
      out
  }

val deserialize_10___ (bytes: t_Slice u8)
    : Prims.Pure t_PortableVector Prims.l_True (fun _ -> Prims.l_True)

val deserialize_11___ (bytes: t_Slice u8)
    : Prims.Pure t_PortableVector Prims.l_True (fun _ -> Prims.l_True)

val deserialize_12___ (bytes: t_Slice u8)
    : Prims.Pure t_PortableVector Prims.l_True (fun _ -> Prims.l_True)

val deserialize_1___ (v: u8) : Prims.Pure t_PortableVector Prims.l_True (fun _ -> Prims.l_True)

val deserialize_4___ (bytes: t_Slice u8)
    : Prims.Pure t_PortableVector Prims.l_True (fun _ -> Prims.l_True)

val deserialize_5___ (bytes: t_Slice u8)
    : Prims.Pure t_PortableVector Prims.l_True (fun _ -> Prims.l_True)

val serialize_10___ (v: t_PortableVector)
    : Prims.Pure (t_Array u8 (sz 10)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_11___ (v: t_PortableVector)
    : Prims.Pure (t_Array u8 (sz 11)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_12___ (v: t_PortableVector)
    : Prims.Pure (t_Array u8 (sz 12)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_1___ (v: t_PortableVector) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val serialize_4___ (v: t_PortableVector)
    : Prims.Pure (t_Array u8 (sz 4)) Prims.l_True (fun _ -> Prims.l_True)

val serialize_5___ (v: t_PortableVector)
    : Prims.Pure (t_Array u8 (sz 5)) Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: Libcrux_ml_kem.Simd.Simd_trait.t_SerializeOperations t_PortableVector =
  {
    f_serialize_1_pre = (fun (a: t_PortableVector) -> true);
    f_serialize_1_post = (fun (a: t_PortableVector) (out: u8) -> true);
    f_serialize_1_ = (fun (a: t_PortableVector) -> serialize_1___ a);
    f_deserialize_1_pre = (fun (a: u8) -> true);
    f_deserialize_1_post = (fun (a: u8) (out: t_PortableVector) -> true);
    f_deserialize_1_ = (fun (a: u8) -> deserialize_1___ a);
    f_serialize_4_pre = (fun (a: t_PortableVector) -> true);
    f_serialize_4_post = (fun (a: t_PortableVector) (out: t_Array u8 (sz 4)) -> true);
    f_serialize_4_ = (fun (a: t_PortableVector) -> serialize_4___ a);
    f_deserialize_4_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_4_post = (fun (a: t_Slice u8) (out: t_PortableVector) -> true);
    f_deserialize_4_ = (fun (a: t_Slice u8) -> deserialize_4___ a);
    f_serialize_5_pre = (fun (a: t_PortableVector) -> true);
    f_serialize_5_post = (fun (a: t_PortableVector) (out: t_Array u8 (sz 5)) -> true);
    f_serialize_5_ = (fun (a: t_PortableVector) -> serialize_5___ a);
    f_deserialize_5_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_5_post = (fun (a: t_Slice u8) (out: t_PortableVector) -> true);
    f_deserialize_5_ = (fun (a: t_Slice u8) -> deserialize_5___ a);
    f_serialize_10_pre = (fun (a: t_PortableVector) -> true);
    f_serialize_10_post = (fun (a: t_PortableVector) (out: t_Array u8 (sz 10)) -> true);
    f_serialize_10_ = (fun (a: t_PortableVector) -> serialize_10___ a);
    f_deserialize_10_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_10_post = (fun (a: t_Slice u8) (out: t_PortableVector) -> true);
    f_deserialize_10_ = (fun (a: t_Slice u8) -> deserialize_10___ a);
    f_serialize_11_pre = (fun (a: t_PortableVector) -> true);
    f_serialize_11_post = (fun (a: t_PortableVector) (out: t_Array u8 (sz 11)) -> true);
    f_serialize_11_ = (fun (a: t_PortableVector) -> serialize_11___ a);
    f_deserialize_11_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_11_post = (fun (a: t_Slice u8) (out: t_PortableVector) -> true);
    f_deserialize_11_ = (fun (a: t_Slice u8) -> deserialize_11___ a);
    f_serialize_12_pre = (fun (a: t_PortableVector) -> true);
    f_serialize_12_post = (fun (a: t_PortableVector) (out: t_Array u8 (sz 12)) -> true);
    f_serialize_12_ = (fun (a: t_PortableVector) -> serialize_12___ a);
    f_deserialize_12_pre = (fun (a: t_Slice u8) -> true);
    f_deserialize_12_post = (fun (a: t_Slice u8) (out: t_PortableVector) -> true);
    f_deserialize_12_ = fun (a: t_Slice u8) -> deserialize_12___ a
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7: Libcrux_ml_kem.Simd.Simd_trait.t_Operations t_PortableVector =
  {
    _super_16550665238208597986 = FStar.Tactics.Typeclasses.solve;
    _super_9181983936900423582 = FStar.Tactics.Typeclasses.solve;
    _super_11057338832248834886 = FStar.Tactics.Typeclasses.solve;
    _super_5739476159407468282 = FStar.Tactics.Typeclasses.solve;
    _super_13298396156660513588 = FStar.Tactics.Typeclasses.solve;
    _super_1988623142765322925 = FStar.Tactics.Typeclasses.solve;
    _super_18188678553863793517 = FStar.Tactics.Typeclasses.solve;
    _super_957087622381469234 = FStar.Tactics.Typeclasses.solve;
    _super_2101570567305961368 = FStar.Tactics.Typeclasses.solve;
    __marker_trait = ()
  }
