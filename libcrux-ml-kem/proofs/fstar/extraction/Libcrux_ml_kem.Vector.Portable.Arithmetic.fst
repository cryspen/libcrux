module Libcrux_ml_kem.Vector.Portable.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let get_n_least_significant_bits (n: u8) (value: u32) = value &. ((1ul <<! n <: u32) -! 1ul <: u32)

let barrett_reduce_element (value: i16) =
  let t:i32 =
    ((Core.Convert.f_from #i32 #i16 #FStar.Tactics.Typeclasses.solve value <: i32) *!
      v_BARRETT_MULTIPLIER
      <:
      i32) +!
    (v_BARRETT_R >>! 1l <: i32)
  in
  let quotient:i16 = cast (t >>! v_BARRETT_SHIFT <: i32) <: i16 in
  value -! (quotient *! Libcrux_ml_kem.Vector.Traits.v_FIELD_MODULUS <: i16)

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

let add (lhs rhs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let lhs:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
      (fun lhs temp_1_ ->
          let lhs:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = lhs in
          let _:usize = temp_1_ in
          true)
      lhs
      (fun lhs i ->
          let lhs:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = lhs in
          let i:usize = i in
          {
            lhs with
            Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs
                .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
              i
              ((lhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16) +!
                (rhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16)
                <:
                i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
  in
  lhs

let barrett_reduce (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
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
              (barrett_reduce_element (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ]
                    <:
                    i16)
                <:
                i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
  in
  v

let bitwise_and_with_constant
      (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (c: i16)
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
              ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16) &. c <: i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
  in
  v

let cond_subtract_3329_ (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
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
          let _:Prims.unit =
            if true
            then
              let _:Prims.unit =
                Hax_lib.v_assert (((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ]
                        <:
                        i16) >=.
                      0s
                      <:
                      bool) &&
                    ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16) <. 4096s
                      <:
                      bool))
              in
              ()
          in
          if (v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16) >=. 3329s
          then
            {
              v with
              Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
                  .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
                i
                ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16) -! 3329s
                  <:
                  i16)
            }
            <:
            Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
          else v)
  in
  v

let montgomery_multiply_by_constant
      (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (c: i16)
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
              (montgomery_multiply_fe_by_fer (v
                      .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ]
                    <:
                    i16)
                  c
                <:
                i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
  in
  v

let multiply_by_constant (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (c: i16) =
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
              ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16) *! c <: i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
  in
  v

let shift_right (v_SHIFT_BY: i32) (v: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
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
              ((v.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16) >>! v_SHIFT_BY
                <:
                i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
  in
  v

let sub (lhs rhs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) =
  let lhs:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      Libcrux_ml_kem.Vector.Traits.v_FIELD_ELEMENTS_IN_VECTOR
      (fun lhs temp_1_ ->
          let lhs:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = lhs in
          let _:usize = temp_1_ in
          true)
      lhs
      (fun lhs i ->
          let lhs:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = lhs in
          let i:usize = i in
          {
            lhs with
            Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize lhs
                .Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements
              i
              ((lhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16) -!
                (rhs.Libcrux_ml_kem.Vector.Portable.Vector_type.f_elements.[ i ] <: i16)
                <:
                i16)
            <:
            t_Array i16 (sz 16)
          }
          <:
          Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
  in
  lhs
