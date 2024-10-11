module Libcrux_ml_dsa.Simd.Portable.Encoding.Gamma1
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Portable in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let deserialize_when_gamma1_is_2_pow_17___GAMMA1: i32 =
  Rust_primitives.mk_i32 1 <<! Rust_primitives.mk_i32 17

let deserialize_when_gamma1_is_2_pow_17___GAMMA1_TIMES_2_BITMASK: i32 =
  (deserialize_when_gamma1_is_2_pow_17___GAMMA1 <<! Rust_primitives.mk_i32 1 <: i32) -!
  Rust_primitives.mk_i32 1

let deserialize_when_gamma1_is_2_pow_19___GAMMA1: i32 =
  Rust_primitives.mk_i32 1 <<! Rust_primitives.mk_i32 19

let deserialize_when_gamma1_is_2_pow_19___GAMMA1_TIMES_2_BITMASK: i32 =
  (deserialize_when_gamma1_is_2_pow_19___GAMMA1 <<! Rust_primitives.mk_i32 1 <: i32) -!
  Rust_primitives.mk_i32 1

let serialize_when_gamma1_is_2_pow_17___GAMMA1: i32 =
  Rust_primitives.mk_i32 1 <<! Rust_primitives.mk_i32 17

let serialize_when_gamma1_is_2_pow_19___GAMMA1: i32 =
  Rust_primitives.mk_i32 1 <<! Rust_primitives.mk_i32 19

let serialize_when_gamma1_is_2_pow_17_
      (v_OUTPUT_SIZE: usize)
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
    : t_Array u8 v_OUTPUT_SIZE =
  let serialized:t_Array u8 v_OUTPUT_SIZE =
    Rust_primitives.Hax.repeat (Rust_primitives.mk_u8 0) v_OUTPUT_SIZE
  in
  let serialized:t_Array u8 v_OUTPUT_SIZE =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (Rust_primitives.mk_usize 4)
      (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients <: t_Slice i32)
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 v_OUTPUT_SIZE = serialized in
          let _:usize = temp_1_ in
          true)
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 v_OUTPUT_SIZE = serialized in
          let i, coefficients:(usize & t_Slice i32) = temp_1_ in
          let coefficient0:i32 =
            serialize_when_gamma1_is_2_pow_17___GAMMA1 -!
            (coefficients.[ Rust_primitives.mk_usize 0 ] <: i32)
          in
          let coefficient1:i32 =
            serialize_when_gamma1_is_2_pow_17___GAMMA1 -!
            (coefficients.[ Rust_primitives.mk_usize 1 ] <: i32)
          in
          let coefficient2:i32 =
            serialize_when_gamma1_is_2_pow_17___GAMMA1 -!
            (coefficients.[ Rust_primitives.mk_usize 2 ] <: i32)
          in
          let coefficient3:i32 =
            serialize_when_gamma1_is_2_pow_17___GAMMA1 -!
            (coefficients.[ Rust_primitives.mk_usize 3 ] <: i32)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              (Rust_primitives.mk_usize 9 *! i <: usize)
              (cast (coefficient0 <: i32) <: u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((Rust_primitives.mk_usize 9 *! i <: usize) +! Rust_primitives.mk_usize 1 <: usize)
              (cast (coefficient0 >>! Rust_primitives.mk_i32 8 <: i32) <: u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((Rust_primitives.mk_usize 9 *! i <: usize) +! Rust_primitives.mk_usize 2 <: usize)
              (cast (coefficient0 >>! Rust_primitives.mk_i32 16 <: i32) <: u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((Rust_primitives.mk_usize 9 *! i <: usize) +! Rust_primitives.mk_usize 2 <: usize)
              ((serialized.[ (Rust_primitives.mk_usize 9 *! i <: usize) +!
                    Rust_primitives.mk_usize 2
                    <:
                    usize ]
                  <:
                  u8) |.
                (cast (coefficient1 <<! Rust_primitives.mk_i32 2 <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((Rust_primitives.mk_usize 9 *! i <: usize) +! Rust_primitives.mk_usize 3 <: usize)
              (cast (coefficient1 >>! Rust_primitives.mk_i32 6 <: i32) <: u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((Rust_primitives.mk_usize 9 *! i <: usize) +! Rust_primitives.mk_usize 4 <: usize)
              (cast (coefficient1 >>! Rust_primitives.mk_i32 14 <: i32) <: u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((Rust_primitives.mk_usize 9 *! i <: usize) +! Rust_primitives.mk_usize 4 <: usize)
              ((serialized.[ (Rust_primitives.mk_usize 9 *! i <: usize) +!
                    Rust_primitives.mk_usize 4
                    <:
                    usize ]
                  <:
                  u8) |.
                (cast (coefficient2 <<! Rust_primitives.mk_i32 4 <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((Rust_primitives.mk_usize 9 *! i <: usize) +! Rust_primitives.mk_usize 5 <: usize)
              (cast (coefficient2 >>! Rust_primitives.mk_i32 4 <: i32) <: u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((Rust_primitives.mk_usize 9 *! i <: usize) +! Rust_primitives.mk_usize 6 <: usize)
              (cast (coefficient2 >>! Rust_primitives.mk_i32 12 <: i32) <: u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((Rust_primitives.mk_usize 9 *! i <: usize) +! Rust_primitives.mk_usize 6 <: usize)
              ((serialized.[ (Rust_primitives.mk_usize 9 *! i <: usize) +!
                    Rust_primitives.mk_usize 6
                    <:
                    usize ]
                  <:
                  u8) |.
                (cast (coefficient3 <<! Rust_primitives.mk_i32 6 <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((Rust_primitives.mk_usize 9 *! i <: usize) +! Rust_primitives.mk_usize 7 <: usize)
              (cast (coefficient3 >>! Rust_primitives.mk_i32 2 <: i32) <: u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((Rust_primitives.mk_usize 9 *! i <: usize) +! Rust_primitives.mk_usize 8 <: usize)
              (cast (coefficient3 >>! Rust_primitives.mk_i32 10 <: i32) <: u8)
          in
          serialized)
  in
  serialized

let serialize_when_gamma1_is_2_pow_19_
      (v_OUTPUT_SIZE: usize)
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
    : t_Array u8 v_OUTPUT_SIZE =
  let serialized:t_Array u8 v_OUTPUT_SIZE =
    Rust_primitives.Hax.repeat (Rust_primitives.mk_u8 0) v_OUTPUT_SIZE
  in
  let serialized:t_Array u8 v_OUTPUT_SIZE =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (Rust_primitives.mk_usize 2)
      (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients <: t_Slice i32)
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 v_OUTPUT_SIZE = serialized in
          let _:usize = temp_1_ in
          true)
      serialized
      (fun serialized temp_1_ ->
          let serialized:t_Array u8 v_OUTPUT_SIZE = serialized in
          let i, coefficients:(usize & t_Slice i32) = temp_1_ in
          let coefficient0:i32 =
            serialize_when_gamma1_is_2_pow_19___GAMMA1 -!
            (coefficients.[ Rust_primitives.mk_usize 0 ] <: i32)
          in
          let coefficient1:i32 =
            serialize_when_gamma1_is_2_pow_19___GAMMA1 -!
            (coefficients.[ Rust_primitives.mk_usize 1 ] <: i32)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              (Rust_primitives.mk_usize 5 *! i <: usize)
              (cast (coefficient0 <: i32) <: u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((Rust_primitives.mk_usize 5 *! i <: usize) +! Rust_primitives.mk_usize 1 <: usize)
              (cast (coefficient0 >>! Rust_primitives.mk_i32 8 <: i32) <: u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((Rust_primitives.mk_usize 5 *! i <: usize) +! Rust_primitives.mk_usize 2 <: usize)
              (cast (coefficient0 >>! Rust_primitives.mk_i32 16 <: i32) <: u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((Rust_primitives.mk_usize 5 *! i <: usize) +! Rust_primitives.mk_usize 2 <: usize)
              ((serialized.[ (Rust_primitives.mk_usize 5 *! i <: usize) +!
                    Rust_primitives.mk_usize 2
                    <:
                    usize ]
                  <:
                  u8) |.
                (cast (coefficient1 <<! Rust_primitives.mk_i32 4 <: i32) <: u8)
                <:
                u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((Rust_primitives.mk_usize 5 *! i <: usize) +! Rust_primitives.mk_usize 3 <: usize)
              (cast (coefficient1 >>! Rust_primitives.mk_i32 4 <: i32) <: u8)
          in
          let serialized:t_Array u8 v_OUTPUT_SIZE =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize serialized
              ((Rust_primitives.mk_usize 5 *! i <: usize) +! Rust_primitives.mk_usize 4 <: usize)
              (cast (coefficient1 >>! Rust_primitives.mk_i32 12 <: i32) <: u8)
          in
          serialized)
  in
  serialized

let serialize (v_OUTPUT_SIZE: usize) (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
    : t_Array u8 v_OUTPUT_SIZE =
  match cast (v_OUTPUT_SIZE <: usize) <: u8 with
  | 18 -> serialize_when_gamma1_is_2_pow_17_ v_OUTPUT_SIZE simd_unit
  | 20 -> serialize_when_gamma1_is_2_pow_19_ v_OUTPUT_SIZE simd_unit
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let deserialize_when_gamma1_is_2_pow_17_ (serialized: t_Slice u8)
    : Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =.
            Rust_primitives.mk_usize 18
            <:
            bool)
      in
      ()
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Traits.f_ZERO #Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (Rust_primitives.mk_usize 9)
      serialized
      (fun simd_unit temp_1_ ->
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit = simd_unit in
          let _:usize = temp_1_ in
          true)
      simd_unit
      (fun simd_unit temp_1_ ->
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit = simd_unit in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                (Rust_primitives.mk_usize 4 *! i <: usize)
                (cast (bytes.[ Rust_primitives.mk_usize 0 ] <: u8) <: i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                (Rust_primitives.mk_usize 4 *! i <: usize)
                ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 4 *!
                      i
                      <:
                      usize ]
                    <:
                    i32) |.
                  ((cast (bytes.[ Rust_primitives.mk_usize 1 ] <: u8) <: i32) <<!
                    Rust_primitives.mk_i32 8
                    <:
                    i32)
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                (Rust_primitives.mk_usize 4 *! i <: usize)
                ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 4 *!
                      i
                      <:
                      usize ]
                    <:
                    i32) |.
                  ((cast (bytes.[ Rust_primitives.mk_usize 2 ] <: u8) <: i32) <<!
                    Rust_primitives.mk_i32 16
                    <:
                    i32)
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                (Rust_primitives.mk_usize 4 *! i <: usize)
                ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 4 *!
                      i
                      <:
                      usize ]
                    <:
                    i32) &.
                  deserialize_when_gamma1_is_2_pow_17___GAMMA1_TIMES_2_BITMASK
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                ((Rust_primitives.mk_usize 4 *! i <: usize) +! Rust_primitives.mk_usize 1 <: usize)
                ((cast (bytes.[ Rust_primitives.mk_usize 2 ] <: u8) <: i32) >>!
                  Rust_primitives.mk_i32 2
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                ((Rust_primitives.mk_usize 4 *! i <: usize) +! Rust_primitives.mk_usize 1 <: usize)
                ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ (Rust_primitives.mk_usize
                        4 *!
                        i
                        <:
                        usize) +!
                      Rust_primitives.mk_usize 1
                      <:
                      usize ]
                    <:
                    i32) |.
                  ((cast (bytes.[ Rust_primitives.mk_usize 3 ] <: u8) <: i32) <<!
                    Rust_primitives.mk_i32 6
                    <:
                    i32)
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                ((Rust_primitives.mk_usize 4 *! i <: usize) +! Rust_primitives.mk_usize 1 <: usize)
                ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ (Rust_primitives.mk_usize
                        4 *!
                        i
                        <:
                        usize) +!
                      Rust_primitives.mk_usize 1
                      <:
                      usize ]
                    <:
                    i32) |.
                  ((cast (bytes.[ Rust_primitives.mk_usize 4 ] <: u8) <: i32) <<!
                    Rust_primitives.mk_i32 14
                    <:
                    i32)
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                ((Rust_primitives.mk_usize 4 *! i <: usize) +! Rust_primitives.mk_usize 1 <: usize)
                ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ (Rust_primitives.mk_usize
                        4 *!
                        i
                        <:
                        usize) +!
                      Rust_primitives.mk_usize 1
                      <:
                      usize ]
                    <:
                    i32) &.
                  deserialize_when_gamma1_is_2_pow_17___GAMMA1_TIMES_2_BITMASK
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                ((Rust_primitives.mk_usize 4 *! i <: usize) +! Rust_primitives.mk_usize 2 <: usize)
                ((cast (bytes.[ Rust_primitives.mk_usize 4 ] <: u8) <: i32) >>!
                  Rust_primitives.mk_i32 4
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                ((Rust_primitives.mk_usize 4 *! i <: usize) +! Rust_primitives.mk_usize 2 <: usize)
                ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ (Rust_primitives.mk_usize
                        4 *!
                        i
                        <:
                        usize) +!
                      Rust_primitives.mk_usize 2
                      <:
                      usize ]
                    <:
                    i32) |.
                  ((cast (bytes.[ Rust_primitives.mk_usize 5 ] <: u8) <: i32) <<!
                    Rust_primitives.mk_i32 4
                    <:
                    i32)
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                ((Rust_primitives.mk_usize 4 *! i <: usize) +! Rust_primitives.mk_usize 2 <: usize)
                ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ (Rust_primitives.mk_usize
                        4 *!
                        i
                        <:
                        usize) +!
                      Rust_primitives.mk_usize 2
                      <:
                      usize ]
                    <:
                    i32) |.
                  ((cast (bytes.[ Rust_primitives.mk_usize 6 ] <: u8) <: i32) <<!
                    Rust_primitives.mk_i32 12
                    <:
                    i32)
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                ((Rust_primitives.mk_usize 4 *! i <: usize) +! Rust_primitives.mk_usize 2 <: usize)
                ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ (Rust_primitives.mk_usize
                        4 *!
                        i
                        <:
                        usize) +!
                      Rust_primitives.mk_usize 2
                      <:
                      usize ]
                    <:
                    i32) &.
                  deserialize_when_gamma1_is_2_pow_17___GAMMA1_TIMES_2_BITMASK
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                ((Rust_primitives.mk_usize 4 *! i <: usize) +! Rust_primitives.mk_usize 3 <: usize)
                ((cast (bytes.[ Rust_primitives.mk_usize 6 ] <: u8) <: i32) >>!
                  Rust_primitives.mk_i32 6
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                ((Rust_primitives.mk_usize 4 *! i <: usize) +! Rust_primitives.mk_usize 3 <: usize)
                ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ (Rust_primitives.mk_usize
                        4 *!
                        i
                        <:
                        usize) +!
                      Rust_primitives.mk_usize 3
                      <:
                      usize ]
                    <:
                    i32) |.
                  ((cast (bytes.[ Rust_primitives.mk_usize 7 ] <: u8) <: i32) <<!
                    Rust_primitives.mk_i32 2
                    <:
                    i32)
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                ((Rust_primitives.mk_usize 4 *! i <: usize) +! Rust_primitives.mk_usize 3 <: usize)
                ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ (Rust_primitives.mk_usize
                        4 *!
                        i
                        <:
                        usize) +!
                      Rust_primitives.mk_usize 3
                      <:
                      usize ]
                    <:
                    i32) |.
                  ((cast (bytes.[ Rust_primitives.mk_usize 8 ] <: u8) <: i32) <<!
                    Rust_primitives.mk_i32 10
                    <:
                    i32)
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                ((Rust_primitives.mk_usize 4 *! i <: usize) +! Rust_primitives.mk_usize 3 <: usize)
                ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ (Rust_primitives.mk_usize
                        4 *!
                        i
                        <:
                        usize) +!
                      Rust_primitives.mk_usize 3
                      <:
                      usize ]
                    <:
                    i32) &.
                  deserialize_when_gamma1_is_2_pow_17___GAMMA1_TIMES_2_BITMASK
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                (Rust_primitives.mk_usize 4 *! i <: usize)
                (deserialize_when_gamma1_is_2_pow_17___GAMMA1 -!
                  (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize
                      4 *!
                      i
                      <:
                      usize ]
                    <:
                    i32)
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                ((Rust_primitives.mk_usize 4 *! i <: usize) +! Rust_primitives.mk_usize 1 <: usize)
                (deserialize_when_gamma1_is_2_pow_17___GAMMA1 -!
                  (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ (Rust_primitives.mk_usize
                        4 *!
                        i
                        <:
                        usize) +!
                      Rust_primitives.mk_usize 1
                      <:
                      usize ]
                    <:
                    i32)
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                ((Rust_primitives.mk_usize 4 *! i <: usize) +! Rust_primitives.mk_usize 2 <: usize)
                (deserialize_when_gamma1_is_2_pow_17___GAMMA1 -!
                  (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ (Rust_primitives.mk_usize
                        4 *!
                        i
                        <:
                        usize) +!
                      Rust_primitives.mk_usize 2
                      <:
                      usize ]
                    <:
                    i32)
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                ((Rust_primitives.mk_usize 4 *! i <: usize) +! Rust_primitives.mk_usize 3 <: usize)
                (deserialize_when_gamma1_is_2_pow_17___GAMMA1 -!
                  (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ (Rust_primitives.mk_usize
                        4 *!
                        i
                        <:
                        usize) +!
                      Rust_primitives.mk_usize 3
                      <:
                      usize ]
                    <:
                    i32)
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          simd_unit)
  in
  simd_unit

let deserialize_when_gamma1_is_2_pow_19_ (serialized: t_Slice u8)
    : Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core.Slice.impl__len #u8 serialized <: usize) =.
            Rust_primitives.mk_usize 20
            <:
            bool)
      in
      ()
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    Libcrux_ml_dsa.Simd.Traits.f_ZERO #Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (Rust_primitives.mk_usize 5)
      serialized
      (fun simd_unit temp_1_ ->
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit = simd_unit in
          let _:usize = temp_1_ in
          true)
      simd_unit
      (fun simd_unit temp_1_ ->
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit = simd_unit in
          let i, bytes:(usize & t_Slice u8) = temp_1_ in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                (Rust_primitives.mk_usize 2 *! i <: usize)
                (cast (bytes.[ Rust_primitives.mk_usize 0 ] <: u8) <: i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                (Rust_primitives.mk_usize 2 *! i <: usize)
                ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 2 *!
                      i
                      <:
                      usize ]
                    <:
                    i32) |.
                  ((cast (bytes.[ Rust_primitives.mk_usize 1 ] <: u8) <: i32) <<!
                    Rust_primitives.mk_i32 8
                    <:
                    i32)
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                (Rust_primitives.mk_usize 2 *! i <: usize)
                ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 2 *!
                      i
                      <:
                      usize ]
                    <:
                    i32) |.
                  ((cast (bytes.[ Rust_primitives.mk_usize 2 ] <: u8) <: i32) <<!
                    Rust_primitives.mk_i32 16
                    <:
                    i32)
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                (Rust_primitives.mk_usize 2 *! i <: usize)
                ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize 2 *!
                      i
                      <:
                      usize ]
                    <:
                    i32) &.
                  deserialize_when_gamma1_is_2_pow_19___GAMMA1_TIMES_2_BITMASK
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                ((Rust_primitives.mk_usize 2 *! i <: usize) +! Rust_primitives.mk_usize 1 <: usize)
                ((cast (bytes.[ Rust_primitives.mk_usize 2 ] <: u8) <: i32) >>!
                  Rust_primitives.mk_i32 4
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                ((Rust_primitives.mk_usize 2 *! i <: usize) +! Rust_primitives.mk_usize 1 <: usize)
                ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ (Rust_primitives.mk_usize
                        2 *!
                        i
                        <:
                        usize) +!
                      Rust_primitives.mk_usize 1
                      <:
                      usize ]
                    <:
                    i32) |.
                  ((cast (bytes.[ Rust_primitives.mk_usize 3 ] <: u8) <: i32) <<!
                    Rust_primitives.mk_i32 4
                    <:
                    i32)
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                ((Rust_primitives.mk_usize 2 *! i <: usize) +! Rust_primitives.mk_usize 1 <: usize)
                ((simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ (Rust_primitives.mk_usize
                        2 *!
                        i
                        <:
                        usize) +!
                      Rust_primitives.mk_usize 1
                      <:
                      usize ]
                    <:
                    i32) |.
                  ((cast (bytes.[ Rust_primitives.mk_usize 4 ] <: u8) <: i32) <<!
                    Rust_primitives.mk_i32 12
                    <:
                    i32)
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                (Rust_primitives.mk_usize 2 *! i <: usize)
                (deserialize_when_gamma1_is_2_pow_19___GAMMA1 -!
                  (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ Rust_primitives.mk_usize
                      2 *!
                      i
                      <:
                      usize ]
                    <:
                    i32)
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          let simd_unit:Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
            {
              simd_unit with
              Libcrux_ml_dsa.Simd.Portable.f_coefficients
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize simd_unit
                  .Libcrux_ml_dsa.Simd.Portable.f_coefficients
                ((Rust_primitives.mk_usize 2 *! i <: usize) +! Rust_primitives.mk_usize 1 <: usize)
                (deserialize_when_gamma1_is_2_pow_19___GAMMA1 -!
                  (simd_unit.Libcrux_ml_dsa.Simd.Portable.f_coefficients.[ (Rust_primitives.mk_usize
                        2 *!
                        i
                        <:
                        usize) +!
                      Rust_primitives.mk_usize 1
                      <:
                      usize ]
                    <:
                    i32)
                  <:
                  i32)
            }
            <:
            Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
          in
          simd_unit)
  in
  simd_unit

let deserialize (v_GAMMA1_EXPONENT: usize) (serialized: t_Slice u8)
    : Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit =
  match cast (v_GAMMA1_EXPONENT <: usize) <: u8 with
  | 17 -> deserialize_when_gamma1_is_2_pow_17_ serialized
  | 19 -> deserialize_when_gamma1_is_2_pow_19_ serialized
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)
