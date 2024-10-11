module Libcrux_ml_dsa.Simd.Avx2.Rejection_sample.Shuffle_table
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let is_bit_set (number: usize) (bit_position: u8) =
  ((number &. (Rust_primitives.mk_usize 1 <<! bit_position <: usize) <: usize) >>! bit_position
    <:
    usize) =.
  Rust_primitives.mk_usize 1

let generate_shuffle_table (_: Prims.unit) =
  let byte_shuffles:t_Array (t_Array u8 (Rust_primitives.mk_usize 16)) (Rust_primitives.mk_usize 16)
  =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat (Rust_primitives.mk_u8 255)
          (Rust_primitives.mk_usize 16)
        <:
        t_Array u8 (Rust_primitives.mk_usize 16))
      (Rust_primitives.mk_usize 16)
  in
  let byte_shuffles:t_Array (t_Array u8 (Rust_primitives.mk_usize 16)) (Rust_primitives.mk_usize 16)
  =
    Rust_primitives.Hax.Folds.fold_range (Rust_primitives.mk_usize 0)
      (Rust_primitives.mk_usize 1 <<! Rust_primitives.mk_i32 4 <: usize)
      (fun byte_shuffles temp_1_ ->
          let byte_shuffles:t_Array (t_Array u8 (Rust_primitives.mk_usize 16))
            (Rust_primitives.mk_usize 16) =
            byte_shuffles
          in
          let _:usize = temp_1_ in
          true)
      byte_shuffles
      (fun byte_shuffles bit_pattern ->
          let byte_shuffles:t_Array (t_Array u8 (Rust_primitives.mk_usize 16))
            (Rust_primitives.mk_usize 16) =
            byte_shuffles
          in
          let bit_pattern:usize = bit_pattern in
          let byte_shuffles_index:usize = Rust_primitives.mk_usize 0 in
          let byte_shuffles, byte_shuffles_index:(t_Array (t_Array u8 (Rust_primitives.mk_usize 16))
              (Rust_primitives.mk_usize 16) &
            usize) =
            Rust_primitives.Hax.Folds.fold_range (Rust_primitives.mk_u8 0)
              (Rust_primitives.mk_u8 4)
              (fun temp_0_ temp_1_ ->
                  let byte_shuffles, byte_shuffles_index:(t_Array
                      (t_Array u8 (Rust_primitives.mk_usize 16)) (Rust_primitives.mk_usize 16) &
                    usize) =
                    temp_0_
                  in
                  let _:u8 = temp_1_ in
                  true)
              (byte_shuffles, byte_shuffles_index
                <:
                (t_Array (t_Array u8 (Rust_primitives.mk_usize 16)) (Rust_primitives.mk_usize 16) &
                  usize))
              (fun temp_0_ bit_position ->
                  let byte_shuffles, byte_shuffles_index:(t_Array
                      (t_Array u8 (Rust_primitives.mk_usize 16)) (Rust_primitives.mk_usize 16) &
                    usize) =
                    temp_0_
                  in
                  let bit_position:u8 = bit_position in
                  if is_bit_set bit_pattern bit_position <: bool
                  then
                    let byte_shuffles:t_Array (t_Array u8 (Rust_primitives.mk_usize 16))
                      (Rust_primitives.mk_usize 16) =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize byte_shuffles
                        bit_pattern
                        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (byte_shuffles.[
                                bit_pattern ]
                              <:
                              t_Array u8 (Rust_primitives.mk_usize 16))
                            byte_shuffles_index
                            (bit_position *! Rust_primitives.mk_u8 4 <: u8)
                          <:
                          t_Array u8 (Rust_primitives.mk_usize 16))
                    in
                    let byte_shuffles_index:usize =
                      byte_shuffles_index +! Rust_primitives.mk_usize 1
                    in
                    let byte_shuffles:t_Array (t_Array u8 (Rust_primitives.mk_usize 16))
                      (Rust_primitives.mk_usize 16) =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize byte_shuffles
                        bit_pattern
                        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (byte_shuffles.[
                                bit_pattern ]
                              <:
                              t_Array u8 (Rust_primitives.mk_usize 16))
                            byte_shuffles_index
                            ((bit_position *! Rust_primitives.mk_u8 4 <: u8) +!
                              Rust_primitives.mk_u8 1
                              <:
                              u8)
                          <:
                          t_Array u8 (Rust_primitives.mk_usize 16))
                    in
                    let byte_shuffles_index:usize =
                      byte_shuffles_index +! Rust_primitives.mk_usize 1
                    in
                    let byte_shuffles:t_Array (t_Array u8 (Rust_primitives.mk_usize 16))
                      (Rust_primitives.mk_usize 16) =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize byte_shuffles
                        bit_pattern
                        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (byte_shuffles.[
                                bit_pattern ]
                              <:
                              t_Array u8 (Rust_primitives.mk_usize 16))
                            byte_shuffles_index
                            ((bit_position *! Rust_primitives.mk_u8 4 <: u8) +!
                              Rust_primitives.mk_u8 2
                              <:
                              u8)
                          <:
                          t_Array u8 (Rust_primitives.mk_usize 16))
                    in
                    let byte_shuffles_index:usize =
                      byte_shuffles_index +! Rust_primitives.mk_usize 1
                    in
                    let byte_shuffles:t_Array (t_Array u8 (Rust_primitives.mk_usize 16))
                      (Rust_primitives.mk_usize 16) =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize byte_shuffles
                        bit_pattern
                        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (byte_shuffles.[
                                bit_pattern ]
                              <:
                              t_Array u8 (Rust_primitives.mk_usize 16))
                            byte_shuffles_index
                            ((bit_position *! Rust_primitives.mk_u8 4 <: u8) +!
                              Rust_primitives.mk_u8 3
                              <:
                              u8)
                          <:
                          t_Array u8 (Rust_primitives.mk_usize 16))
                    in
                    let byte_shuffles_index:usize =
                      byte_shuffles_index +! Rust_primitives.mk_usize 1
                    in
                    byte_shuffles, byte_shuffles_index
                    <:
                    (t_Array (t_Array u8 (Rust_primitives.mk_usize 16))
                        (Rust_primitives.mk_usize 16) &
                      usize)
                  else
                    byte_shuffles, byte_shuffles_index
                    <:
                    (t_Array (t_Array u8 (Rust_primitives.mk_usize 16))
                        (Rust_primitives.mk_usize 16) &
                      usize))
          in
          byte_shuffles)
  in
  byte_shuffles
