module Libcrux_ml_kem.Vector.Neon
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Neon.Vector_type in
  ()

let rej_sample (a: t_Slice u8) (result: t_Slice i16) =
  let sampled:usize = sz 0 in
  let result, sampled:(t_Slice i16 & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Slice.Iter.t_Chunks
            u8)
          #FStar.Tactics.Typeclasses.solve
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
