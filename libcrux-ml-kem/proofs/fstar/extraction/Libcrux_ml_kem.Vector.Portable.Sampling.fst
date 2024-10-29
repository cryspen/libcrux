module Libcrux_ml_kem.Vector.Portable.Sampling
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let rej_sample (a: t_Slice u8) (result: t_Slice i16) =
  let sampled:usize = sz 0 in
  let result, sampled:(t_Slice i16 & usize) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      ((Core.Slice.impl__len #u8 a <: usize) /! sz 3 <: usize)
      (fun temp_0_ temp_1_ ->
          let result, sampled:(t_Slice i16 & usize) = temp_0_ in
          let _:usize = temp_1_ in
          true)
      (result, sampled <: (t_Slice i16 & usize))
      (fun temp_0_ i ->
          let result, sampled:(t_Slice i16 & usize) = temp_0_ in
          let i:usize = i in
          let b1:i16 = cast (a.[ (i *! sz 3 <: usize) +! sz 0 <: usize ] <: u8) <: i16 in
          let b2:i16 = cast (a.[ (i *! sz 3 <: usize) +! sz 1 <: usize ] <: u8) <: i16 in
          let b3:i16 = cast (a.[ (i *! sz 3 <: usize) +! sz 2 <: usize ] <: u8) <: i16 in
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
