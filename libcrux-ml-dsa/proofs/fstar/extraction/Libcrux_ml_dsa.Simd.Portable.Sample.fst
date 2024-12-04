module Libcrux_ml_dsa.Simd.Portable.Sample
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let rejection_sample_less_than_eta_equals_2_ (randomness: t_Slice u8) (out: t_Slice i32) =
  let sampled:usize = sz 0 in
  let out, sampled:(t_Slice i32 & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(t_Slice u8)
          #FStar.Tactics.Typeclasses.solve
          randomness
        <:
        Core.Slice.Iter.t_Iter u8)
      (out, sampled <: (t_Slice i32 & usize))
      (fun temp_0_ byte ->
          let out, sampled:(t_Slice i32 & usize) = temp_0_ in
          let byte:u8 = byte in
          let try_0_:u8 = byte &. 15uy in
          let try_1_:u8 = byte >>! 4l in
          let out, sampled:(t_Slice i32 & usize) =
            if try_0_ <. 15uy
            then
              let try_0_:i32 = cast (try_0_ <: u8) <: i32 in
              let try_0_mod_5_:i32 =
                try_0_ -! (((try_0_ *! 26l <: i32) >>! 7l <: i32) *! 5l <: i32)
              in
              let out:t_Slice i32 =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                  sampled
                  (2l -! try_0_mod_5_ <: i32)
              in
              let sampled:usize = sampled +! sz 1 in
              out, sampled <: (t_Slice i32 & usize)
            else out, sampled <: (t_Slice i32 & usize)
          in
          if try_1_ <. 15uy
          then
            let try_1_:i32 = cast (try_1_ <: u8) <: i32 in
            let try_1_mod_5_:i32 =
              try_1_ -! (((try_1_ *! 26l <: i32) >>! 7l <: i32) *! 5l <: i32)
            in
            let out:t_Slice i32 =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                sampled
                (2l -! try_1_mod_5_ <: i32)
            in
            let sampled:usize = sampled +! sz 1 in
            out, sampled <: (t_Slice i32 & usize)
          else out, sampled <: (t_Slice i32 & usize))
  in
  let hax_temp_output:usize = sampled in
  out, hax_temp_output <: (t_Slice i32 & usize)

let rejection_sample_less_than_eta_equals_4_ (randomness: t_Slice u8) (out: t_Slice i32) =
  let sampled:usize = sz 0 in
  let out, sampled:(t_Slice i32 & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(t_Slice u8)
          #FStar.Tactics.Typeclasses.solve
          randomness
        <:
        Core.Slice.Iter.t_Iter u8)
      (out, sampled <: (t_Slice i32 & usize))
      (fun temp_0_ byte ->
          let out, sampled:(t_Slice i32 & usize) = temp_0_ in
          let byte:u8 = byte in
          let try_0_:u8 = byte &. 15uy in
          let try_1_:u8 = byte >>! 4l in
          let out, sampled:(t_Slice i32 & usize) =
            if try_0_ <. 9uy
            then
              let out:t_Slice i32 =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                  sampled
                  (4l -! (cast (try_0_ <: u8) <: i32) <: i32)
              in
              let sampled:usize = sampled +! sz 1 in
              out, sampled <: (t_Slice i32 & usize)
            else out, sampled <: (t_Slice i32 & usize)
          in
          if try_1_ <. 9uy
          then
            let out:t_Slice i32 =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                sampled
                (4l -! (cast (try_1_ <: u8) <: i32) <: i32)
            in
            let sampled:usize = sampled +! sz 1 in
            out, sampled <: (t_Slice i32 & usize)
          else out, sampled <: (t_Slice i32 & usize))
  in
  let hax_temp_output:usize = sampled in
  out, hax_temp_output <: (t_Slice i32 & usize)

let rejection_sample_less_than_field_modulus (randomness: t_Slice u8) (out: t_Slice i32) =
  let sampled:usize = sz 0 in
  let out, sampled:(t_Slice i32 & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Slice.Iter.t_Chunks
            u8)
          #FStar.Tactics.Typeclasses.solve
          (Core.Slice.impl__chunks #u8 randomness (sz 3) <: Core.Slice.Iter.t_Chunks u8)
        <:
        Core.Slice.Iter.t_Chunks u8)
      (out, sampled <: (t_Slice i32 & usize))
      (fun temp_0_ bytes ->
          let out, sampled:(t_Slice i32 & usize) = temp_0_ in
          let bytes:t_Slice u8 = bytes in
          let b0:i32 = cast (bytes.[ sz 0 ] <: u8) <: i32 in
          let b1:i32 = cast (bytes.[ sz 1 ] <: u8) <: i32 in
          let b2:i32 = cast (bytes.[ sz 2 ] <: u8) <: i32 in
          let coefficient:i32 =
            (((b2 <<! 16l <: i32) |. (b1 <<! 8l <: i32) <: i32) |. b0 <: i32) &. 8388607l
          in
          if coefficient <. Libcrux_ml_dsa.Constants.v_FIELD_MODULUS
          then
            let out:t_Slice i32 =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out sampled coefficient
            in
            let sampled:usize = sampled +! sz 1 in
            out, sampled <: (t_Slice i32 & usize)
          else out, sampled <: (t_Slice i32 & usize))
  in
  let hax_temp_output:usize = sampled in
  out, hax_temp_output <: (t_Slice i32 & usize)
