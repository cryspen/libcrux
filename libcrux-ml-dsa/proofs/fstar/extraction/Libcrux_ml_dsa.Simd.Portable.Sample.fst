module Libcrux_ml_dsa.Simd.Portable.Sample
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let rejection_sample_less_than_field_modulus (randomness: t_Slice u8) (out: t_Slice i32) =
  let sampled:usize = mk_usize 0 in
  let out, sampled:(t_Slice i32 & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Slice.Iter.t_ChunksExact
            u8)
          #FStar.Tactics.Typeclasses.solve
          (Core.Slice.impl__chunks_exact #u8 randomness (mk_usize 3)
            <:
            Core.Slice.Iter.t_ChunksExact u8)
        <:
        Core.Slice.Iter.t_ChunksExact u8)
      (out, sampled <: (t_Slice i32 & usize))
      (fun temp_0_ bytes ->
          let out, sampled:(t_Slice i32 & usize) = temp_0_ in
          let bytes:t_Slice u8 = bytes in
          let b0:i32 = cast (bytes.[ mk_usize 0 ] <: u8) <: i32 in
          let b1:i32 = cast (bytes.[ mk_usize 1 ] <: u8) <: i32 in
          let b2:i32 = cast (bytes.[ mk_usize 2 ] <: u8) <: i32 in
          let coefficient:i32 =
            (((b2 <<! mk_i32 16 <: i32) |. (b1 <<! mk_i32 8 <: i32) <: i32) |. b0 <: i32) &.
            mk_i32 8388607
          in
          if coefficient <. Libcrux_ml_dsa.Constants.v_FIELD_MODULUS
          then
            let out:t_Slice i32 =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out sampled coefficient
            in
            let sampled:usize = sampled +! mk_usize 1 in
            out, sampled <: (t_Slice i32 & usize)
          else out, sampled <: (t_Slice i32 & usize))
  in
  let hax_temp_output:usize = sampled in
  out, hax_temp_output <: (t_Slice i32 & usize)

let rejection_sample_less_than_eta_equals_2_ (randomness: t_Slice u8) (out: t_Slice i32) =
  let sampled:usize = mk_usize 0 in
  let out, sampled:(t_Slice i32 & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Slice.Iter.t_Iter
            u8)
          #FStar.Tactics.Typeclasses.solve
          (Core.Slice.impl__iter #u8 randomness <: Core.Slice.Iter.t_Iter u8)
        <:
        Core.Slice.Iter.t_Iter u8)
      (out, sampled <: (t_Slice i32 & usize))
      (fun temp_0_ byte ->
          let out, sampled:(t_Slice i32 & usize) = temp_0_ in
          let byte:u8 = byte in
          let try_0_:u8 = byte &. mk_u8 15 in
          let try_1_:u8 = byte >>! mk_i32 4 in
          let out, sampled:(t_Slice i32 & usize) =
            if try_0_ <. mk_u8 15
            then
              let try_0_:i32 = cast (try_0_ <: u8) <: i32 in
              let try_0_mod_5_:i32 =
                try_0_ -! (((try_0_ *! mk_i32 26 <: i32) >>! mk_i32 7 <: i32) *! mk_i32 5 <: i32)
              in
              let out:t_Slice i32 =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                  sampled
                  (mk_i32 2 -! try_0_mod_5_ <: i32)
              in
              let sampled:usize = sampled +! mk_usize 1 in
              out, sampled <: (t_Slice i32 & usize)
            else out, sampled <: (t_Slice i32 & usize)
          in
          if try_1_ <. mk_u8 15
          then
            let try_1_:i32 = cast (try_1_ <: u8) <: i32 in
            let try_1_mod_5_:i32 =
              try_1_ -! (((try_1_ *! mk_i32 26 <: i32) >>! mk_i32 7 <: i32) *! mk_i32 5 <: i32)
            in
            let out:t_Slice i32 =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                sampled
                (mk_i32 2 -! try_1_mod_5_ <: i32)
            in
            let sampled:usize = sampled +! mk_usize 1 in
            out, sampled <: (t_Slice i32 & usize)
          else out, sampled <: (t_Slice i32 & usize))
  in
  let hax_temp_output:usize = sampled in
  out, hax_temp_output <: (t_Slice i32 & usize)

let rejection_sample_less_than_eta_equals_4_ (randomness: t_Slice u8) (out: t_Slice i32) =
  let sampled:usize = mk_usize 0 in
  let out, sampled:(t_Slice i32 & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Slice.Iter.t_Iter
            u8)
          #FStar.Tactics.Typeclasses.solve
          (Core.Slice.impl__iter #u8 randomness <: Core.Slice.Iter.t_Iter u8)
        <:
        Core.Slice.Iter.t_Iter u8)
      (out, sampled <: (t_Slice i32 & usize))
      (fun temp_0_ byte ->
          let out, sampled:(t_Slice i32 & usize) = temp_0_ in
          let byte:u8 = byte in
          let try_0_:u8 = byte &. mk_u8 15 in
          let try_1_:u8 = byte >>! mk_i32 4 in
          let out, sampled:(t_Slice i32 & usize) =
            if try_0_ <. mk_u8 9
            then
              let out:t_Slice i32 =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                  sampled
                  (mk_i32 4 -! (cast (try_0_ <: u8) <: i32) <: i32)
              in
              let sampled:usize = sampled +! mk_usize 1 in
              out, sampled <: (t_Slice i32 & usize)
            else out, sampled <: (t_Slice i32 & usize)
          in
          if try_1_ <. mk_u8 9
          then
            let out:t_Slice i32 =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                sampled
                (mk_i32 4 -! (cast (try_1_ <: u8) <: i32) <: i32)
            in
            let sampled:usize = sampled +! mk_usize 1 in
            out, sampled <: (t_Slice i32 & usize)
          else out, sampled <: (t_Slice i32 & usize))
  in
  let hax_temp_output:usize = sampled in
  out, hax_temp_output <: (t_Slice i32 & usize)
