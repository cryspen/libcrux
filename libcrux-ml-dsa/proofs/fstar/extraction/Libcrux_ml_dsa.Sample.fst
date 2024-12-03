module Libcrux_ml_dsa.Sample
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Hash_functions.Portable in
  let open Libcrux_ml_dsa.Hash_functions.Shake128 in
  let open Libcrux_ml_dsa.Hash_functions.Shake256 in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let update_seed (seed: t_Array u8 (sz 66)) (domain_separator: u16) =
  let seed:t_Array u8 (sz 66) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seed
      (sz 64)
      (cast (domain_separator <: u16) <: u8)
  in
  let seed:t_Array u8 (sz 66) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seed
      (sz 65)
      (cast (domain_separator >>! 8l <: u16) <: u8)
  in
  let domain_separator:u16 = domain_separator +! 1us in
  let hax_temp_output:t_Array u8 (sz 66) = seed in
  domain_separator, hax_temp_output <: (u16 & t_Array u8 (sz 66))

let rejection_sample_less_than_eta_equals_2_
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (randomness: t_Slice u8)
      (sampled_coefficients: usize)
      (out: t_Array i32 (sz 263))
     =
  let done:bool = false in
  let done, out, sampled_coefficients:(bool & t_Array i32 (sz 263) & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Slice.Iter.t_Chunks
            u8)
          #FStar.Tactics.Typeclasses.solve
          (Core.Slice.impl__chunks #u8 randomness (sz 4) <: Core.Slice.Iter.t_Chunks u8)
        <:
        Core.Slice.Iter.t_Chunks u8)
      (done, out, sampled_coefficients <: (bool & t_Array i32 (sz 263) & usize))
      (fun temp_0_ random_bytes ->
          let done, out, sampled_coefficients:(bool & t_Array i32 (sz 263) & usize) = temp_0_ in
          let random_bytes:t_Slice u8 = random_bytes in
          if ~.done <: bool
          then
            let tmp0, out1:(t_Slice i32 & usize) =
              Libcrux_ml_dsa.Simd.Traits.f_rejection_sample_less_than_eta_equals_2_ #v_SIMDUnit
                #FStar.Tactics.Typeclasses.solve
                random_bytes
                (out.[ { Core.Ops.Range.f_start = sampled_coefficients }
                    <:
                    Core.Ops.Range.t_RangeFrom usize ]
                  <:
                  t_Slice i32)
            in
            let out:t_Array i32 (sz 263) =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from out
                ({ Core.Ops.Range.f_start = sampled_coefficients }
                  <:
                  Core.Ops.Range.t_RangeFrom usize)
                tmp0
            in
            let sampled:usize = out1 in
            let sampled_coefficients:usize = sampled_coefficients +! sampled in
            if sampled_coefficients >=. Libcrux_ml_dsa.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
            then
              let done:bool = true in
              done, out, sampled_coefficients <: (bool & t_Array i32 (sz 263) & usize)
            else done, out, sampled_coefficients <: (bool & t_Array i32 (sz 263) & usize)
          else done, out, sampled_coefficients <: (bool & t_Array i32 (sz 263) & usize))
  in
  let hax_temp_output:bool = done in
  sampled_coefficients, out, hax_temp_output <: (usize & t_Array i32 (sz 263) & bool)

let rejection_sample_less_than_eta_equals_4_
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (randomness: t_Slice u8)
      (sampled_coefficients: usize)
      (out: t_Array i32 (sz 263))
     =
  let done:bool = false in
  let done, out, sampled_coefficients:(bool & t_Array i32 (sz 263) & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Slice.Iter.t_Chunks
            u8)
          #FStar.Tactics.Typeclasses.solve
          (Core.Slice.impl__chunks #u8 randomness (sz 4) <: Core.Slice.Iter.t_Chunks u8)
        <:
        Core.Slice.Iter.t_Chunks u8)
      (done, out, sampled_coefficients <: (bool & t_Array i32 (sz 263) & usize))
      (fun temp_0_ random_bytes ->
          let done, out, sampled_coefficients:(bool & t_Array i32 (sz 263) & usize) = temp_0_ in
          let random_bytes:t_Slice u8 = random_bytes in
          if ~.done <: bool
          then
            let tmp0, out1:(t_Slice i32 & usize) =
              Libcrux_ml_dsa.Simd.Traits.f_rejection_sample_less_than_eta_equals_4_ #v_SIMDUnit
                #FStar.Tactics.Typeclasses.solve
                random_bytes
                (out.[ { Core.Ops.Range.f_start = sampled_coefficients }
                    <:
                    Core.Ops.Range.t_RangeFrom usize ]
                  <:
                  t_Slice i32)
            in
            let out:t_Array i32 (sz 263) =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from out
                ({ Core.Ops.Range.f_start = sampled_coefficients }
                  <:
                  Core.Ops.Range.t_RangeFrom usize)
                tmp0
            in
            let sampled:usize = out1 in
            let sampled_coefficients:usize = sampled_coefficients +! sampled in
            if sampled_coefficients >=. Libcrux_ml_dsa.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
            then
              let done:bool = true in
              done, out, sampled_coefficients <: (bool & t_Array i32 (sz 263) & usize)
            else done, out, sampled_coefficients <: (bool & t_Array i32 (sz 263) & usize)
          else done, out, sampled_coefficients <: (bool & t_Array i32 (sz 263) & usize))
  in
  let hax_temp_output:bool = done in
  sampled_coefficients, out, hax_temp_output <: (usize & t_Array i32 (sz 263) & bool)

let rejection_sample_less_than_eta
      (#v_SIMDUnit: Type0)
      (v_ETA: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (randomness: t_Slice u8)
      (sampled: usize)
      (out: t_Array i32 (sz 263))
     =
  let (out, sampled), hax_temp_output:((t_Array i32 (sz 263) & usize) & bool) =
    match cast (v_ETA <: usize) <: u8 with
    | 2uy ->
      let tmp0, tmp1, out1:(usize & t_Array i32 (sz 263) & bool) =
        rejection_sample_less_than_eta_equals_2_ #v_SIMDUnit randomness sampled out
      in
      let sampled:usize = tmp0 in
      let out:t_Array i32 (sz 263) = tmp1 in
      (out, sampled <: (t_Array i32 (sz 263) & usize)), out1
      <:
      ((t_Array i32 (sz 263) & usize) & bool)
    | 4uy ->
      let tmp0, tmp1, out1:(usize & t_Array i32 (sz 263) & bool) =
        rejection_sample_less_than_eta_equals_4_ #v_SIMDUnit randomness sampled out
      in
      let sampled:usize = tmp0 in
      let out:t_Array i32 (sz 263) = tmp1 in
      (out, sampled <: (t_Array i32 (sz 263) & usize)), out1
      <:
      ((t_Array i32 (sz 263) & usize) & bool)
    | _ ->
      (out, sampled <: (t_Array i32 (sz 263) & usize)),
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

          <:
          Rust_primitives.Hax.t_Never)
      <:
      ((t_Array i32 (sz 263) & usize) & bool)
  in
  sampled, out, hax_temp_output <: (usize & t_Array i32 (sz 263) & bool)

let rejection_sample_less_than_field_modulus
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (randomness: t_Slice u8)
      (sampled_coefficients: usize)
      (out: t_Array i32 (sz 263))
     =
  let done:bool = false in
  let done, out, sampled_coefficients:(bool & t_Array i32 (sz 263) & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Slice.Iter.t_Chunks
            u8)
          #FStar.Tactics.Typeclasses.solve
          (Core.Slice.impl__chunks #u8 randomness (sz 24) <: Core.Slice.Iter.t_Chunks u8)
        <:
        Core.Slice.Iter.t_Chunks u8)
      (done, out, sampled_coefficients <: (bool & t_Array i32 (sz 263) & usize))
      (fun temp_0_ random_bytes ->
          let done, out, sampled_coefficients:(bool & t_Array i32 (sz 263) & usize) = temp_0_ in
          let random_bytes:t_Slice u8 = random_bytes in
          if ~.done <: bool
          then
            let tmp0, out1:(t_Slice i32 & usize) =
              Libcrux_ml_dsa.Simd.Traits.f_rejection_sample_less_than_field_modulus #v_SIMDUnit
                #FStar.Tactics.Typeclasses.solve
                random_bytes
                (out.[ { Core.Ops.Range.f_start = sampled_coefficients }
                    <:
                    Core.Ops.Range.t_RangeFrom usize ]
                  <:
                  t_Slice i32)
            in
            let out:t_Array i32 (sz 263) =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from out
                ({ Core.Ops.Range.f_start = sampled_coefficients }
                  <:
                  Core.Ops.Range.t_RangeFrom usize)
                tmp0
            in
            let sampled:usize = out1 in
            let sampled_coefficients:usize = sampled_coefficients +! sampled in
            if sampled_coefficients >=. Libcrux_ml_dsa.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
            then
              let done:bool = true in
              done, out, sampled_coefficients <: (bool & t_Array i32 (sz 263) & usize)
            else done, out, sampled_coefficients <: (bool & t_Array i32 (sz 263) & usize)
          else done, out, sampled_coefficients <: (bool & t_Array i32 (sz 263) & usize))
  in
  let hax_temp_output:bool = done in
  sampled_coefficients, out, hax_temp_output <: (usize & t_Array i32 (sz 263) & bool)

let inside_out_shuffle
      (randomness: t_Slice u8)
      (out_index: usize)
      (signs: u64)
      (result: t_Array i32 (sz 256))
     =
  let done:bool = false in
  let done, out_index, result, signs:(bool & usize & t_Array i32 (sz 256) & u64) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(t_Slice u8)
          #FStar.Tactics.Typeclasses.solve
          randomness
        <:
        Core.Slice.Iter.t_Iter u8)
      (done, out_index, result, signs <: (bool & usize & t_Array i32 (sz 256) & u64))
      (fun temp_0_ byte ->
          let done, out_index, result, signs:(bool & usize & t_Array i32 (sz 256) & u64) =
            temp_0_
          in
          let byte:u8 = byte in
          if ~.done <: bool
          then
            let sample_at:usize = cast (byte <: u8) <: usize in
            let out_index, result, signs:(usize & t_Array i32 (sz 256) & u64) =
              if sample_at <=. out_index
              then
                let result:t_Array i32 (sz 256) =
                  Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
                    out_index
                    (result.[ sample_at ] <: i32)
                in
                let out_index:usize = out_index +! sz 1 in
                let result:t_Array i32 (sz 256) =
                  Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
                    sample_at
                    (1l -! (2l *! (cast (signs &. 1uL <: u64) <: i32) <: i32) <: i32)
                in
                let signs:u64 = signs >>! 1l in
                out_index, result, signs <: (usize & t_Array i32 (sz 256) & u64)
              else out_index, result, signs <: (usize & t_Array i32 (sz 256) & u64)
            in
            let done:bool =
              out_index =. (Core.Slice.impl__len #i32 (result <: t_Slice i32) <: usize)
            in
            done, out_index, result, signs <: (bool & usize & t_Array i32 (sz 256) & u64)
          else done, out_index, result, signs <: (bool & usize & t_Array i32 (sz 256) & u64))
  in
  let hax_temp_output:bool = done in
  out_index, signs, result, hax_temp_output <: (usize & u64 & t_Array i32 (sz 256) & bool)

let sample_challenge_ring_element
      (#v_SIMDUnit #v_Shake256: Type0)
      (v_NUMBER_OF_ONES v_SEED_SIZE: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256)
      (seed: t_Array u8 v_SEED_SIZE)
     =
  let state:v_Shake256 =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_init_absorb #v_Shake256
      #FStar.Tactics.Typeclasses.solve
      (seed <: t_Slice u8)
  in
  let tmp0, out:(v_Shake256 & t_Array u8 (sz 136)) =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_squeeze_first_block #v_Shake256
      #FStar.Tactics.Typeclasses.solve
      state
  in
  let state:v_Shake256 = tmp0 in
  let randomness:t_Array u8 (sz 136) = out in
  let signs:u64 =
    Core.Num.impl__u64__from_le_bytes (Core.Result.impl__unwrap #(t_Array u8 (sz 8))
          #Core.Array.t_TryFromSliceError
          (Core.Convert.f_try_into #(t_Slice u8)
              #(t_Array u8 (sz 8))
              #FStar.Tactics.Typeclasses.solve
              (randomness.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 8 }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result (t_Array u8 (sz 8)) Core.Array.t_TryFromSliceError)
        <:
        t_Array u8 (sz 8))
  in
  let result:t_Array i32 (sz 256) = Rust_primitives.Hax.repeat 0l (sz 256) in
  let out_index:usize =
    (Core.Slice.impl__len #i32 (result <: t_Slice i32) <: usize) -! v_NUMBER_OF_ONES
  in
  let tmp0, tmp1, tmp2, out:(usize & u64 & t_Array i32 (sz 256) & bool) =
    inside_out_shuffle (randomness.[ { Core.Ops.Range.f_start = sz 8 }
          <:
          Core.Ops.Range.t_RangeFrom usize ]
        <:
        t_Slice u8)
      out_index
      signs
      result
  in
  let out_index:usize = tmp0 in
  let signs:u64 = tmp1 in
  let result:t_Array i32 (sz 256) = tmp2 in
  let done:bool = out in
  let done, out_index, result, signs, state:(bool & usize & t_Array i32 (sz 256) & u64 & v_Shake256)
  =
    Rust_primitives.f_while_loop (fun temp_0_ ->
          let done, out_index, result, signs, state:(bool & usize & t_Array i32 (sz 256) & u64 &
            v_Shake256) =
            temp_0_
          in
          ~.done <: bool)
      (done, out_index, result, signs, state
        <:
        (bool & usize & t_Array i32 (sz 256) & u64 & v_Shake256))
      (fun temp_0_ ->
          let done, out_index, result, signs, state:(bool & usize & t_Array i32 (sz 256) & u64 &
            v_Shake256) =
            temp_0_
          in
          let tmp0, out:(v_Shake256 & t_Array u8 (sz 136)) =
            Libcrux_ml_dsa.Hash_functions.Shake256.f_squeeze_next_block #v_Shake256
              #FStar.Tactics.Typeclasses.solve
              state
          in
          let state:v_Shake256 = tmp0 in
          let randomness:t_Array u8 (sz 136) = out in
          let tmp0, tmp1, tmp2, out:(usize & u64 & t_Array i32 (sz 256) & bool) =
            inside_out_shuffle (randomness <: t_Slice u8) out_index signs result
          in
          let out_index:usize = tmp0 in
          let signs:u64 = tmp1 in
          let result:t_Array i32 (sz 256) = tmp2 in
          let done:bool = out in
          done, out_index, result, signs, state
          <:
          (bool & usize & t_Array i32 (sz 256) & u64 & v_Shake256))
  in
  Libcrux_ml_dsa.Polynomial.impl__from_i32_array #v_SIMDUnit (result <: t_Slice i32)

let sample_four_error_ring_elements
      (#v_SIMDUnit #v_Shake256: Type0)
      (v_ETA: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256)
      (seed_base: t_Array u8 (sz 66))
      (domain_separator0 domain_separator1 domain_seperator2 domain_separator3: u16)
     =
  let seed0:t_Array u8 (sz 66) = seed_base in
  let seed0:t_Array u8 (sz 66) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seed0
      (sz 64)
      (cast (domain_separator0 <: u16) <: u8)
  in
  let seed0:t_Array u8 (sz 66) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seed0
      (sz 65)
      (cast (domain_separator0 >>! 8l <: u16) <: u8)
  in
  let seed1:t_Array u8 (sz 66) = seed0 in
  let seed1:t_Array u8 (sz 66) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seed1
      (sz 64)
      (cast (domain_separator1 <: u16) <: u8)
  in
  let seed1:t_Array u8 (sz 66) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seed1
      (sz 65)
      (cast (domain_separator1 >>! 8l <: u16) <: u8)
  in
  let seed2:t_Array u8 (sz 66) = seed0 in
  let seed2:t_Array u8 (sz 66) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seed2
      (sz 64)
      (cast (domain_seperator2 <: u16) <: u8)
  in
  let seed2:t_Array u8 (sz 66) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seed2
      (sz 65)
      (cast (domain_seperator2 >>! 8l <: u16) <: u8)
  in
  let seed3:t_Array u8 (sz 66) = seed0 in
  let seed3:t_Array u8 (sz 66) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seed3
      (sz 64)
      (cast (domain_separator3 <: u16) <: u8)
  in
  let seed3:t_Array u8 (sz 66) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seed3
      (sz 65)
      (cast (domain_separator3 >>! 8l <: u16) <: u8)
  in
  let state:v_Shake256 =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_init_absorb_x4 #v_Shake256
      #FStar.Tactics.Typeclasses.solve
      (seed0 <: t_Slice u8)
      (seed1 <: t_Slice u8)
      (seed2 <: t_Slice u8)
      (seed3 <: t_Slice u8)
  in
  let tmp0, out4:(v_Shake256 &
    (t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136))) =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_squeeze_first_block_x4 #v_Shake256
      #FStar.Tactics.Typeclasses.solve
      state
  in
  let state:v_Shake256 = tmp0 in
  let randomnesses:(t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) &
    t_Array u8 (sz 136)) =
    out4
  in
  let out0:t_Array i32 (sz 263) = Rust_primitives.Hax.repeat 0l (sz 263) in
  let out1:t_Array i32 (sz 263) = Rust_primitives.Hax.repeat 0l (sz 263) in
  let out2:t_Array i32 (sz 263) = Rust_primitives.Hax.repeat 0l (sz 263) in
  let out3:t_Array i32 (sz 263) = Rust_primitives.Hax.repeat 0l (sz 263) in
  let sampled0:usize = sz 0 in
  let sampled1:usize = sz 0 in
  let sampled2:usize = sz 0 in
  let sampled3:usize = sz 0 in
  let tmp0, tmp1, out4:(usize & t_Array i32 (sz 263) & bool) =
    rejection_sample_less_than_eta #v_SIMDUnit v_ETA (randomnesses._1 <: t_Slice u8) sampled0 out0
  in
  let sampled0:usize = tmp0 in
  let out0:t_Array i32 (sz 263) = tmp1 in
  let done0:bool = out4 in
  let tmp0, tmp1, out4:(usize & t_Array i32 (sz 263) & bool) =
    rejection_sample_less_than_eta #v_SIMDUnit v_ETA (randomnesses._2 <: t_Slice u8) sampled1 out1
  in
  let sampled1:usize = tmp0 in
  let out1:t_Array i32 (sz 263) = tmp1 in
  let done1:bool = out4 in
  let tmp0, tmp1, out4:(usize & t_Array i32 (sz 263) & bool) =
    rejection_sample_less_than_eta #v_SIMDUnit v_ETA (randomnesses._3 <: t_Slice u8) sampled2 out2
  in
  let sampled2:usize = tmp0 in
  let out2:t_Array i32 (sz 263) = tmp1 in
  let done2:bool = out4 in
  let tmp0, tmp1, out4:(usize & t_Array i32 (sz 263) & bool) =
    rejection_sample_less_than_eta #v_SIMDUnit v_ETA (randomnesses._4 <: t_Slice u8) sampled3 out3
  in
  let sampled3:usize = tmp0 in
  let out3:t_Array i32 (sz 263) = tmp1 in
  let done3:bool = out4 in
  let
  done0, done1, done2, done3, out0, out1, out2, out3, sampled0, sampled1, sampled2, sampled3, state:(
    bool & bool & bool & bool & t_Array i32 (sz 263) & t_Array i32 (sz 263) & t_Array i32 (sz 263) &
    t_Array i32 (sz 263) &
    usize &
    usize &
    usize &
    usize &
    v_Shake256) =
    Rust_primitives.f_while_loop (fun temp_0_ ->
          let
          done0,
          done1,
          done2,
          done3,
          out0,
          out1,
          out2,
          out3,
          sampled0,
          sampled1,
          sampled2,
          sampled3,
          state:(bool & bool & bool & bool & t_Array i32 (sz 263) & t_Array i32 (sz 263) &
            t_Array i32 (sz 263) &
            t_Array i32 (sz 263) &
            usize &
            usize &
            usize &
            usize &
            v_Shake256) =
            temp_0_
          in
          (~.done0 <: bool) || (~.done1 <: bool) || (~.done2 <: bool) || (~.done3 <: bool))
      (done0,
        done1,
        done2,
        done3,
        out0,
        out1,
        out2,
        out3,
        sampled0,
        sampled1,
        sampled2,
        sampled3,
        state
        <:
        (bool & bool & bool & bool & t_Array i32 (sz 263) & t_Array i32 (sz 263) &
          t_Array i32 (sz 263) &
          t_Array i32 (sz 263) &
          usize &
          usize &
          usize &
          usize &
          v_Shake256))
      (fun temp_0_ ->
          let
          done0,
          done1,
          done2,
          done3,
          out0,
          out1,
          out2,
          out3,
          sampled0,
          sampled1,
          sampled2,
          sampled3,
          state:(bool & bool & bool & bool & t_Array i32 (sz 263) & t_Array i32 (sz 263) &
            t_Array i32 (sz 263) &
            t_Array i32 (sz 263) &
            usize &
            usize &
            usize &
            usize &
            v_Shake256) =
            temp_0_
          in
          let tmp0, out4:(v_Shake256 &
            (t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136)))
          =
            Libcrux_ml_dsa.Hash_functions.Shake256.f_squeeze_next_block_x4 #v_Shake256
              #FStar.Tactics.Typeclasses.solve
              state
          in
          let state:v_Shake256 = tmp0 in
          let randomnesses:(t_Array u8 (sz 136) & t_Array u8 (sz 136) & t_Array u8 (sz 136) &
            t_Array u8 (sz 136)) =
            out4
          in
          let done0, out0, sampled0:(bool & t_Array i32 (sz 263) & usize) =
            if ~.done0
            then
              let tmp0, tmp1, out4:(usize & t_Array i32 (sz 263) & bool) =
                rejection_sample_less_than_eta #v_SIMDUnit
                  v_ETA
                  (randomnesses._1 <: t_Slice u8)
                  sampled0
                  out0
              in
              let sampled0:usize = tmp0 in
              let out0:t_Array i32 (sz 263) = tmp1 in
              let done0:bool = out4 in
              done0, out0, sampled0 <: (bool & t_Array i32 (sz 263) & usize)
            else done0, out0, sampled0 <: (bool & t_Array i32 (sz 263) & usize)
          in
          let done1, out1, sampled1:(bool & t_Array i32 (sz 263) & usize) =
            if ~.done1
            then
              let tmp0, tmp1, out4:(usize & t_Array i32 (sz 263) & bool) =
                rejection_sample_less_than_eta #v_SIMDUnit
                  v_ETA
                  (randomnesses._2 <: t_Slice u8)
                  sampled1
                  out1
              in
              let sampled1:usize = tmp0 in
              let out1:t_Array i32 (sz 263) = tmp1 in
              let done1:bool = out4 in
              done1, out1, sampled1 <: (bool & t_Array i32 (sz 263) & usize)
            else done1, out1, sampled1 <: (bool & t_Array i32 (sz 263) & usize)
          in
          let done2, out2, sampled2:(bool & t_Array i32 (sz 263) & usize) =
            if ~.done2
            then
              let tmp0, tmp1, out4:(usize & t_Array i32 (sz 263) & bool) =
                rejection_sample_less_than_eta #v_SIMDUnit
                  v_ETA
                  (randomnesses._3 <: t_Slice u8)
                  sampled2
                  out2
              in
              let sampled2:usize = tmp0 in
              let out2:t_Array i32 (sz 263) = tmp1 in
              let done2:bool = out4 in
              done2, out2, sampled2 <: (bool & t_Array i32 (sz 263) & usize)
            else done2, out2, sampled2 <: (bool & t_Array i32 (sz 263) & usize)
          in
          if ~.done3
          then
            let tmp0, tmp1, out4:(usize & t_Array i32 (sz 263) & bool) =
              rejection_sample_less_than_eta #v_SIMDUnit
                v_ETA
                (randomnesses._4 <: t_Slice u8)
                sampled3
                out3
            in
            let sampled3:usize = tmp0 in
            let out3:t_Array i32 (sz 263) = tmp1 in
            let done3:bool = out4 in
            done0,
            done1,
            done2,
            done3,
            out0,
            out1,
            out2,
            out3,
            sampled0,
            sampled1,
            sampled2,
            sampled3,
            state
            <:
            (bool & bool & bool & bool & t_Array i32 (sz 263) & t_Array i32 (sz 263) &
              t_Array i32 (sz 263) &
              t_Array i32 (sz 263) &
              usize &
              usize &
              usize &
              usize &
              v_Shake256)
          else
            done0,
            done1,
            done2,
            done3,
            out0,
            out1,
            out2,
            out3,
            sampled0,
            sampled1,
            sampled2,
            sampled3,
            state
            <:
            (bool & bool & bool & bool & t_Array i32 (sz 263) & t_Array i32 (sz 263) &
              t_Array i32 (sz 263) &
              t_Array i32 (sz 263) &
              usize &
              usize &
              usize &
              usize &
              v_Shake256))
  in
  Libcrux_ml_dsa.Polynomial.impl__from_i32_array #v_SIMDUnit (out0 <: t_Slice i32),
  Libcrux_ml_dsa.Polynomial.impl__from_i32_array #v_SIMDUnit (out1 <: t_Slice i32),
  Libcrux_ml_dsa.Polynomial.impl__from_i32_array #v_SIMDUnit (out2 <: t_Slice i32),
  Libcrux_ml_dsa.Polynomial.impl__from_i32_array #v_SIMDUnit (out3 <: t_Slice i32)
  <:
  (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)

let sample_four_ring_elements
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (seed0: t_Array u8 (sz 34))
      (domain_separator0 domain_separator1 domain_seperator2 domain_separator3: u16)
     =
  let seed0:t_Array u8 (sz 34) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seed0
      (sz 32)
      (cast (domain_separator0 <: u16) <: u8)
  in
  let seed0:t_Array u8 (sz 34) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seed0
      (sz 33)
      (cast (domain_separator0 >>! 8l <: u16) <: u8)
  in
  let seed1:t_Array u8 (sz 34) = seed0 in
  let seed1:t_Array u8 (sz 34) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seed1
      (sz 32)
      (cast (domain_separator1 <: u16) <: u8)
  in
  let seed1:t_Array u8 (sz 34) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seed1
      (sz 33)
      (cast (domain_separator1 >>! 8l <: u16) <: u8)
  in
  let seed2:t_Array u8 (sz 34) = seed0 in
  let seed2:t_Array u8 (sz 34) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seed2
      (sz 32)
      (cast (domain_seperator2 <: u16) <: u8)
  in
  let seed2:t_Array u8 (sz 34) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seed2
      (sz 33)
      (cast (domain_seperator2 >>! 8l <: u16) <: u8)
  in
  let seed3:t_Array u8 (sz 34) = seed0 in
  let seed3:t_Array u8 (sz 34) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seed3
      (sz 32)
      (cast (domain_separator3 <: u16) <: u8)
  in
  let seed3:t_Array u8 (sz 34) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seed3
      (sz 33)
      (cast (domain_separator3 >>! 8l <: u16) <: u8)
  in
  let state:Libcrux_ml_dsa.Hash_functions.Portable.t_Shake128X4 =
    Libcrux_ml_dsa.Hash_functions.Shake128.f_init_absorb #Libcrux_ml_dsa.Hash_functions.Portable.t_Shake128X4
      #FStar.Tactics.Typeclasses.solve
      (seed0 <: t_Slice u8)
      (seed1 <: t_Slice u8)
      (seed2 <: t_Slice u8)
      (seed3 <: t_Slice u8)
  in
  let randomness0:t_Array u8 (sz 840) = Rust_primitives.Hax.repeat 0uy (sz 840) in
  let randomness1:t_Array u8 (sz 840) = Rust_primitives.Hax.repeat 0uy (sz 840) in
  let randomness2:t_Array u8 (sz 840) = Rust_primitives.Hax.repeat 0uy (sz 840) in
  let randomness3:t_Array u8 (sz 840) = Rust_primitives.Hax.repeat 0uy (sz 840) in
  let tmp0, tmp1, tmp2, tmp3, tmp4:(Libcrux_ml_dsa.Hash_functions.Portable.t_Shake128X4 &
    t_Array u8 (sz 840) &
    t_Array u8 (sz 840) &
    t_Array u8 (sz 840) &
    t_Array u8 (sz 840)) =
    Libcrux_ml_dsa.Hash_functions.Shake128.f_squeeze_first_five_blocks #Libcrux_ml_dsa.Hash_functions.Portable.t_Shake128X4
      #FStar.Tactics.Typeclasses.solve
      state
      randomness0
      randomness1
      randomness2
      randomness3
  in
  let state:Libcrux_ml_dsa.Hash_functions.Portable.t_Shake128X4 = tmp0 in
  let randomness0:t_Array u8 (sz 840) = tmp1 in
  let randomness1:t_Array u8 (sz 840) = tmp2 in
  let randomness2:t_Array u8 (sz 840) = tmp3 in
  let randomness3:t_Array u8 (sz 840) = tmp4 in
  let _:Prims.unit = () in
  let coefficients0:t_Array i32 (sz 263) = Rust_primitives.Hax.repeat 0l (sz 263) in
  let coefficients1:t_Array i32 (sz 263) = Rust_primitives.Hax.repeat 0l (sz 263) in
  let coefficients2:t_Array i32 (sz 263) = Rust_primitives.Hax.repeat 0l (sz 263) in
  let coefficients3:t_Array i32 (sz 263) = Rust_primitives.Hax.repeat 0l (sz 263) in
  let sampled0:usize = sz 0 in
  let sampled1:usize = sz 0 in
  let sampled2:usize = sz 0 in
  let sampled3:usize = sz 0 in
  let tmp0, tmp1, out:(usize & t_Array i32 (sz 263) & bool) =
    rejection_sample_less_than_field_modulus #v_SIMDUnit
      (randomness0 <: t_Slice u8)
      sampled0
      coefficients0
  in
  let sampled0:usize = tmp0 in
  let coefficients0:t_Array i32 (sz 263) = tmp1 in
  let done0:bool = out in
  let tmp0, tmp1, out:(usize & t_Array i32 (sz 263) & bool) =
    rejection_sample_less_than_field_modulus #v_SIMDUnit
      (randomness1 <: t_Slice u8)
      sampled1
      coefficients1
  in
  let sampled1:usize = tmp0 in
  let coefficients1:t_Array i32 (sz 263) = tmp1 in
  let done1:bool = out in
  let tmp0, tmp1, out:(usize & t_Array i32 (sz 263) & bool) =
    rejection_sample_less_than_field_modulus #v_SIMDUnit
      (randomness2 <: t_Slice u8)
      sampled2
      coefficients2
  in
  let sampled2:usize = tmp0 in
  let coefficients2:t_Array i32 (sz 263) = tmp1 in
  let done2:bool = out in
  let tmp0, tmp1, out:(usize & t_Array i32 (sz 263) & bool) =
    rejection_sample_less_than_field_modulus #v_SIMDUnit
      (randomness3 <: t_Slice u8)
      sampled3
      coefficients3
  in
  let sampled3:usize = tmp0 in
  let coefficients3:t_Array i32 (sz 263) = tmp1 in
  let done3:bool = out in
  let
  coefficients0,
  coefficients1,
  coefficients2,
  coefficients3,
  done0,
  done1,
  done2,
  done3,
  sampled0,
  sampled1,
  sampled2,
  sampled3,
  state:(t_Array i32 (sz 263) & t_Array i32 (sz 263) & t_Array i32 (sz 263) & t_Array i32 (sz 263) &
    bool &
    bool &
    bool &
    bool &
    usize &
    usize &
    usize &
    usize &
    Libcrux_ml_dsa.Hash_functions.Portable.t_Shake128X4) =
    Rust_primitives.f_while_loop (fun temp_0_ ->
          let
          coefficients0,
          coefficients1,
          coefficients2,
          coefficients3,
          done0,
          done1,
          done2,
          done3,
          sampled0,
          sampled1,
          sampled2,
          sampled3,
          state:(t_Array i32 (sz 263) & t_Array i32 (sz 263) & t_Array i32 (sz 263) &
            t_Array i32 (sz 263) &
            bool &
            bool &
            bool &
            bool &
            usize &
            usize &
            usize &
            usize &
            Libcrux_ml_dsa.Hash_functions.Portable.t_Shake128X4) =
            temp_0_
          in
          (~.done0 <: bool) || (~.done1 <: bool) || (~.done2 <: bool) || (~.done3 <: bool))
      (coefficients0,
        coefficients1,
        coefficients2,
        coefficients3,
        done0,
        done1,
        done2,
        done3,
        sampled0,
        sampled1,
        sampled2,
        sampled3,
        state
        <:
        (t_Array i32 (sz 263) & t_Array i32 (sz 263) & t_Array i32 (sz 263) & t_Array i32 (sz 263) &
          bool &
          bool &
          bool &
          bool &
          usize &
          usize &
          usize &
          usize &
          Libcrux_ml_dsa.Hash_functions.Portable.t_Shake128X4))
      (fun temp_0_ ->
          let
          coefficients0,
          coefficients1,
          coefficients2,
          coefficients3,
          done0,
          done1,
          done2,
          done3,
          sampled0,
          sampled1,
          sampled2,
          sampled3,
          state:(t_Array i32 (sz 263) & t_Array i32 (sz 263) & t_Array i32 (sz 263) &
            t_Array i32 (sz 263) &
            bool &
            bool &
            bool &
            bool &
            usize &
            usize &
            usize &
            usize &
            Libcrux_ml_dsa.Hash_functions.Portable.t_Shake128X4) =
            temp_0_
          in
          let tmp0, out:(Libcrux_ml_dsa.Hash_functions.Portable.t_Shake128X4 &
            (t_Array u8 (sz 168) & t_Array u8 (sz 168) & t_Array u8 (sz 168) & t_Array u8 (sz 168)))
          =
            Libcrux_ml_dsa.Hash_functions.Shake128.f_squeeze_next_block #Libcrux_ml_dsa.Hash_functions.Portable.t_Shake128X4
              #FStar.Tactics.Typeclasses.solve
              state
          in
          let state:Libcrux_ml_dsa.Hash_functions.Portable.t_Shake128X4 = tmp0 in
          let randomnesses:(t_Array u8 (sz 168) & t_Array u8 (sz 168) & t_Array u8 (sz 168) &
            t_Array u8 (sz 168)) =
            out
          in
          let coefficients0, done0, sampled0:(t_Array i32 (sz 263) & bool & usize) =
            if ~.done0
            then
              let tmp0, tmp1, out:(usize & t_Array i32 (sz 263) & bool) =
                rejection_sample_less_than_field_modulus #v_SIMDUnit
                  (randomnesses._1 <: t_Slice u8)
                  sampled0
                  coefficients0
              in
              let sampled0:usize = tmp0 in
              let coefficients0:t_Array i32 (sz 263) = tmp1 in
              let done0:bool = out in
              coefficients0, done0, sampled0 <: (t_Array i32 (sz 263) & bool & usize)
            else coefficients0, done0, sampled0 <: (t_Array i32 (sz 263) & bool & usize)
          in
          let coefficients1, done1, sampled1:(t_Array i32 (sz 263) & bool & usize) =
            if ~.done1
            then
              let tmp0, tmp1, out:(usize & t_Array i32 (sz 263) & bool) =
                rejection_sample_less_than_field_modulus #v_SIMDUnit
                  (randomnesses._2 <: t_Slice u8)
                  sampled1
                  coefficients1
              in
              let sampled1:usize = tmp0 in
              let coefficients1:t_Array i32 (sz 263) = tmp1 in
              let done1:bool = out in
              coefficients1, done1, sampled1 <: (t_Array i32 (sz 263) & bool & usize)
            else coefficients1, done1, sampled1 <: (t_Array i32 (sz 263) & bool & usize)
          in
          let coefficients2, done2, sampled2:(t_Array i32 (sz 263) & bool & usize) =
            if ~.done2
            then
              let tmp0, tmp1, out:(usize & t_Array i32 (sz 263) & bool) =
                rejection_sample_less_than_field_modulus #v_SIMDUnit
                  (randomnesses._3 <: t_Slice u8)
                  sampled2
                  coefficients2
              in
              let sampled2:usize = tmp0 in
              let coefficients2:t_Array i32 (sz 263) = tmp1 in
              let done2:bool = out in
              coefficients2, done2, sampled2 <: (t_Array i32 (sz 263) & bool & usize)
            else coefficients2, done2, sampled2 <: (t_Array i32 (sz 263) & bool & usize)
          in
          if ~.done3
          then
            let tmp0, tmp1, out:(usize & t_Array i32 (sz 263) & bool) =
              rejection_sample_less_than_field_modulus #v_SIMDUnit
                (randomnesses._4 <: t_Slice u8)
                sampled3
                coefficients3
            in
            let sampled3:usize = tmp0 in
            let coefficients3:t_Array i32 (sz 263) = tmp1 in
            let done3:bool = out in
            coefficients0,
            coefficients1,
            coefficients2,
            coefficients3,
            done0,
            done1,
            done2,
            done3,
            sampled0,
            sampled1,
            sampled2,
            sampled3,
            state
            <:
            (t_Array i32 (sz 263) & t_Array i32 (sz 263) & t_Array i32 (sz 263) &
              t_Array i32 (sz 263) &
              bool &
              bool &
              bool &
              bool &
              usize &
              usize &
              usize &
              usize &
              Libcrux_ml_dsa.Hash_functions.Portable.t_Shake128X4)
          else
            coefficients0,
            coefficients1,
            coefficients2,
            coefficients3,
            done0,
            done1,
            done2,
            done3,
            sampled0,
            sampled1,
            sampled2,
            sampled3,
            state
            <:
            (t_Array i32 (sz 263) & t_Array i32 (sz 263) & t_Array i32 (sz 263) &
              t_Array i32 (sz 263) &
              bool &
              bool &
              bool &
              bool &
              usize &
              usize &
              usize &
              usize &
              Libcrux_ml_dsa.Hash_functions.Portable.t_Shake128X4))
  in
  Libcrux_ml_dsa.Polynomial.impl__from_i32_array #v_SIMDUnit (coefficients0 <: t_Slice i32),
  Libcrux_ml_dsa.Polynomial.impl__from_i32_array #v_SIMDUnit (coefficients1 <: t_Slice i32),
  Libcrux_ml_dsa.Polynomial.impl__from_i32_array #v_SIMDUnit (coefficients2 <: t_Slice i32),
  Libcrux_ml_dsa.Polynomial.impl__from_i32_array #v_SIMDUnit (coefficients3 <: t_Slice i32)
  <:
  (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit &
    Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)

let sample_mask_ring_element
      (#v_SIMDUnit #v_Shake256: Type0)
      (v_GAMMA1_EXPONENT: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256)
      (seed: t_Array u8 (sz 66))
     =
  match cast (v_GAMMA1_EXPONENT <: usize) <: u8 with
  | 17uy ->
    let out:t_Array u8 (sz 576) = Rust_primitives.Hax.repeat 0uy (sz 576) in
    let out:t_Array u8 (sz 576) =
      Libcrux_ml_dsa.Hash_functions.Shake256.f_shake256 #v_Shake256
        #FStar.Tactics.Typeclasses.solve
        (sz 576)
        (seed <: t_Slice u8)
        out
    in
    Libcrux_ml_dsa.Encoding.Gamma1.deserialize #v_SIMDUnit v_GAMMA1_EXPONENT (out <: t_Slice u8)
  | 19uy ->
    let out:t_Array u8 (sz 640) = Rust_primitives.Hax.repeat 0uy (sz 640) in
    let out:t_Array u8 (sz 640) =
      Libcrux_ml_dsa.Hash_functions.Shake256.f_shake256 #v_Shake256
        #FStar.Tactics.Typeclasses.solve
        (sz 640)
        (seed <: t_Slice u8)
        out
    in
    Libcrux_ml_dsa.Encoding.Gamma1.deserialize #v_SIMDUnit v_GAMMA1_EXPONENT (out <: t_Slice u8)
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let sample_mask_vector
      (#v_SIMDUnit #v_Shake256 #v_Shake256X4: Type0)
      (v_DIMENSION v_GAMMA1_EXPONENT: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i4:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_Xof v_Shake256)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i5:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4)
      (seed: t_Array u8 (sz 66))
      (domain_separator: u16)
     =
  let mask:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION =
    Rust_primitives.Hax.repeat (Libcrux_ml_dsa.Polynomial.impl__ZERO #v_SIMDUnit ()
        <:
        Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      v_DIMENSION
  in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((v_DIMENSION =. sz 4 <: bool) || (v_DIMENSION =. sz 5 <: bool) ||
            (v_DIMENSION =. sz 7 <: bool))
      in
      ()
  in
  let tmp0, out4:(u16 & t_Array u8 (sz 66)) = update_seed seed domain_separator in
  let domain_separator:u16 = tmp0 in
  let seed0:t_Array u8 (sz 66) = out4 in
  let tmp0, out4:(u16 & t_Array u8 (sz 66)) = update_seed seed domain_separator in
  let domain_separator:u16 = tmp0 in
  let seed1:t_Array u8 (sz 66) = out4 in
  let tmp0, out4:(u16 & t_Array u8 (sz 66)) = update_seed seed domain_separator in
  let domain_separator:u16 = tmp0 in
  let seed2:t_Array u8 (sz 66) = out4 in
  let tmp0, out4:(u16 & t_Array u8 (sz 66)) = update_seed seed domain_separator in
  let domain_separator:u16 = tmp0 in
  let seed3:t_Array u8 (sz 66) = out4 in
  let mask:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION =
    match cast (v_GAMMA1_EXPONENT <: usize) <: u8 with
    | 17uy ->
      let out0:t_Array u8 (sz 576) = Rust_primitives.Hax.repeat 0uy (sz 576) in
      let out1:t_Array u8 (sz 576) = Rust_primitives.Hax.repeat 0uy (sz 576) in
      let out2:t_Array u8 (sz 576) = Rust_primitives.Hax.repeat 0uy (sz 576) in
      let out3:t_Array u8 (sz 576) = Rust_primitives.Hax.repeat 0uy (sz 576) in
      let tmp0, tmp1, tmp2, tmp3:(t_Array u8 (sz 576) & t_Array u8 (sz 576) & t_Array u8 (sz 576) &
        t_Array u8 (sz 576)) =
        Libcrux_ml_dsa.Hash_functions.Shake256.f_shake256_x4 #v_Shake256X4
          #FStar.Tactics.Typeclasses.solve (sz 576) (seed0 <: t_Slice u8) (seed1 <: t_Slice u8)
          (seed2 <: t_Slice u8) (seed3 <: t_Slice u8) out0 out1 out2 out3
      in
      let out0:t_Array u8 (sz 576) = tmp0 in
      let out1:t_Array u8 (sz 576) = tmp1 in
      let out2:t_Array u8 (sz 576) = tmp2 in
      let out3:t_Array u8 (sz 576) = tmp3 in
      let _:Prims.unit = () in
      let mask:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize mask
          (sz 0)
          (Libcrux_ml_dsa.Encoding.Gamma1.deserialize #v_SIMDUnit
              v_GAMMA1_EXPONENT
              (out0 <: t_Slice u8)
            <:
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      in
      let mask:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize mask
          (sz 1)
          (Libcrux_ml_dsa.Encoding.Gamma1.deserialize #v_SIMDUnit
              v_GAMMA1_EXPONENT
              (out1 <: t_Slice u8)
            <:
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      in
      let mask:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize mask
          (sz 2)
          (Libcrux_ml_dsa.Encoding.Gamma1.deserialize #v_SIMDUnit
              v_GAMMA1_EXPONENT
              (out2 <: t_Slice u8)
            <:
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      in
      let mask:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize mask
          (sz 3)
          (Libcrux_ml_dsa.Encoding.Gamma1.deserialize #v_SIMDUnit
              v_GAMMA1_EXPONENT
              (out3 <: t_Slice u8)
            <:
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      in
      mask
    | 19uy ->
      let out0:t_Array u8 (sz 640) = Rust_primitives.Hax.repeat 0uy (sz 640) in
      let out1:t_Array u8 (sz 640) = Rust_primitives.Hax.repeat 0uy (sz 640) in
      let out2:t_Array u8 (sz 640) = Rust_primitives.Hax.repeat 0uy (sz 640) in
      let out3:t_Array u8 (sz 640) = Rust_primitives.Hax.repeat 0uy (sz 640) in
      let tmp0, tmp1, tmp2, tmp3:(t_Array u8 (sz 640) & t_Array u8 (sz 640) & t_Array u8 (sz 640) &
        t_Array u8 (sz 640)) =
        Libcrux_ml_dsa.Hash_functions.Shake256.f_shake256_x4 #v_Shake256X4
          #FStar.Tactics.Typeclasses.solve (sz 640) (seed0 <: t_Slice u8) (seed1 <: t_Slice u8)
          (seed2 <: t_Slice u8) (seed3 <: t_Slice u8) out0 out1 out2 out3
      in
      let out0:t_Array u8 (sz 640) = tmp0 in
      let out1:t_Array u8 (sz 640) = tmp1 in
      let out2:t_Array u8 (sz 640) = tmp2 in
      let out3:t_Array u8 (sz 640) = tmp3 in
      let _:Prims.unit = () in
      let mask:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize mask
          (sz 0)
          (Libcrux_ml_dsa.Encoding.Gamma1.deserialize #v_SIMDUnit
              v_GAMMA1_EXPONENT
              (out0 <: t_Slice u8)
            <:
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      in
      let mask:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize mask
          (sz 1)
          (Libcrux_ml_dsa.Encoding.Gamma1.deserialize #v_SIMDUnit
              v_GAMMA1_EXPONENT
              (out1 <: t_Slice u8)
            <:
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      in
      let mask:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize mask
          (sz 2)
          (Libcrux_ml_dsa.Encoding.Gamma1.deserialize #v_SIMDUnit
              v_GAMMA1_EXPONENT
              (out2 <: t_Slice u8)
            <:
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      in
      let mask:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize mask
          (sz 3)
          (Libcrux_ml_dsa.Encoding.Gamma1.deserialize #v_SIMDUnit
              v_GAMMA1_EXPONENT
              (out3 <: t_Slice u8)
            <:
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      in
      mask
    | _ -> mask
  in
  let domain_separator, mask, seed:(u16 &
    t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION &
    t_Array u8 (sz 66)) =
    Rust_primitives.Hax.Folds.fold_range (sz 4)
      v_DIMENSION
      (fun temp_0_ temp_1_ ->
          let domain_separator, mask, seed:(u16 &
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION &
            t_Array u8 (sz 66)) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (domain_separator, mask, seed
        <:
        (u16 & t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION &
          t_Array u8 (sz 66)))
      (fun temp_0_ i ->
          let domain_separator, mask, seed:(u16 &
            t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION &
            t_Array u8 (sz 66)) =
            temp_0_
          in
          let i:usize = i in
          let seed:t_Array u8 (sz 66) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seed
              (sz 64)
              (cast (domain_separator <: u16) <: u8)
          in
          let seed:t_Array u8 (sz 66) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seed
              (sz 65)
              (cast (domain_separator >>! 8l <: u16) <: u8)
          in
          let domain_separator:u16 = domain_separator +! 1us in
          let mask:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            v_DIMENSION =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize mask
              i
              (sample_mask_ring_element #v_SIMDUnit #v_Shake256 v_GAMMA1_EXPONENT seed
                <:
                Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          in
          domain_separator, mask, seed
          <:
          (u16 & t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION &
            t_Array u8 (sz 66)))
  in
  let hax_temp_output:t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    v_DIMENSION =
    mask
  in
  domain_separator, hax_temp_output
  <:
  (u16 & t_Array (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) v_DIMENSION)
