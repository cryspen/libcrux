module Libcrux_ml_dsa.Sample
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Hash_functions.Shake128 in
  let open Libcrux_ml_dsa.Hash_functions.Shake256 in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

let generate_domain_separator (row, column: (u8 & u8)) =
  (cast (column <: u8) <: u16) |. ((cast (row <: u8) <: u16) <<! mk_i32 8 <: u16)

let sample_up_to_four_ring_elements_flat__xy (index width: usize) =
  (cast (index /! width <: usize) <: u8), (cast (index %! width <: usize) <: u8) <: (u8 & u8)

let add_domain_separator (slice: t_Slice u8) (indices: (u8 & u8)) =
  let out:t_Array u8 (mk_usize 34) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 34) in
  let out:t_Array u8 (mk_usize 34) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
      ({
          Core.Ops.Range.f_start = mk_usize 0;
          Core.Ops.Range.f_end = Core.Slice.impl__len #u8 slice <: usize
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (out.[ {
                Core.Ops.Range.f_start = mk_usize 0;
                Core.Ops.Range.f_end = Core.Slice.impl__len #u8 slice <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          slice
        <:
        t_Slice u8)
  in
  let domain_separator:u16 = generate_domain_separator indices in
  let out:t_Array u8 (mk_usize 34) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
      (mk_usize 32)
      (cast (domain_separator <: u16) <: u8)
  in
  let out:t_Array u8 (mk_usize 34) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
      (mk_usize 33)
      (cast (domain_separator >>! mk_i32 8 <: u16) <: u8)
  in
  out

let add_error_domain_separator (slice: t_Slice u8) (domain_separator: u16) =
  let out:t_Array u8 (mk_usize 66) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 66) in
  let out:t_Array u8 (mk_usize 66) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
      ({
          Core.Ops.Range.f_start = mk_usize 0;
          Core.Ops.Range.f_end = Core.Slice.impl__len #u8 slice <: usize
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (out.[ {
                Core.Ops.Range.f_start = mk_usize 0;
                Core.Ops.Range.f_end = Core.Slice.impl__len #u8 slice <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          slice
        <:
        t_Slice u8)
  in
  let out:t_Array u8 (mk_usize 66) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
      (mk_usize 64)
      (cast (domain_separator <: u16) <: u8)
  in
  let out:t_Array u8 (mk_usize 66) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
      (mk_usize 65)
      (cast (domain_separator >>! mk_i32 8 <: u16) <: u8)
  in
  out

let rejection_sample_less_than_eta_equals_2_
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (randomness: t_Slice u8)
      (sampled_coefficients: usize)
      (out: t_Array i32 (mk_usize 263))
     =
  let done:bool = false in
  let done, out, sampled_coefficients:(bool & t_Array i32 (mk_usize 263) & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Slice.Iter.t_ChunksExact
            u8)
          #FStar.Tactics.Typeclasses.solve
          (Core.Slice.impl__chunks_exact #u8 randomness (mk_usize 4)
            <:
            Core.Slice.Iter.t_ChunksExact u8)
        <:
        Core.Slice.Iter.t_ChunksExact u8)
      (done, out, sampled_coefficients <: (bool & t_Array i32 (mk_usize 263) & usize))
      (fun temp_0_ random_bytes ->
          let done, out, sampled_coefficients:(bool & t_Array i32 (mk_usize 263) & usize) =
            temp_0_
          in
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
            let out:t_Array i32 (mk_usize 263) =
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
              done, out, sampled_coefficients <: (bool & t_Array i32 (mk_usize 263) & usize)
            else done, out, sampled_coefficients <: (bool & t_Array i32 (mk_usize 263) & usize)
          else done, out, sampled_coefficients <: (bool & t_Array i32 (mk_usize 263) & usize))
  in
  let hax_temp_output:bool = done in
  sampled_coefficients, out, hax_temp_output <: (usize & t_Array i32 (mk_usize 263) & bool)

let rejection_sample_less_than_eta_equals_4_
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (randomness: t_Slice u8)
      (sampled_coefficients: usize)
      (out: t_Array i32 (mk_usize 263))
     =
  let done:bool = false in
  let done, out, sampled_coefficients:(bool & t_Array i32 (mk_usize 263) & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Slice.Iter.t_ChunksExact
            u8)
          #FStar.Tactics.Typeclasses.solve
          (Core.Slice.impl__chunks_exact #u8 randomness (mk_usize 4)
            <:
            Core.Slice.Iter.t_ChunksExact u8)
        <:
        Core.Slice.Iter.t_ChunksExact u8)
      (done, out, sampled_coefficients <: (bool & t_Array i32 (mk_usize 263) & usize))
      (fun temp_0_ random_bytes ->
          let done, out, sampled_coefficients:(bool & t_Array i32 (mk_usize 263) & usize) =
            temp_0_
          in
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
            let out:t_Array i32 (mk_usize 263) =
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
              done, out, sampled_coefficients <: (bool & t_Array i32 (mk_usize 263) & usize)
            else done, out, sampled_coefficients <: (bool & t_Array i32 (mk_usize 263) & usize)
          else done, out, sampled_coefficients <: (bool & t_Array i32 (mk_usize 263) & usize))
  in
  let hax_temp_output:bool = done in
  sampled_coefficients, out, hax_temp_output <: (usize & t_Array i32 (mk_usize 263) & bool)

let rejection_sample_less_than_eta
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (eta: Libcrux_ml_dsa.Constants.t_Eta)
      (randomness: t_Slice u8)
      (sampled: usize)
      (out: t_Array i32 (mk_usize 263))
     =
  let (out, sampled), hax_temp_output:((t_Array i32 (mk_usize 263) & usize) & bool) =
    match eta <: Libcrux_ml_dsa.Constants.t_Eta with
    | Libcrux_ml_dsa.Constants.Eta_Two  ->
      let tmp0, tmp1, out1:(usize & t_Array i32 (mk_usize 263) & bool) =
        rejection_sample_less_than_eta_equals_2_ #v_SIMDUnit randomness sampled out
      in
      let sampled:usize = tmp0 in
      let out:t_Array i32 (mk_usize 263) = tmp1 in
      (out, sampled <: (t_Array i32 (mk_usize 263) & usize)), out1
      <:
      ((t_Array i32 (mk_usize 263) & usize) & bool)
    | Libcrux_ml_dsa.Constants.Eta_Four  ->
      let tmp0, tmp1, out1:(usize & t_Array i32 (mk_usize 263) & bool) =
        rejection_sample_less_than_eta_equals_4_ #v_SIMDUnit randomness sampled out
      in
      let sampled:usize = tmp0 in
      let out:t_Array i32 (mk_usize 263) = tmp1 in
      (out, sampled <: (t_Array i32 (mk_usize 263) & usize)), out1
      <:
      ((t_Array i32 (mk_usize 263) & usize) & bool)
  in
  sampled, out, hax_temp_output <: (usize & t_Array i32 (mk_usize 263) & bool)

let rejection_sample_less_than_field_modulus
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (randomness: t_Slice u8)
      (sampled_coefficients: usize)
      (out: t_Array i32 (mk_usize 263))
     =
  let done:bool = false in
  let done, out, sampled_coefficients:(bool & t_Array i32 (mk_usize 263) & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Slice.Iter.t_ChunksExact
            u8)
          #FStar.Tactics.Typeclasses.solve
          (Core.Slice.impl__chunks_exact #u8 randomness (mk_usize 24)
            <:
            Core.Slice.Iter.t_ChunksExact u8)
        <:
        Core.Slice.Iter.t_ChunksExact u8)
      (done, out, sampled_coefficients <: (bool & t_Array i32 (mk_usize 263) & usize))
      (fun temp_0_ random_bytes ->
          let done, out, sampled_coefficients:(bool & t_Array i32 (mk_usize 263) & usize) =
            temp_0_
          in
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
            let out:t_Array i32 (mk_usize 263) =
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
              done, out, sampled_coefficients <: (bool & t_Array i32 (mk_usize 263) & usize)
            else done, out, sampled_coefficients <: (bool & t_Array i32 (mk_usize 263) & usize)
          else done, out, sampled_coefficients <: (bool & t_Array i32 (mk_usize 263) & usize))
  in
  let hax_temp_output:bool = done in
  sampled_coefficients, out, hax_temp_output <: (usize & t_Array i32 (mk_usize 263) & bool)

let inside_out_shuffle
      (randomness: t_Slice u8)
      (out_index: usize)
      (signs: u64)
      (result: t_Array i32 (mk_usize 256))
     =
  let done:bool = false in
  let done, out_index, result, signs:(bool & usize & t_Array i32 (mk_usize 256) & u64) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Slice.Iter.t_Iter
            u8)
          #FStar.Tactics.Typeclasses.solve
          (Core.Slice.impl__iter #u8 randomness <: Core.Slice.Iter.t_Iter u8)
        <:
        Core.Slice.Iter.t_Iter u8)
      (done, out_index, result, signs <: (bool & usize & t_Array i32 (mk_usize 256) & u64))
      (fun temp_0_ byte ->
          let done, out_index, result, signs:(bool & usize & t_Array i32 (mk_usize 256) & u64) =
            temp_0_
          in
          let byte:u8 = byte in
          if ~.done <: bool
          then
            let sample_at:usize = cast (byte <: u8) <: usize in
            let out_index, result, signs:(usize & t_Array i32 (mk_usize 256) & u64) =
              if sample_at <=. out_index
              then
                let result:t_Array i32 (mk_usize 256) =
                  Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
                    out_index
                    (result.[ sample_at ] <: i32)
                in
                let out_index:usize = out_index +! mk_usize 1 in
                let result:t_Array i32 (mk_usize 256) =
                  Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
                    sample_at
                    (mk_i32 1 -! (mk_i32 2 *! (cast (signs &. mk_u64 1 <: u64) <: i32) <: i32)
                      <:
                      i32)
                in
                let signs:u64 = signs >>! mk_i32 1 in
                out_index, result, signs <: (usize & t_Array i32 (mk_usize 256) & u64)
              else out_index, result, signs <: (usize & t_Array i32 (mk_usize 256) & u64)
            in
            let done:bool =
              out_index =. (Core.Slice.impl__len #i32 (result <: t_Slice i32) <: usize)
            in
            done, out_index, result, signs <: (bool & usize & t_Array i32 (mk_usize 256) & u64)
          else done, out_index, result, signs <: (bool & usize & t_Array i32 (mk_usize 256) & u64))
  in
  let hax_temp_output:bool = done in
  out_index, signs, result, hax_temp_output <: (usize & u64 & t_Array i32 (mk_usize 256) & bool)

let sample_challenge_ring_element
      (#v_SIMDUnit #v_Shake256: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256)
      (seed: t_Slice u8)
      (number_of_ones: usize)
      (re: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
     =
  let state:v_Shake256 =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_init_absorb_final #v_Shake256
      #FStar.Tactics.Typeclasses.solve
      seed
  in
  let tmp0, out:(v_Shake256 & t_Array u8 (mk_usize 136)) =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_squeeze_first_block #v_Shake256
      #FStar.Tactics.Typeclasses.solve
      state
  in
  let state:v_Shake256 = tmp0 in
  let randomness:t_Array u8 (mk_usize 136) = out in
  let signs:u64 =
    Core.Num.impl__u64__from_le_bytes (Core.Result.impl__unwrap #(t_Array u8 (mk_usize 8))
          #Core.Array.t_TryFromSliceError
          (Core.Convert.f_try_into #(t_Slice u8)
              #(t_Array u8 (mk_usize 8))
              #FStar.Tactics.Typeclasses.solve
              (randomness.[ {
                    Core.Ops.Range.f_start = mk_usize 0;
                    Core.Ops.Range.f_end = mk_usize 8
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result (t_Array u8 (mk_usize 8)) Core.Array.t_TryFromSliceError)
        <:
        t_Array u8 (mk_usize 8))
  in
  let result:t_Array i32 (mk_usize 256) = Rust_primitives.Hax.repeat (mk_i32 0) (mk_usize 256) in
  let out_index:usize =
    (Core.Slice.impl__len #i32 (result <: t_Slice i32) <: usize) -! number_of_ones
  in
  let tmp0, tmp1, tmp2, out:(usize & u64 & t_Array i32 (mk_usize 256) & bool) =
    inside_out_shuffle (randomness.[ { Core.Ops.Range.f_start = mk_usize 8 }
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
  let result:t_Array i32 (mk_usize 256) = tmp2 in
  let done:bool = out in
  let done, out_index, result, signs, state:(bool & usize & t_Array i32 (mk_usize 256) & u64 &
    v_Shake256) =
    Rust_primitives.f_while_loop (fun temp_0_ ->
          let done, out_index, result, signs, state:(bool & usize & t_Array i32 (mk_usize 256) & u64 &
            v_Shake256) =
            temp_0_
          in
          ~.done <: bool)
      (done, out_index, result, signs, state
        <:
        (bool & usize & t_Array i32 (mk_usize 256) & u64 & v_Shake256))
      (fun temp_0_ ->
          let done, out_index, result, signs, state:(bool & usize & t_Array i32 (mk_usize 256) & u64 &
            v_Shake256) =
            temp_0_
          in
          let tmp0, out:(v_Shake256 & t_Array u8 (mk_usize 136)) =
            Libcrux_ml_dsa.Hash_functions.Shake256.f_squeeze_next_block #v_Shake256
              #FStar.Tactics.Typeclasses.solve
              state
          in
          let state:v_Shake256 = tmp0 in
          let randomness:t_Array u8 (mk_usize 136) = out in
          let tmp0, tmp1, tmp2, out:(usize & u64 & t_Array i32 (mk_usize 256) & bool) =
            inside_out_shuffle (randomness <: t_Slice u8) out_index signs result
          in
          let out_index:usize = tmp0 in
          let signs:u64 = tmp1 in
          let result:t_Array i32 (mk_usize 256) = tmp2 in
          let done:bool = out in
          done, out_index, result, signs, state
          <:
          (bool & usize & t_Array i32 (mk_usize 256) & u64 & v_Shake256))
  in
  let re:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    Libcrux_ml_dsa.Polynomial.impl__from_i32_array #v_SIMDUnit (result <: t_Slice i32) re
  in
  re

let sample_four_error_ring_elements
      (#v_SIMDUnit #v_Shake256: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256)
      (eta: Libcrux_ml_dsa.Constants.t_Eta)
      (seed: t_Slice u8)
      (start_index: u16)
      (re: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
     =
  let seed0:t_Array u8 (mk_usize 66) = add_error_domain_separator seed start_index in
  let seed1:t_Array u8 (mk_usize 66) =
    add_error_domain_separator seed (start_index +! mk_u16 1 <: u16)
  in
  let seed2:t_Array u8 (mk_usize 66) =
    add_error_domain_separator seed (start_index +! mk_u16 2 <: u16)
  in
  let seed3:t_Array u8 (mk_usize 66) =
    add_error_domain_separator seed (start_index +! mk_u16 3 <: u16)
  in
  let state:v_Shake256 =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_init_absorb_x4 #v_Shake256
      #FStar.Tactics.Typeclasses.solve
      (seed0 <: t_Slice u8)
      (seed1 <: t_Slice u8)
      (seed2 <: t_Slice u8)
      (seed3 <: t_Slice u8)
  in
  let tmp0, out1:(v_Shake256 &
    (t_Array u8 (mk_usize 136) & t_Array u8 (mk_usize 136) & t_Array u8 (mk_usize 136) &
      t_Array u8 (mk_usize 136))) =
    Libcrux_ml_dsa.Hash_functions.Shake256.f_squeeze_first_block_x4 #v_Shake256
      #FStar.Tactics.Typeclasses.solve
      state
  in
  let state:v_Shake256 = tmp0 in
  let randomnesses:(t_Array u8 (mk_usize 136) & t_Array u8 (mk_usize 136) &
    t_Array u8 (mk_usize 136) &
    t_Array u8 (mk_usize 136)) =
    out1
  in
  let out:t_Array (t_Array i32 (mk_usize 263)) (mk_usize 4) =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat (mk_i32 0) (mk_usize 263)
        <:
        t_Array i32 (mk_usize 263))
      (mk_usize 4)
  in
  let sampled0:usize = mk_usize 0 in
  let sampled1:usize = mk_usize 0 in
  let sampled2:usize = mk_usize 0 in
  let sampled3:usize = mk_usize 0 in
  let tmp0, tmp1, out1:(usize & t_Array i32 (mk_usize 263) & bool) =
    rejection_sample_less_than_eta #v_SIMDUnit
      eta
      (randomnesses._1 <: t_Slice u8)
      sampled0
      (out.[ mk_usize 0 ] <: t_Array i32 (mk_usize 263))
  in
  let sampled0:usize = tmp0 in
  let out:t_Array (t_Array i32 (mk_usize 263)) (mk_usize 4) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 0) tmp1
  in
  let done0:bool = out1 in
  let tmp0, tmp1, out1:(usize & t_Array i32 (mk_usize 263) & bool) =
    rejection_sample_less_than_eta #v_SIMDUnit
      eta
      (randomnesses._2 <: t_Slice u8)
      sampled1
      (out.[ mk_usize 1 ] <: t_Array i32 (mk_usize 263))
  in
  let sampled1:usize = tmp0 in
  let out:t_Array (t_Array i32 (mk_usize 263)) (mk_usize 4) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 1) tmp1
  in
  let done1:bool = out1 in
  let tmp0, tmp1, out1:(usize & t_Array i32 (mk_usize 263) & bool) =
    rejection_sample_less_than_eta #v_SIMDUnit
      eta
      (randomnesses._3 <: t_Slice u8)
      sampled2
      (out.[ mk_usize 2 ] <: t_Array i32 (mk_usize 263))
  in
  let sampled2:usize = tmp0 in
  let out:t_Array (t_Array i32 (mk_usize 263)) (mk_usize 4) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 2) tmp1
  in
  let done2:bool = out1 in
  let tmp0, tmp1, out1:(usize & t_Array i32 (mk_usize 263) & bool) =
    rejection_sample_less_than_eta #v_SIMDUnit
      eta
      (randomnesses._4 <: t_Slice u8)
      sampled3
      (out.[ mk_usize 3 ] <: t_Array i32 (mk_usize 263))
  in
  let sampled3:usize = tmp0 in
  let out:t_Array (t_Array i32 (mk_usize 263)) (mk_usize 4) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 3) tmp1
  in
  let done3:bool = out1 in
  let done0, done1, done2, done3, out, sampled0, sampled1, sampled2, sampled3, state:(bool & bool &
    bool &
    bool &
    t_Array (t_Array i32 (mk_usize 263)) (mk_usize 4) &
    usize &
    usize &
    usize &
    usize &
    v_Shake256) =
    Rust_primitives.f_while_loop (fun temp_0_ ->
          let done0, done1, done2, done3, out, sampled0, sampled1, sampled2, sampled3, state:(bool &
            bool &
            bool &
            bool &
            t_Array (t_Array i32 (mk_usize 263)) (mk_usize 4) &
            usize &
            usize &
            usize &
            usize &
            v_Shake256) =
            temp_0_
          in
          (~.done0 <: bool) || (~.done1 <: bool) || (~.done2 <: bool) || (~.done3 <: bool))
      (done0, done1, done2, done3, out, sampled0, sampled1, sampled2, sampled3, state
        <:
        (bool & bool & bool & bool & t_Array (t_Array i32 (mk_usize 263)) (mk_usize 4) & usize &
          usize &
          usize &
          usize &
          v_Shake256))
      (fun temp_0_ ->
          let done0, done1, done2, done3, out, sampled0, sampled1, sampled2, sampled3, state:(bool &
            bool &
            bool &
            bool &
            t_Array (t_Array i32 (mk_usize 263)) (mk_usize 4) &
            usize &
            usize &
            usize &
            usize &
            v_Shake256) =
            temp_0_
          in
          let tmp0, out1:(v_Shake256 &
            (t_Array u8 (mk_usize 136) & t_Array u8 (mk_usize 136) & t_Array u8 (mk_usize 136) &
              t_Array u8 (mk_usize 136))) =
            Libcrux_ml_dsa.Hash_functions.Shake256.f_squeeze_next_block_x4 #v_Shake256
              #FStar.Tactics.Typeclasses.solve
              state
          in
          let state:v_Shake256 = tmp0 in
          let randomnesses:(t_Array u8 (mk_usize 136) & t_Array u8 (mk_usize 136) &
            t_Array u8 (mk_usize 136) &
            t_Array u8 (mk_usize 136)) =
            out1
          in
          let done0, out, sampled0:(bool & t_Array (t_Array i32 (mk_usize 263)) (mk_usize 4) & usize
          ) =
            if ~.done0
            then
              let tmp0, tmp1, out1:(usize & t_Array i32 (mk_usize 263) & bool) =
                rejection_sample_less_than_eta #v_SIMDUnit
                  eta
                  (randomnesses._1 <: t_Slice u8)
                  sampled0
                  (out.[ mk_usize 0 ] <: t_Array i32 (mk_usize 263))
              in
              let sampled0:usize = tmp0 in
              let out:t_Array (t_Array i32 (mk_usize 263)) (mk_usize 4) =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 0) tmp1
              in
              let done0:bool = out1 in
              done0, out, sampled0
              <:
              (bool & t_Array (t_Array i32 (mk_usize 263)) (mk_usize 4) & usize)
            else
              done0, out, sampled0
              <:
              (bool & t_Array (t_Array i32 (mk_usize 263)) (mk_usize 4) & usize)
          in
          let done1, out, sampled1:(bool & t_Array (t_Array i32 (mk_usize 263)) (mk_usize 4) & usize
          ) =
            if ~.done1
            then
              let tmp0, tmp1, out1:(usize & t_Array i32 (mk_usize 263) & bool) =
                rejection_sample_less_than_eta #v_SIMDUnit
                  eta
                  (randomnesses._2 <: t_Slice u8)
                  sampled1
                  (out.[ mk_usize 1 ] <: t_Array i32 (mk_usize 263))
              in
              let sampled1:usize = tmp0 in
              let out:t_Array (t_Array i32 (mk_usize 263)) (mk_usize 4) =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 1) tmp1
              in
              let done1:bool = out1 in
              done1, out, sampled1
              <:
              (bool & t_Array (t_Array i32 (mk_usize 263)) (mk_usize 4) & usize)
            else
              done1, out, sampled1
              <:
              (bool & t_Array (t_Array i32 (mk_usize 263)) (mk_usize 4) & usize)
          in
          let done2, out, sampled2:(bool & t_Array (t_Array i32 (mk_usize 263)) (mk_usize 4) & usize
          ) =
            if ~.done2
            then
              let tmp0, tmp1, out1:(usize & t_Array i32 (mk_usize 263) & bool) =
                rejection_sample_less_than_eta #v_SIMDUnit
                  eta
                  (randomnesses._3 <: t_Slice u8)
                  sampled2
                  (out.[ mk_usize 2 ] <: t_Array i32 (mk_usize 263))
              in
              let sampled2:usize = tmp0 in
              let out:t_Array (t_Array i32 (mk_usize 263)) (mk_usize 4) =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 2) tmp1
              in
              let done2:bool = out1 in
              done2, out, sampled2
              <:
              (bool & t_Array (t_Array i32 (mk_usize 263)) (mk_usize 4) & usize)
            else
              done2, out, sampled2
              <:
              (bool & t_Array (t_Array i32 (mk_usize 263)) (mk_usize 4) & usize)
          in
          if ~.done3
          then
            let tmp0, tmp1, out1:(usize & t_Array i32 (mk_usize 263) & bool) =
              rejection_sample_less_than_eta #v_SIMDUnit
                eta
                (randomnesses._4 <: t_Slice u8)
                sampled3
                (out.[ mk_usize 3 ] <: t_Array i32 (mk_usize 263))
            in
            let sampled3:usize = tmp0 in
            let out:t_Array (t_Array i32 (mk_usize 263)) (mk_usize 4) =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (mk_usize 3) tmp1
            in
            let done3:bool = out1 in
            done0, done1, done2, done3, out, sampled0, sampled1, sampled2, sampled3, state
            <:
            (bool & bool & bool & bool & t_Array (t_Array i32 (mk_usize 263)) (mk_usize 4) & usize &
              usize &
              usize &
              usize &
              v_Shake256)
          else
            done0, done1, done2, done3, out, sampled0, sampled1, sampled2, sampled3, state
            <:
            (bool & bool & bool & bool & t_Array (t_Array i32 (mk_usize 263)) (mk_usize 4) & usize &
              usize &
              usize &
              usize &
              v_Shake256))
  in
  let max:usize = (cast (start_index <: u16) <: usize) +! mk_usize 4 in
  let max:usize =
    if
      (Core.Slice.impl__len #(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) re
        <:
        usize) <.
      max
    then Core.Slice.impl__len #(Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) re
    else max
  in
  let re:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Rust_primitives.Hax.Folds.fold_range (cast (start_index <: u16) <: usize)
      max
      (fun re temp_1_ ->
          let re:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) = re in
          let _:usize = temp_1_ in
          true)
      re
      (fun re i ->
          let re:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) = re in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
            i
            (Libcrux_ml_dsa.Polynomial.impl__from_i32_array #v_SIMDUnit
                (out.[ i %! mk_usize 4 <: usize ] <: t_Slice i32)
                (re.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
              <:
              Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          <:
          t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
  in
  re

let sample_mask_ring_element
      (#v_SIMDUnit #v_Shake256: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256)
      (seed: t_Array u8 (mk_usize 66))
      (result: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      (gamma1_exponent: usize)
     =
  let result:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
    match cast (gamma1_exponent <: usize) <: u8 with
    | Rust_primitives.Integers.MkInt 17 ->
      let out:t_Array u8 (mk_usize 576) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 576) in
      let out:t_Array u8 (mk_usize 576) =
        Libcrux_ml_dsa.Hash_functions.Shake256.f_shake256 #v_Shake256
          #FStar.Tactics.Typeclasses.solve
          (mk_usize 576)
          (seed <: t_Slice u8)
          out
      in
      let result:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
        Libcrux_ml_dsa.Encoding.Gamma1.deserialize #v_SIMDUnit
          gamma1_exponent
          (out <: t_Slice u8)
          result
      in
      result
    | Rust_primitives.Integers.MkInt 19 ->
      let out:t_Array u8 (mk_usize 640) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 640) in
      let out:t_Array u8 (mk_usize 640) =
        Libcrux_ml_dsa.Hash_functions.Shake256.f_shake256 #v_Shake256
          #FStar.Tactics.Typeclasses.solve
          (mk_usize 640)
          (seed <: t_Slice u8)
          out
      in
      let result:Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit =
        Libcrux_ml_dsa.Encoding.Gamma1.deserialize #v_SIMDUnit
          gamma1_exponent
          (out <: t_Slice u8)
          result
      in
      result
    | _ -> result
  in
  result

let sample_mask_vector
      (#v_SIMDUnit #v_Shake256 #v_Shake256X4: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i4:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_DsaXof v_Shake256)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i5:
          Libcrux_ml_dsa.Hash_functions.Shake256.t_XofX4 v_Shake256X4)
      (dimension gamma1_exponent: usize)
      (seed: t_Array u8 (mk_usize 64))
      (domain_separator: u16)
      (mask: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((dimension =. mk_usize 4 <: bool) || (dimension =. mk_usize 5 <: bool) ||
            (dimension =. mk_usize 7 <: bool))
      in
      ()
  in
  let seed0:t_Array u8 (mk_usize 66) =
    add_error_domain_separator (seed <: t_Slice u8) domain_separator
  in
  let seed1:t_Array u8 (mk_usize 66) =
    add_error_domain_separator (seed <: t_Slice u8) (domain_separator +! mk_u16 1 <: u16)
  in
  let seed2:t_Array u8 (mk_usize 66) =
    add_error_domain_separator (seed <: t_Slice u8) (domain_separator +! mk_u16 2 <: u16)
  in
  let seed3:t_Array u8 (mk_usize 66) =
    add_error_domain_separator (seed <: t_Slice u8) (domain_separator +! mk_u16 3 <: u16)
  in
  let domain_separator:u16 = domain_separator +! mk_u16 4 in
  let mask:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    match cast (gamma1_exponent <: usize) <: u8 with
    | Rust_primitives.Integers.MkInt 17 ->
      let out0:t_Array u8 (mk_usize 576) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 576) in
      let out1:t_Array u8 (mk_usize 576) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 576) in
      let out2:t_Array u8 (mk_usize 576) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 576) in
      let out3:t_Array u8 (mk_usize 576) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 576) in
      let tmp0, tmp1, tmp2, tmp3:(t_Array u8 (mk_usize 576) & t_Array u8 (mk_usize 576) &
        t_Array u8 (mk_usize 576) &
        t_Array u8 (mk_usize 576)) =
        Libcrux_ml_dsa.Hash_functions.Shake256.f_shake256_x4 #v_Shake256X4
          #FStar.Tactics.Typeclasses.solve (mk_usize 576) (seed0 <: t_Slice u8)
          (seed1 <: t_Slice u8) (seed2 <: t_Slice u8) (seed3 <: t_Slice u8) out0 out1 out2 out3
      in
      let out0:t_Array u8 (mk_usize 576) = tmp0 in
      let out1:t_Array u8 (mk_usize 576) = tmp1 in
      let out2:t_Array u8 (mk_usize 576) = tmp2 in
      let out3:t_Array u8 (mk_usize 576) = tmp3 in
      let _:Prims.unit = () in
      let mask:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize mask
          (mk_usize 0)
          (Libcrux_ml_dsa.Encoding.Gamma1.deserialize #v_SIMDUnit
              gamma1_exponent
              (out0 <: t_Slice u8)
              (mask.[ mk_usize 0 ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            <:
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      in
      let mask:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize mask
          (mk_usize 1)
          (Libcrux_ml_dsa.Encoding.Gamma1.deserialize #v_SIMDUnit
              gamma1_exponent
              (out1 <: t_Slice u8)
              (mask.[ mk_usize 1 ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            <:
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      in
      let mask:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize mask
          (mk_usize 2)
          (Libcrux_ml_dsa.Encoding.Gamma1.deserialize #v_SIMDUnit
              gamma1_exponent
              (out2 <: t_Slice u8)
              (mask.[ mk_usize 2 ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            <:
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      in
      let mask:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize mask
          (mk_usize 3)
          (Libcrux_ml_dsa.Encoding.Gamma1.deserialize #v_SIMDUnit
              gamma1_exponent
              (out3 <: t_Slice u8)
              (mask.[ mk_usize 3 ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            <:
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      in
      mask
    | Rust_primitives.Integers.MkInt 19 ->
      let out0:t_Array u8 (mk_usize 640) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 640) in
      let out1:t_Array u8 (mk_usize 640) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 640) in
      let out2:t_Array u8 (mk_usize 640) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 640) in
      let out3:t_Array u8 (mk_usize 640) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 640) in
      let tmp0, tmp1, tmp2, tmp3:(t_Array u8 (mk_usize 640) & t_Array u8 (mk_usize 640) &
        t_Array u8 (mk_usize 640) &
        t_Array u8 (mk_usize 640)) =
        Libcrux_ml_dsa.Hash_functions.Shake256.f_shake256_x4 #v_Shake256X4
          #FStar.Tactics.Typeclasses.solve (mk_usize 640) (seed0 <: t_Slice u8)
          (seed1 <: t_Slice u8) (seed2 <: t_Slice u8) (seed3 <: t_Slice u8) out0 out1 out2 out3
      in
      let out0:t_Array u8 (mk_usize 640) = tmp0 in
      let out1:t_Array u8 (mk_usize 640) = tmp1 in
      let out2:t_Array u8 (mk_usize 640) = tmp2 in
      let out3:t_Array u8 (mk_usize 640) = tmp3 in
      let _:Prims.unit = () in
      let mask:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize mask
          (mk_usize 0)
          (Libcrux_ml_dsa.Encoding.Gamma1.deserialize #v_SIMDUnit
              gamma1_exponent
              (out0 <: t_Slice u8)
              (mask.[ mk_usize 0 ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            <:
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      in
      let mask:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize mask
          (mk_usize 1)
          (Libcrux_ml_dsa.Encoding.Gamma1.deserialize #v_SIMDUnit
              gamma1_exponent
              (out1 <: t_Slice u8)
              (mask.[ mk_usize 1 ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            <:
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      in
      let mask:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize mask
          (mk_usize 2)
          (Libcrux_ml_dsa.Encoding.Gamma1.deserialize #v_SIMDUnit
              gamma1_exponent
              (out2 <: t_Slice u8)
              (mask.[ mk_usize 2 ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            <:
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      in
      let mask:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize mask
          (mk_usize 3)
          (Libcrux_ml_dsa.Encoding.Gamma1.deserialize #v_SIMDUnit
              gamma1_exponent
              (out3 <: t_Slice u8)
              (mask.[ mk_usize 3 ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
            <:
            Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      in
      mask
    | _ -> mask
  in
  let domain_separator, mask:(u16 &
    t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 4)
      dimension
      (fun temp_0_ temp_1_ ->
          let domain_separator, mask:(u16 &
            t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (domain_separator, mask
        <:
        (u16 & t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)))
      (fun temp_0_ i ->
          let domain_separator, mask:(u16 &
            t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)) =
            temp_0_
          in
          let i:usize = i in
          let seed:t_Array u8 (mk_usize 66) =
            add_error_domain_separator (seed <: t_Slice u8) domain_separator
          in
          let domain_separator:u16 = domain_separator +! mk_u16 1 in
          let mask:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize mask
              i
              (sample_mask_ring_element #v_SIMDUnit
                  #v_Shake256
                  seed
                  (mask.[ i ] <: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
                  gamma1_exponent
                <:
                Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          in
          domain_separator, mask
          <:
          (u16 & t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)))
  in
  domain_separator, mask
  <:
  (u16 & t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))

let sample_up_to_four_ring_elements_flat
      (#v_SIMDUnit #v_Shake128: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_dsa.Hash_functions.Shake128.t_XofX4 v_Shake128)
      (columns: usize)
      (seed: t_Slice u8)
      (matrix: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (rand_stack0 rand_stack1 rand_stack2 rand_stack3: t_Array u8 (mk_usize 840))
      (tmp_stack: t_Slice (t_Array i32 (mk_usize 263)))
      (start_index elements_requested: usize)
     =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit = Hax_lib.v_assert (elements_requested <=. mk_usize 4 <: bool) in
      ()
  in
  let seed0:t_Array u8 (mk_usize 34) =
    add_domain_separator seed
      (sample_up_to_four_ring_elements_flat__xy start_index columns <: (u8 & u8))
  in
  let seed1:t_Array u8 (mk_usize 34) =
    add_domain_separator seed
      (sample_up_to_four_ring_elements_flat__xy (start_index +! mk_usize 1 <: usize) columns
        <:
        (u8 & u8))
  in
  let seed2:t_Array u8 (mk_usize 34) =
    add_domain_separator seed
      (sample_up_to_four_ring_elements_flat__xy (start_index +! mk_usize 2 <: usize) columns
        <:
        (u8 & u8))
  in
  let seed3:t_Array u8 (mk_usize 34) =
    add_domain_separator seed
      (sample_up_to_four_ring_elements_flat__xy (start_index +! mk_usize 3 <: usize) columns
        <:
        (u8 & u8))
  in
  let state:v_Shake128 =
    Libcrux_ml_dsa.Hash_functions.Shake128.f_init_absorb #v_Shake128
      #FStar.Tactics.Typeclasses.solve
      (seed0 <: t_Slice u8)
      (seed1 <: t_Slice u8)
      (seed2 <: t_Slice u8)
      (seed3 <: t_Slice u8)
  in
  let tmp0, tmp1, tmp2, tmp3, tmp4:(v_Shake128 & t_Array u8 (mk_usize 840) &
    t_Array u8 (mk_usize 840) &
    t_Array u8 (mk_usize 840) &
    t_Array u8 (mk_usize 840)) =
    Libcrux_ml_dsa.Hash_functions.Shake128.f_squeeze_first_five_blocks #v_Shake128
      #FStar.Tactics.Typeclasses.solve
      state
      rand_stack0
      rand_stack1
      rand_stack2
      rand_stack3
  in
  let state:v_Shake128 = tmp0 in
  let rand_stack0:t_Array u8 (mk_usize 840) = tmp1 in
  let rand_stack1:t_Array u8 (mk_usize 840) = tmp2 in
  let rand_stack2:t_Array u8 (mk_usize 840) = tmp3 in
  let rand_stack3:t_Array u8 (mk_usize 840) = tmp4 in
  let _:Prims.unit = () in
  let sampled0:usize = mk_usize 0 in
  let sampled1:usize = mk_usize 0 in
  let sampled2:usize = mk_usize 0 in
  let sampled3:usize = mk_usize 0 in
  let tmp0, tmp1, out:(usize & t_Array i32 (mk_usize 263) & bool) =
    rejection_sample_less_than_field_modulus #v_SIMDUnit
      (rand_stack0 <: t_Slice u8)
      sampled0
      (tmp_stack.[ mk_usize 0 ] <: t_Array i32 (mk_usize 263))
  in
  let sampled0:usize = tmp0 in
  let tmp_stack:t_Slice (t_Array i32 (mk_usize 263)) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize tmp_stack (mk_usize 0) tmp1
  in
  let done0:bool = out in
  let tmp0, tmp1, out:(usize & t_Array i32 (mk_usize 263) & bool) =
    rejection_sample_less_than_field_modulus #v_SIMDUnit
      (rand_stack1 <: t_Slice u8)
      sampled1
      (tmp_stack.[ mk_usize 1 ] <: t_Array i32 (mk_usize 263))
  in
  let sampled1:usize = tmp0 in
  let tmp_stack:t_Slice (t_Array i32 (mk_usize 263)) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize tmp_stack (mk_usize 1) tmp1
  in
  let done1:bool = out in
  let tmp0, tmp1, out:(usize & t_Array i32 (mk_usize 263) & bool) =
    rejection_sample_less_than_field_modulus #v_SIMDUnit
      (rand_stack2 <: t_Slice u8)
      sampled2
      (tmp_stack.[ mk_usize 2 ] <: t_Array i32 (mk_usize 263))
  in
  let sampled2:usize = tmp0 in
  let tmp_stack:t_Slice (t_Array i32 (mk_usize 263)) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize tmp_stack (mk_usize 2) tmp1
  in
  let done2:bool = out in
  let tmp0, tmp1, out:(usize & t_Array i32 (mk_usize 263) & bool) =
    rejection_sample_less_than_field_modulus #v_SIMDUnit
      (rand_stack3 <: t_Slice u8)
      sampled3
      (tmp_stack.[ mk_usize 3 ] <: t_Array i32 (mk_usize 263))
  in
  let sampled3:usize = tmp0 in
  let tmp_stack:t_Slice (t_Array i32 (mk_usize 263)) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize tmp_stack (mk_usize 3) tmp1
  in
  let done3:bool = out in
  let done0, done1, done2, done3, sampled0, sampled1, sampled2, sampled3, state, tmp_stack:(bool &
    bool &
    bool &
    bool &
    usize &
    usize &
    usize &
    usize &
    v_Shake128 &
    t_Slice (t_Array i32 (mk_usize 263))) =
    Rust_primitives.f_while_loop (fun temp_0_ ->
          let done0, done1, done2, done3, sampled0, sampled1, sampled2, sampled3, state, tmp_stack:(bool &
            bool &
            bool &
            bool &
            usize &
            usize &
            usize &
            usize &
            v_Shake128 &
            t_Slice (t_Array i32 (mk_usize 263))) =
            temp_0_
          in
          (~.done0 <: bool) || (~.done1 <: bool) || (~.done2 <: bool) || (~.done3 <: bool))
      (done0, done1, done2, done3, sampled0, sampled1, sampled2, sampled3, state, tmp_stack
        <:
        (bool & bool & bool & bool & usize & usize & usize & usize & v_Shake128 &
          t_Slice (t_Array i32 (mk_usize 263))))
      (fun temp_0_ ->
          let done0, done1, done2, done3, sampled0, sampled1, sampled2, sampled3, state, tmp_stack:(bool &
            bool &
            bool &
            bool &
            usize &
            usize &
            usize &
            usize &
            v_Shake128 &
            t_Slice (t_Array i32 (mk_usize 263))) =
            temp_0_
          in
          let tmp0, out:(v_Shake128 &
            (t_Array u8 (mk_usize 168) & t_Array u8 (mk_usize 168) & t_Array u8 (mk_usize 168) &
              t_Array u8 (mk_usize 168))) =
            Libcrux_ml_dsa.Hash_functions.Shake128.f_squeeze_next_block #v_Shake128
              #FStar.Tactics.Typeclasses.solve
              state
          in
          let state:v_Shake128 = tmp0 in
          let randomnesses:(t_Array u8 (mk_usize 168) & t_Array u8 (mk_usize 168) &
            t_Array u8 (mk_usize 168) &
            t_Array u8 (mk_usize 168)) =
            out
          in
          let done0, sampled0, tmp_stack:(bool & usize & t_Slice (t_Array i32 (mk_usize 263))) =
            if ~.done0
            then
              let tmp0, tmp1, out:(usize & t_Array i32 (mk_usize 263) & bool) =
                rejection_sample_less_than_field_modulus #v_SIMDUnit
                  (randomnesses._1 <: t_Slice u8)
                  sampled0
                  (tmp_stack.[ mk_usize 0 ] <: t_Array i32 (mk_usize 263))
              in
              let sampled0:usize = tmp0 in
              let tmp_stack:t_Slice (t_Array i32 (mk_usize 263)) =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize tmp_stack
                  (mk_usize 0)
                  tmp1
              in
              let done0:bool = out in
              done0, sampled0, tmp_stack <: (bool & usize & t_Slice (t_Array i32 (mk_usize 263)))
            else done0, sampled0, tmp_stack <: (bool & usize & t_Slice (t_Array i32 (mk_usize 263)))
          in
          let done1, sampled1, tmp_stack:(bool & usize & t_Slice (t_Array i32 (mk_usize 263))) =
            if ~.done1
            then
              let tmp0, tmp1, out:(usize & t_Array i32 (mk_usize 263) & bool) =
                rejection_sample_less_than_field_modulus #v_SIMDUnit
                  (randomnesses._2 <: t_Slice u8)
                  sampled1
                  (tmp_stack.[ mk_usize 1 ] <: t_Array i32 (mk_usize 263))
              in
              let sampled1:usize = tmp0 in
              let tmp_stack:t_Slice (t_Array i32 (mk_usize 263)) =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize tmp_stack
                  (mk_usize 1)
                  tmp1
              in
              let done1:bool = out in
              done1, sampled1, tmp_stack <: (bool & usize & t_Slice (t_Array i32 (mk_usize 263)))
            else done1, sampled1, tmp_stack <: (bool & usize & t_Slice (t_Array i32 (mk_usize 263)))
          in
          let done2, sampled2, tmp_stack:(bool & usize & t_Slice (t_Array i32 (mk_usize 263))) =
            if ~.done2
            then
              let tmp0, tmp1, out:(usize & t_Array i32 (mk_usize 263) & bool) =
                rejection_sample_less_than_field_modulus #v_SIMDUnit
                  (randomnesses._3 <: t_Slice u8)
                  sampled2
                  (tmp_stack.[ mk_usize 2 ] <: t_Array i32 (mk_usize 263))
              in
              let sampled2:usize = tmp0 in
              let tmp_stack:t_Slice (t_Array i32 (mk_usize 263)) =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize tmp_stack
                  (mk_usize 2)
                  tmp1
              in
              let done2:bool = out in
              done2, sampled2, tmp_stack <: (bool & usize & t_Slice (t_Array i32 (mk_usize 263)))
            else done2, sampled2, tmp_stack <: (bool & usize & t_Slice (t_Array i32 (mk_usize 263)))
          in
          if ~.done3
          then
            let tmp0, tmp1, out:(usize & t_Array i32 (mk_usize 263) & bool) =
              rejection_sample_less_than_field_modulus #v_SIMDUnit
                (randomnesses._4 <: t_Slice u8)
                sampled3
                (tmp_stack.[ mk_usize 3 ] <: t_Array i32 (mk_usize 263))
            in
            let sampled3:usize = tmp0 in
            let tmp_stack:t_Slice (t_Array i32 (mk_usize 263)) =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize tmp_stack
                (mk_usize 3)
                tmp1
            in
            let done3:bool = out in
            done0, done1, done2, done3, sampled0, sampled1, sampled2, sampled3, state, tmp_stack
            <:
            (bool & bool & bool & bool & usize & usize & usize & usize & v_Shake128 &
              t_Slice (t_Array i32 (mk_usize 263)))
          else
            done0, done1, done2, done3, sampled0, sampled1, sampled2, sampled3, state, tmp_stack
            <:
            (bool & bool & bool & bool & usize & usize & usize & usize & v_Shake128 &
              t_Slice (t_Array i32 (mk_usize 263))))
  in
  let matrix:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      elements_requested
      (fun matrix temp_1_ ->
          let matrix:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
            matrix
          in
          let _:usize = temp_1_ in
          true)
      matrix
      (fun matrix k ->
          let matrix:t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) =
            matrix
          in
          let k:usize = k in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize matrix
            (start_index +! k <: usize)
            (Libcrux_ml_dsa.Polynomial.impl__from_i32_array #v_SIMDUnit
                (tmp_stack.[ k ] <: t_Slice i32)
                (matrix.[ start_index +! k <: usize ]
                  <:
                  Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
              <:
              Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
          <:
          t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
  in
  matrix, rand_stack0, rand_stack1, rand_stack2, rand_stack3, tmp_stack
  <:
  (t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit) &
    t_Array u8 (mk_usize 840) &
    t_Array u8 (mk_usize 840) &
    t_Array u8 (mk_usize 840) &
    t_Array u8 (mk_usize 840) &
    t_Slice (t_Array i32 (mk_usize 263)))
