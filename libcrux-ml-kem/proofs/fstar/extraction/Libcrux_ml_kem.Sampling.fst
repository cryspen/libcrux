module Libcrux_ml_kem.Sampling
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let sample_from_uniform_distribution_next
      (v_K v_N: usize)
      (randomness: t_Array (t_Array u8 v_N) v_K)
      (sampled_coefficients: t_Array usize v_K)
      (out: t_Array (t_Array i32 (sz 256)) v_K)
     =
  let done:bool = true in
  let done, out, sampled_coefficients:(bool & t_Array (t_Array i32 (sz 256)) v_K & t_Array usize v_K
  ) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      (done, out, sampled_coefficients
        <:
        (bool & t_Array (t_Array i32 (sz 256)) v_K & t_Array usize v_K))
      (fun temp_0_ i ->
          let done, out, sampled_coefficients:(bool & t_Array (t_Array i32 (sz 256)) v_K &
            t_Array usize v_K) =
            temp_0_
          in
          let i:usize = i in
          let out, sampled_coefficients:(t_Array (t_Array i32 (sz 256)) v_K & t_Array usize v_K) =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Slice.impl__chunks
                      (Rust_primitives.unsize (randomness.[ i ] <: t_Array u8 v_N) <: t_Slice u8)
                      (sz 3)
                    <:
                    Core.Slice.Iter.t_Chunks u8)
                <:
                Core.Slice.Iter.t_Chunks u8)
              (out, sampled_coefficients <: (t_Array (t_Array i32 (sz 256)) v_K & t_Array usize v_K)
              )
              (fun temp_0_ bytes ->
                  let out, sampled_coefficients:(t_Array (t_Array i32 (sz 256)) v_K &
                    t_Array usize v_K) =
                    temp_0_
                  in
                  let bytes:t_Slice u8 = bytes in
                  let b1:i32 = cast (bytes.[ sz 0 ] <: u8) <: i32 in
                  let b2:i32 = cast (bytes.[ sz 1 ] <: u8) <: i32 in
                  let b3:i32 = cast (bytes.[ sz 2 ] <: u8) <: i32 in
                  let d1:i32 = ((b2 &. 15l <: i32) <<! 8l <: i32) |. b1 in
                  let d2:i32 = (b3 <<! 4l <: i32) |. (b2 >>! 4l <: i32) in
                  let out, sampled_coefficients:(t_Array (t_Array i32 (sz 256)) v_K &
                    t_Array usize v_K) =
                    if
                      d1 <. Libcrux_ml_kem.Constants.v_FIELD_MODULUS &&
                      (sampled_coefficients.[ i ] <: usize) <.
                      Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
                    then
                      let out:t_Array (t_Array i32 (sz 256)) v_K =
                        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                          i
                          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (out.[ i ]
                                <:
                                t_Array i32 (sz 256))
                              (sampled_coefficients.[ i ] <: usize)
                              d1
                            <:
                            t_Array i32 (sz 256))
                      in
                      out,
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize sampled_coefficients
                        i
                        ((sampled_coefficients.[ i ] <: usize) +! sz 1 <: usize)
                      <:
                      (t_Array (t_Array i32 (sz 256)) v_K & t_Array usize v_K)
                    else
                      out, sampled_coefficients
                      <:
                      (t_Array (t_Array i32 (sz 256)) v_K & t_Array usize v_K)
                  in
                  if
                    d2 <. Libcrux_ml_kem.Constants.v_FIELD_MODULUS &&
                    (sampled_coefficients.[ i ] <: usize) <.
                    Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
                  then
                    let out:t_Array (t_Array i32 (sz 256)) v_K =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                        i
                        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (out.[ i ]
                              <:
                              t_Array i32 (sz 256))
                            (sampled_coefficients.[ i ] <: usize)
                            d2
                          <:
                          t_Array i32 (sz 256))
                    in
                    let sampled_coefficients:t_Array usize v_K =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize sampled_coefficients
                        i
                        ((sampled_coefficients.[ i ] <: usize) +! sz 1 <: usize)
                    in
                    out, sampled_coefficients
                    <:
                    (t_Array (t_Array i32 (sz 256)) v_K & t_Array usize v_K)
                  else
                    out, sampled_coefficients
                    <:
                    (t_Array (t_Array i32 (sz 256)) v_K & t_Array usize v_K))
          in
          if
            (sampled_coefficients.[ i ] <: usize) <.
            Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
          then
            false, out, sampled_coefficients
            <:
            (bool & t_Array (t_Array i32 (sz 256)) v_K & t_Array usize v_K)
          else
            done, out, sampled_coefficients
            <:
            (bool & t_Array (t_Array i32 (sz 256)) v_K & t_Array usize v_K))
  in
  let hax_temp_output:bool = done in
  sampled_coefficients, out, hax_temp_output
  <:
  (t_Array usize v_K & t_Array (t_Array i32 (sz 256)) v_K & bool)

let sample_from_binomial_distribution_2_ (randomness: t_Slice u8) =
  let sampled_i32s:t_Array i32 (sz 256) = Rust_primitives.Hax.repeat 0l (sz 256) in
  let sampled_i32s:t_Array i32 (sz 256) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact randomness (sz 4) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      sampled_i32s
      (fun sampled_i32s temp_1_ ->
          let sampled_i32s:t_Array i32 (sz 256) = sampled_i32s in
          let chunk_number, byte_chunk:(usize & t_Slice u8) = temp_1_ in
          let (random_bits_as_u32: u32):u32 =
            (((cast (byte_chunk.[ sz 0 ] <: u8) <: u32) |.
                ((cast (byte_chunk.[ sz 1 ] <: u8) <: u32) <<! 8l <: u32)
                <:
                u32) |.
              ((cast (byte_chunk.[ sz 2 ] <: u8) <: u32) <<! 16l <: u32)
              <:
              u32) |.
            ((cast (byte_chunk.[ sz 3 ] <: u8) <: u32) <<! 24l <: u32)
          in
          let even_bits:u32 = random_bits_as_u32 &. 1431655765ul in
          let odd_bits:u32 = (random_bits_as_u32 >>! 1l <: u32) &. 1431655765ul in
          let coin_toss_outcomes:u32 = even_bits +! odd_bits in
          Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_step_by
                    ({
                        Core.Ops.Range.f_start = 0ul;
                        Core.Ops.Range.f_end = Core.Num.impl__u32__BITS
                      }
                      <:
                      Core.Ops.Range.t_Range u32)
                    (sz 4)
                  <:
                  Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range u32))
              <:
              Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range u32))
            sampled_i32s
            (fun sampled_i32s outcome_set ->
                let sampled_i32s:t_Array i32 (sz 256) = sampled_i32s in
                let outcome_set:u32 = outcome_set in
                let outcome_1_:i32 =
                  cast ((coin_toss_outcomes >>! outcome_set <: u32) &. 3ul <: u32) <: i32
                in
                let outcome_2_:i32 =
                  cast ((coin_toss_outcomes >>! (outcome_set +! 2ul <: u32) <: u32) &. 3ul <: u32)
                  <:
                  i32
                in
                let offset:usize = cast (outcome_set >>! 2l <: u32) <: usize in
                let sampled_i32s:t_Array i32 (sz 256) =
                  Rust_primitives.Hax.Monomorphized_update_at.update_at_usize sampled_i32s
                    ((sz 8 *! chunk_number <: usize) +! offset <: usize)
                    (outcome_1_ -! outcome_2_ <: i32)
                in
                sampled_i32s))
  in
  Libcrux_ml_kem.Polynomial.from_i32_array sampled_i32s

let sample_from_binomial_distribution_3_ (randomness: t_Slice u8) =
  let sampled_i32s:t_Array i32 (sz 256) = Rust_primitives.Hax.repeat 0l (sz 256) in
  let sampled_i32s:t_Array i32 (sz 256) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact randomness (sz 3) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      sampled_i32s
      (fun sampled_i32s temp_1_ ->
          let sampled_i32s:t_Array i32 (sz 256) = sampled_i32s in
          let chunk_number, byte_chunk:(usize & t_Slice u8) = temp_1_ in
          let (random_bits_as_u24: u32):u32 =
            ((cast (byte_chunk.[ sz 0 ] <: u8) <: u32) |.
              ((cast (byte_chunk.[ sz 1 ] <: u8) <: u32) <<! 8l <: u32)
              <:
              u32) |.
            ((cast (byte_chunk.[ sz 2 ] <: u8) <: u32) <<! 16l <: u32)
          in
          let first_bits:u32 = random_bits_as_u24 &. 2396745ul in
          let second_bits:u32 = (random_bits_as_u24 >>! 1l <: u32) &. 2396745ul in
          let third_bits:u32 = (random_bits_as_u24 >>! 2l <: u32) &. 2396745ul in
          let coin_toss_outcomes:u32 = (first_bits +! second_bits <: u32) +! third_bits in
          Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_step_by
                    ({ Core.Ops.Range.f_start = 0l; Core.Ops.Range.f_end = 24l }
                      <:
                      Core.Ops.Range.t_Range i32)
                    (sz 6)
                  <:
                  Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range i32))
              <:
              Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range i32))
            sampled_i32s
            (fun sampled_i32s outcome_set ->
                let sampled_i32s:t_Array i32 (sz 256) = sampled_i32s in
                let outcome_set:i32 = outcome_set in
                let outcome_1_:i32 =
                  cast ((coin_toss_outcomes >>! outcome_set <: u32) &. 7ul <: u32) <: i32
                in
                let outcome_2_:i32 =
                  cast ((coin_toss_outcomes >>! (outcome_set +! 3l <: i32) <: u32) &. 7ul <: u32)
                  <:
                  i32
                in
                let offset:usize = cast (outcome_set /! 6l <: i32) <: usize in
                let sampled_i32s:t_Array i32 (sz 256) =
                  Rust_primitives.Hax.Monomorphized_update_at.update_at_usize sampled_i32s
                    ((sz 4 *! chunk_number <: usize) +! offset <: usize)
                    (outcome_1_ -! outcome_2_ <: i32)
                in
                sampled_i32s))
  in
  Libcrux_ml_kem.Polynomial.from_i32_array sampled_i32s

let sample_from_binomial_distribution (v_ETA: usize) (randomness: t_Slice u8) =
  match cast (v_ETA <: usize) <: u32 with
  | 2ul -> sample_from_binomial_distribution_2_ randomness
  | 3ul -> sample_from_binomial_distribution_3_ randomness
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let sample_from_xof (v_K: usize) (seeds: t_Array (t_Array u8 (sz 34)) v_K) =
  let (sampled_coefficients: t_Array usize v_K):t_Array usize v_K =
    Rust_primitives.Hax.repeat (sz 0) v_K
  in
  let (out: t_Array (t_Array i32 (sz 256)) v_K):t_Array (t_Array i32 (sz 256)) v_K =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0l (sz 256) <: t_Array i32 (sz 256)) v_K
  in
  let xof_state:Libcrux_sha3.X4.t_Shake128StateX4 =
    Libcrux_ml_kem.Hash_functions.absorb v_K seeds
  in
  let tmp0, out1:(Libcrux_sha3.X4.t_Shake128StateX4 & t_Array (t_Array u8 (sz 504)) v_K) =
    Libcrux_ml_kem.Hash_functions.squeeze_three_blocks v_K xof_state
  in
  let xof_state:Libcrux_sha3.X4.t_Shake128StateX4 = tmp0 in
  let randomness:t_Array (t_Array u8 (sz 504)) v_K = out1 in
  let tmp0, tmp1, out1:(t_Array usize v_K & t_Array (t_Array i32 (sz 256)) v_K & bool) =
    sample_from_uniform_distribution_next v_K (sz 504) randomness sampled_coefficients out
  in
  let sampled_coefficients:t_Array usize v_K = tmp0 in
  let out:t_Array (t_Array i32 (sz 256)) v_K = tmp1 in
  let done:bool = out1 in
  let done, out, sampled_coefficients, xof_state:(bool & t_Array (t_Array i32 (sz 256)) v_K &
    t_Array usize v_K &
    Libcrux_sha3.X4.t_Shake128StateX4) =
    Rust_primitives.f_while_loop (fun temp_0_ ->
          let done, out, sampled_coefficients, xof_state:(bool & t_Array (t_Array i32 (sz 256)) v_K &
            t_Array usize v_K &
            Libcrux_sha3.X4.t_Shake128StateX4) =
            temp_0_
          in
          ~.done <: bool)
      (done, out, sampled_coefficients, xof_state
        <:
        (bool & t_Array (t_Array i32 (sz 256)) v_K & t_Array usize v_K &
          Libcrux_sha3.X4.t_Shake128StateX4))
      (fun temp_0_ ->
          let done, out, sampled_coefficients, xof_state:(bool & t_Array (t_Array i32 (sz 256)) v_K &
            t_Array usize v_K &
            Libcrux_sha3.X4.t_Shake128StateX4) =
            temp_0_
          in
          let tmp0, out1:(Libcrux_sha3.X4.t_Shake128StateX4 & t_Array (t_Array u8 (sz 168)) v_K) =
            Libcrux_ml_kem.Hash_functions.squeeze_block v_K xof_state
          in
          let xof_state:Libcrux_sha3.X4.t_Shake128StateX4 = tmp0 in
          let randomness:t_Array (t_Array u8 (sz 168)) v_K = out1 in
          let tmp0, tmp1, out1:(t_Array usize v_K & t_Array (t_Array i32 (sz 256)) v_K & bool) =
            sample_from_uniform_distribution_next v_K (sz 168) randomness sampled_coefficients out
          in
          let sampled_coefficients:t_Array usize v_K = tmp0 in
          let out:t_Array (t_Array i32 (sz 256)) v_K = tmp1 in
          let done:bool = out1 in
          done, out, sampled_coefficients, xof_state
          <:
          (bool & t_Array (t_Array i32 (sz 256)) v_K & t_Array usize v_K &
            Libcrux_sha3.X4.t_Shake128StateX4))
  in
  let _:Prims.unit = Libcrux_ml_kem.Hash_functions.free_state xof_state in
  Core.Array.impl_23__map v_K out Libcrux_ml_kem.Polynomial.from_i32_array
