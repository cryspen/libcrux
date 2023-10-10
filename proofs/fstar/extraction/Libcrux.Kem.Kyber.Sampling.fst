module Libcrux.Kem.Kyber.Sampling
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let sample_from_uniform_distribution (#v_SEED_SIZE: usize) (randomness: array u8 v_SEED_SIZE)
    : (Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement &
      Core.Option.t_Option Libcrux.Kem.Kyber.t_BadRejectionSamplingRandomnessError) =
  let (sampled_coefficients: usize):usize = sz 0 in
  let (out: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement):Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement
  =
    Libcrux.Kem.Kyber.Arithmetic.impl__ZERO
  in
  let out, sampled_coefficients:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement &
    Prims.unit) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Slice.impl__chunks
              (Rust_primitives.unsize randomness <: slice u8)
              (sz 3)
            <:
            Core.Slice.Iter.t_Chunks u8)
        <:
        _.f_IntoIter)
      (out, sampled_coefficients)
      (fun (out, sampled_coefficients) bytes ->
          let b1:i32 = cast bytes.[ sz 0 ] <: i32 in
          let b2:i32 = cast bytes.[ sz 1 ] <: i32 in
          let b3:i32 = cast bytes.[ sz 2 ] <: i32 in
          let d1:i32 = ((b2 &. 15l <: i32) <<! 8l <: i32) |. b1 in
          let d2:i32 = (b3 <<! 4l <: i32) |. (b2 >>! 4l <: i32) in
          let out, sampled_coefficients:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement &
            Prims.unit) =
            if
              d1 <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS &&
              sampled_coefficients <. Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
            then
              let out:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                Rust_primitives.Hax.update_at out sampled_coefficients d1
              in
              out, sampled_coefficients +! sz 1
            else out, sampled_coefficients
          in
          let out, sampled_coefficients:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement &
            Prims.unit) =
            if
              d2 <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS &&
              sampled_coefficients <. Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
            then
              let out:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                Rust_primitives.Hax.update_at out sampled_coefficients d2
              in
              let sampled_coefficients:Prims.unit = sampled_coefficients +! sz 1 in
              out, sampled_coefficients
            else out, sampled_coefficients
          in
          if sampled_coefficients =. Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
          then
            let* hoist4:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (out, Core.Option.Option_None)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (out, sampled_coefficients)
          else Core.Ops.Control_flow.ControlFlow_Continue (out, sampled_coefficients))
  in
  out, Core.Option.Option_Some Libcrux.Kem.Kyber.BadRejectionSamplingRandomnessError

let sample_from_binomial_distribution_2_ (randomness: array u8 (sz 128))
    : Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let (sampled: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement):Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement
  =
    Libcrux.Kem.Kyber.Arithmetic.impl__ZERO
  in
  let sampled:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact (Rust_primitives.unsize randomness <: slice u8) (sz 4)
                <:
                Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        _.f_IntoIter)
      sampled
      (fun sampled (chunk_number, byte_chunk) ->
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
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_step_by
                    ({ Core.Ops.Range.f_start = 0ul; Core.Ops.Range.f_end = Core.Num.impl_8__BITS })
                    (sz 4)
                  <:
                  Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range u32))
              <:
              _.f_IntoIter)
            sampled
            (fun sampled outcome_set ->
                let outcome_1_:i32 =
                  cast ((coin_toss_outcomes >>! outcome_set <: u32) &. 3ul) <: i32
                in
                let outcome_2_:i32 =
                  cast ((coin_toss_outcomes >>! (outcome_set +! 2ul <: u32) <: u32) &. 3ul) <: i32
                in
                let offset:usize = cast (outcome_set >>! 2l) <: usize in
                let sampled:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                  Rust_primitives.Hax.update_at sampled
                    ((sz 8 *! chunk_number <: usize) +! offset <: usize)
                    (outcome_1_ -! outcome_2_ <: i32)
                in
                sampled))
  in
  sampled