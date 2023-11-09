module Libcrux.Kem.Kyber.Sampling
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let sample_from_binomial_distribution_2_ (randomness: t_Slice u8)
    : Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let (sampled: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement):Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement
  =
    Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
  in
  let sampled:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact randomness (sz 4) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      sampled
      (fun sampled temp_1_ ->
          let sampled:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement = sampled in
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
                      })
                    (sz 4)
                  <:
                  Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range u32))
              <:
              Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range u32))
            sampled
            (fun sampled outcome_set ->
                let sampled:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement = sampled in
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
                let sampled:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                  {
                    sampled with
                    Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    =
                    Rust_primitives.Hax.update_at sampled
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      ((sz 8 *! chunk_number <: usize) +! offset <: usize)
                      (outcome_1_ -! outcome_2_ <: i32)
                  }
                in
                sampled))
  in
  let _:Prims.unit = () in
  sampled

let sample_from_binomial_distribution_3_ (randomness: t_Slice u8)
    : Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let (sampled: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement):Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement
  =
    Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
  in
  let sampled:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact randomness (sz 3) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      sampled
      (fun sampled temp_1_ ->
          let sampled:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement = sampled in
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
                    ({ Core.Ops.Range.f_start = 0l; Core.Ops.Range.f_end = 24l })
                    (sz 6)
                  <:
                  Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range i32))
              <:
              Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range i32))
            sampled
            (fun sampled outcome_set ->
                let sampled:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement = sampled in
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
                let sampled:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                  {
                    sampled with
                    Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    =
                    Rust_primitives.Hax.update_at sampled
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      ((sz 4 *! chunk_number <: usize) +! offset <: usize)
                      (outcome_1_ -! outcome_2_ <: i32)
                  }
                in
                sampled))
  in
  let _:Prims.unit = () in
  sampled

let sample_from_uniform_distribution (v_SEED_SIZE: usize) (randomness: t_Array u8 v_SEED_SIZE)
    : (Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement &
      Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error) =
  let (sampled_coefficients: usize):usize = sz 0 in
  let (out: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement):Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement
  =
    Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
  in
  let out, sampled_coefficients:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement & usize)
  =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Slice.impl__chunks (
                Rust_primitives.unsize randomness <: t_Slice u8)
              (sz 3)
            <:
            Core.Slice.Iter.t_Chunks u8)
        <:
        Core.Slice.Iter.t_Chunks u8)
      (out, sampled_coefficients)
      (fun temp_0_ bytes ->
          let out, sampled_coefficients:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement &
            usize) =
            temp_0_
          in
          let bytes:t_Slice u8 = bytes in
          let b1:i32 = cast (bytes.[ sz 0 ] <: u8) <: i32 in
          let b2:i32 = cast (bytes.[ sz 1 ] <: u8) <: i32 in
          let b3:i32 = cast (bytes.[ sz 2 ] <: u8) <: i32 in
          let d1:i32 = ((b2 &. 15l <: i32) <<! 8l <: i32) |. b1 in
          let d2:i32 = (b3 <<! 4l <: i32) |. (b2 >>! 4l <: i32) in
          let out, sampled_coefficients:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement &
            usize) =
            if
              d1 <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS &&
              sampled_coefficients <. Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
            then
              let out:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                {
                  out with
                  Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                  =
                  Rust_primitives.Hax.update_at out.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    sampled_coefficients
                    d1
                }
              in
              out, sampled_coefficients +! sz 1
            else out, sampled_coefficients
          in
          let out, sampled_coefficients:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement &
            usize) =
            if
              d2 <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS &&
              sampled_coefficients <. Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
            then
              let out:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                {
                  out with
                  Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                  =
                  Rust_primitives.Hax.update_at out.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    sampled_coefficients
                    d2
                }
              in
              let sampled_coefficients:usize = sampled_coefficients +! sz 1 in
              out, sampled_coefficients
            else out, sampled_coefficients
          in
          if sampled_coefficients =. Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
          then
            let _:Prims.unit = () in
            let* hoist1:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (out, Core.Option.Option_None)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (out, sampled_coefficients)
          else Core.Ops.Control_flow.ControlFlow_Continue (out, sampled_coefficients))
  in
  out, Core.Option.Option_Some Libcrux.Kem.Kyber.Types.Error_RejectionSampling

let sample_from_binomial_distribution (v_ETA: usize) (randomness: t_Slice u8)
    : Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let _:Prims.unit = () in
  match cast (v_ETA <: usize) <: u32 with
  | 2ul -> sample_from_binomial_distribution_2_ randomness
  | 3ul -> sample_from_binomial_distribution_3_ randomness
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)