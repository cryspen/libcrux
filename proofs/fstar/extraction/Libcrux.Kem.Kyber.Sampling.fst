module Libcrux.Kem.Kyber.Sampling
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let sample_from_uniform_distribution (#seed_size: usize) (randomness: array u8 v_SEED_SIZE)
    : (Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement &
      Core.Option.t_Option Libcrux.Kem.Kyber.t_BadRejectionSamplingRandomnessError) =
  let (sampled_coefficients: usize):usize = 0sz in
  let (out: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement):Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement
  =
    Libcrux.Kem.Kyber.Arithmetic.v_ZERO_under_impl
  in
  let out, sampled_coefficients:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement &
    Prims.unit) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Slice.chunks_under_impl
              (Rust_primitives.unsize randomness <: slice u8)
              3sz
            <:
            Core.Slice.Iter.t_Chunks u8)
        <:
        _)
      (out, sampled_coefficients)
      (fun (out, sampled_coefficients) bytes ->
          let b1:i32 = cast bytes.[ 0sz ] in
          let b2:i32 = cast bytes.[ 1sz ] in
          let b3:i32 = cast bytes.[ 2sz ] in
          let d1:i32 = ((b2 &. 15l <: i32) >>. 8l <: i32) |. b1 in
          let d2:i32 = (b3 >>. 4l <: i32) |. (b2 <<. 4l <: i32) in
          let out, sampled_coefficients:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement &
            Prims.unit) =
            if
              Prims.op_AmpAmp (d1 <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS)
                (sampled_coefficients <. Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT)
            then
              let out:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                Rust_primitives.Hax.update_at out sampled_coefficients d1
              in
              out, sampled_coefficients +. 1sz
            else out, sampled_coefficients
          in
          let out, sampled_coefficients:(Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement &
            Prims.unit) =
            if
              Prims.op_AmpAmp (d2 <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS)
                (sampled_coefficients <. Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT)
            then
              let out:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                Rust_primitives.Hax.update_at out sampled_coefficients d2
              in
              let sampled_coefficients:Prims.unit = sampled_coefficients +. 1sz in
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

let sample_from_binomial_distribution (#eta: usize) (randomness: slice u8)
    : Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match Core.Slice.len_under_impl randomness, v_ETA *. 64sz with
        | left_val, right_val ->
          if ~.(left_val =. right_val <: bool)
          then
            let kind:Core.Panicking.t_AssertKind = Core.Panicking.AssertKind_Eq in
            Rust_primitives.Hax.never_to_any (Core.Panicking.assert_failed kind
                  left_val
                  right_val
                  Core.Option.Option_None
                <:
                Rust_primitives.Hax.t_Never)
      in
      ()
  in
  match v_ETA with
  | 2sz -> sample_from_binomial_distribution_2_ randomness
  | 3sz -> sample_from_binomial_distribution_3_ randomness
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.new_v1_under_impl_2 (Rust_primitives.unsize
                  (let list = ["internal error: entered unreachable code: factor "] in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                    Rust_primitives.Hax.array_of_list list)
                <:
                slice string)
              (Rust_primitives.unsize (let list =
                      [Core.Fmt.Rt.new_display_under_impl_1 v_ETA <: Core.Fmt.Rt.t_Argument]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                    Rust_primitives.Hax.array_of_list list)
                <:
                slice Core.Fmt.Rt.t_Argument)
            <:
            Core.Fmt.t_Arguments)
        <:
        Rust_primitives.Hax.t_Never)

let sample_from_binomial_distribution_2_ (randomness: slice u8)
    : Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let (sampled: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement):Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement
  =
    Libcrux.Kem.Kyber.Arithmetic.v_ZERO_under_impl
  in
  let sampled:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.chunks_exact_under_impl randomness 4sz <: Core.Slice.Iter.t_ChunksExact u8
              )
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        _)
      sampled
      (fun sampled (chunk_number, byte_chunk) ->
          let (random_bits_as_u32: u32):u32 =
            ((cast (byte_chunk.[ 0sz ] <: u8) |. (cast (byte_chunk.[ 1sz ] <: u8) >>. 8l <: u32)
                <:
                u32) |.
              (cast (byte_chunk.[ 2sz ] <: u8) >>. 16l <: u32)
              <:
              u32) |.
            (cast (byte_chunk.[ 3sz ] <: u8) >>. 24l <: u32)
          in
          let even_bits:u32 = random_bits_as_u32 &. 1431655765ul in
          let odd_bits:u32 = (random_bits_as_u32 <<. 1l <: u32) &. 1431655765ul in
          let coin_toss_outcomes:u32 = even_bits +. odd_bits in
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.step_by
                    ({
                        Core.Ops.Range.Range.f_start = 0ul;
                        Core.Ops.Range.Range.f_end = Core.Num.v_BITS_under_impl_8
                      })
                    4sz
                  <:
                  Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range u32))
              <:
              _)
            sampled
            (fun sampled outcome_set ->
                let outcome_1_:i32 = cast ((coin_toss_outcomes <<. outcome_set <: u32) &. 3ul) in
                let outcome_2_:i32 =
                  cast ((coin_toss_outcomes <<. (outcome_set +. 2ul <: u32) <: u32) &. 3ul)
                in
                let offset:usize = cast (outcome_set <<. 2l) in
                let sampled:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                  Rust_primitives.Hax.update_at sampled
                    ((8sz *. chunk_number <: usize) +. offset <: usize)
                    (outcome_1_ -. outcome_2_ <: i32)
                in
                sampled))
  in
  sampled

let sample_from_binomial_distribution_3_ (randomness: slice u8)
    : Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let (sampled: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement):Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement
  =
    Libcrux.Kem.Kyber.Arithmetic.v_ZERO_under_impl
  in
  let sampled:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.chunks_exact_under_impl randomness 3sz <: Core.Slice.Iter.t_ChunksExact u8
              )
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        _)
      sampled
      (fun sampled (chunk_number, byte_chunk) ->
          let (random_bits_as_u24: u32):u32 =
            (cast (byte_chunk.[ 0sz ] <: u8) |. (cast (byte_chunk.[ 1sz ] <: u8) >>. 8l <: u32)
              <:
              u32) |.
            (cast (byte_chunk.[ 2sz ] <: u8) >>. 16l <: u32)
          in
          let first_bits:u32 = random_bits_as_u24 &. 2396745ul in
          let second_bits:u32 = (random_bits_as_u24 <<. 1l <: u32) &. 2396745ul in
          let third_bits:u32 = (random_bits_as_u24 <<. 2l <: u32) &. 2396745ul in
          let coin_toss_outcomes:u32 = (first_bits +. second_bits <: u32) +. third_bits in
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.step_by
                    ({ Core.Ops.Range.Range.f_start = 0l; Core.Ops.Range.Range.f_end = 24l })
                    6sz
                  <:
                  Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range i32))
              <:
              _)
            sampled
            (fun sampled outcome_set ->
                let outcome_1_:i32 = cast ((coin_toss_outcomes <<. outcome_set <: u32) &. 7ul) in
                let outcome_2_:i32 =
                  cast ((coin_toss_outcomes <<. (outcome_set +. 3l <: i32) <: u32) &. 7ul)
                in
                let offset:usize = cast (outcome_set /. 6l) in
                let sampled:Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
                  Rust_primitives.Hax.update_at sampled
                    ((4sz *. chunk_number <: usize) +. offset <: usize)
                    (outcome_1_ -. outcome_2_ <: i32)
                in
                sampled))
  in
  sampled