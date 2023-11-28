module Libcrux.Kem.Kyber.Sampling
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let increment (x: usize) : FStar.HyperStack.ST.St Prims.unit =
  let x:usize = x +! sz 1 in
  ()

let sample_from_binomial_distribution_2_ (randomness: t_Slice u8)
    : FStar.HyperStack.ST.St Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
  let (sampled: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement):Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
  =
    Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let _:Prims.unit =
    Rust_primitives.f_for_loop (sz 0)
      ((Core.Slice.impl__len randomness <: usize) /! sz 4 <: usize)
      (fun chunk_number ->
          let chunk_number:usize = chunk_number in
          let byte_chunk:t_Slice u8 =
            randomness.[ {
                Core.Ops.Range.f_start = chunk_number *! sz 4 <: usize;
                Core.Ops.Range.f_end = (chunk_number *! sz 4 <: usize) +! sz 4 <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
          in
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
          Rust_primitives.f_for_loop 0ul
            (Core.Num.impl__u32__BITS /! 4ul <: u32)
            (fun i ->
                let i:u32 = i in
                let outcome_set:u32 = i *! 4ul in
                let outcome_1_:i32 =
                  cast ((coin_toss_outcomes >>! outcome_set <: u32) &. 3ul <: u32) <: i32
                in
                let outcome_2_:i32 =
                  cast ((coin_toss_outcomes >>! (outcome_set +! 2ul <: u32) <: u32) &. 3ul <: u32)
                  <:
                  i32
                in
                let offset:usize = cast (outcome_set >>! 2l <: u32) <: usize in
                let _:Prims.unit =
                  Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize sampled
                      .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    ((sz 8 *! chunk_number <: usize) +! offset <: usize)
                    (outcome_1_ -! outcome_2_ <: i32)
                in
                ()))
  in
  let _:Prims.unit = () <: Prims.unit in
  sampled

let sample_from_binomial_distribution_3_ (randomness: t_Slice u8)
    : FStar.HyperStack.ST.St Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
  let (sampled: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement):Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
  =
    Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let _:Prims.unit =
    Rust_primitives.f_for_loop (sz 0)
      ((Core.Slice.impl__len randomness <: usize) /! sz 3 <: usize)
      (fun chunk_number ->
          let chunk_number:usize = chunk_number in
          let byte_chunk:t_Slice u8 =
            randomness.[ {
                Core.Ops.Range.f_start = chunk_number *! sz 3 <: usize;
                Core.Ops.Range.f_end = (chunk_number *! sz 3 <: usize) +! sz 3 <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
          in
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
          Rust_primitives.f_for_loop 0l
            (24l /! 6l <: i32)
            (fun i ->
                let i:i32 = i in
                let outcome_set:i32 = i *! 6l in
                let outcome_1_:i32 =
                  cast ((coin_toss_outcomes >>! outcome_set <: u32) &. 7ul <: u32) <: i32
                in
                let outcome_2_:i32 =
                  cast ((coin_toss_outcomes >>! (outcome_set +! 3l <: i32) <: u32) &. 7ul <: u32)
                  <:
                  i32
                in
                let offset:usize = cast (outcome_set /! 6l <: i32) <: usize in
                let _:Prims.unit =
                  Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize sampled
                      .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    ((sz 4 *! chunk_number <: usize) +! offset <: usize)
                    (outcome_1_ -! outcome_2_ <: i32)
                in
                ()))
  in
  let _:Prims.unit = () <: Prims.unit in
  sampled

let sample_from_binomial_distribution (v_ETA: usize) (randomness: t_Slice u8)
    : FStar.HyperStack.ST.St Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
  let _:Prims.unit = () <: Prims.unit in
  match cast (v_ETA <: usize) <: u32 with
  | 2ul -> sample_from_binomial_distribution_2_ randomness
  | 3ul -> sample_from_binomial_distribution_3_ randomness

let sample_from_uniform_distribution
      (v_SEED_SIZE: usize)
      (randomness: t_Array u8 v_SEED_SIZE)
      (sampling_error: Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error)
    : FStar.HyperStack.ST.St Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
  let sampled_coefficients:usize = sz 0 in
  let (out: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement):Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
  =
    Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let done:t_Array bool (sz 1) =
    [@inline_let] let list =  [false] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
    Rust_primitives.Hax.array_of_list list
  in
  let _:Prims.unit =
    Rust_primitives.f_for_loop (sz 0)
      ((Core.Slice.impl__len (Rust_primitives.unsize randomness <: t_Slice u8) <: usize) /! sz 3
        <:
        usize)
      (fun i ->
          let i:usize = i in
          let bytes:t_Slice u8 =
            randomness.[ {
                Core.Ops.Range.f_start = i *! sz 3 <: usize;
                Core.Ops.Range.f_end = (i *! sz 3 <: usize) +! sz 3 <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
          in
          if ~.(done.[ sz 0 ] <: bool)
          then
            let b1:i32 = cast (bytes.[ sz 0 ] <: u8) <: i32 in
            let b2:i32 = cast (bytes.[ sz 1 ] <: u8) <: i32 in
            let b3:i32 = cast (bytes.[ sz 2 ] <: u8) <: i32 in
            let d1:i32 = ((b2 &. 15l <: i32) <<! 8l <: i32) |. b1 in
            let d2:i32 = (b3 <<! 4l <: i32) |. (b2 >>! 4l <: i32) in
            let _:Prims.unit =
              if
                d1 <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS &&
                sampled_coefficients <. Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
              then
                let _:Prims.unit =
                  Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize out
                      .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    sampled_coefficients
                    d1
                in
                let _:Prims.unit = increment sampled_coefficients in
                ()
            in
            let _:Prims.unit =
              if
                d2 <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS &&
                sampled_coefficients <. Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
              then
                let _:Prims.unit =
                  Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize out
                      .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    sampled_coefficients
                    d2
                in
                let _:Prims.unit = increment sampled_coefficients in
                ()
            in
            if sampled_coefficients =. Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
            then
              let _:Prims.unit =
                Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize done (sz 0) true
              in
              ())
  in
  if done.[ sz 0 ]
  then
    let _:Prims.unit = () <: Prims.unit in
    let sampling_error:Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error =
      Core.Option.Option_None <: Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error
    in
    out
  else
    let sampling_error:Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error =
      Core.Option.Option_Some
      (Libcrux.Kem.Kyber.Types.Error_RejectionSampling <: Libcrux.Kem.Kyber.Types.t_Error)
      <:
      Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error
    in
    out
