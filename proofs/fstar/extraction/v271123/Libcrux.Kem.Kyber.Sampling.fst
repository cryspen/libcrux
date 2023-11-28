module Libcrux.Kem.Kyber.Sampling
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let sample_from_binomial_distribution_2_ (randomness: t_Slice u8)
    : FStar.HyperStack.ST.St Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let (sampled: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement):Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement
  =
    Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
  in
  let _:Prims.unit =
    Rust_primitives.f_for_loop (sz 0)
      ((Core.Slice.impl__len randomness <: usize) /! sz 4 <: usize)
      (fun chunk_number ->
          let chunk_number:usize = chunk_number in
          let (random_bits_as_u32: u32):u32 =
            (((cast (randomness.[ (chunk_number *! sz 4 <: usize) +! sz 0 <: usize ] <: u8) <: u32) |.
                ((cast (randomness.[ (chunk_number *! sz 4 <: usize) +! sz 1 <: usize ] <: u8)
                    <:
                    u32) <<!
                  8l
                  <:
                  u32)
                <:
                u32) |.
              ((cast (randomness.[ (chunk_number *! sz 4 <: usize) +! sz 2 <: usize ] <: u8) <: u32) <<!
                16l
                <:
                u32)
              <:
              u32) |.
            ((cast (randomness.[ (chunk_number *! sz 4 <: usize) +! sz 3 <: usize ] <: u8) <: u32) <<!
              24l
              <:
              u32)
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
    : FStar.HyperStack.ST.St Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let (sampled: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement):Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement
  =
    Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
  in
  let _:Prims.unit =
    Rust_primitives.f_for_loop (sz 0)
      ((Core.Slice.impl__len randomness <: usize) /! sz 3 <: usize)
      (fun chunk_number ->
          let chunk_number:usize = chunk_number in
          let (random_bits_as_u24: u32):u32 =
            ((cast (randomness.[ (chunk_number *! sz 3 <: usize) +! sz 0 <: usize ] <: u8) <: u32) |.
              ((cast (randomness.[ (chunk_number *! sz 3 <: usize) +! sz 1 <: usize ] <: u8) <: u32) <<!
                8l
                <:
                u32)
              <:
              u32) |.
            ((cast (randomness.[ (chunk_number *! sz 3 <: usize) +! sz 2 <: usize ] <: u8) <: u32) <<!
              16l
              <:
              u32)
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
    : FStar.HyperStack.ST.St Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement =
  let _:Prims.unit = () <: Prims.unit in
  match cast (v_ETA <: usize) <: u32 with
  | 2ul -> sample_from_binomial_distribution_2_ randomness
  | 3ul -> sample_from_binomial_distribution_3_ randomness
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let sample_from_uniform_distribution (v_SEED_SIZE: usize) (randomness: t_Array u8 v_SEED_SIZE)
    : FStar.HyperStack.ST.St
    (Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement &
      Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error) =
  let (sampled_coefficients: t_Array usize (sz 1)):t_Array usize (sz 1) =
    let list = [sz 0] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
    Rust_primitives.Hax.array_of_list list
  in
  let (out: Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement):Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement
  =
    Libcrux.Kem.Kyber.Arithmetic.impl__KyberPolynomialRingElement__ZERO
  in
  let (done: t_Array bool (sz 1)):t_Array bool (sz 1) =
    let list = [false] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
    Rust_primitives.Hax.array_of_list list
  in
  let (max: usize):usize =
    (Core.Slice.impl__len (Rust_primitives.unsize randomness <: t_Slice u8) <: usize) /! sz 3
  in
  let _:Prims.unit =
    Rust_primitives.f_for_loop (sz 0)
      max
      (fun i ->
          let i:usize = i in
          if ~.(done.[ sz 0 ] <: bool) <: bool
          then
            let b1:i32 = cast (randomness.[ (i *! sz 3 <: usize) +! sz 0 <: usize ] <: u8) <: i32 in
            let b2:i32 = cast (randomness.[ (i *! sz 3 <: usize) +! sz 1 <: usize ] <: u8) <: i32 in
            let b3:i32 = cast (randomness.[ (i *! sz 3 <: usize) +! sz 2 <: usize ] <: u8) <: i32 in
            let d1:i32 = ((b2 &. 15l <: i32) <<! 8l <: i32) |. b1 in
            let d2:i32 = (b3 <<! 4l <: i32) |. (b2 >>! 4l <: i32) in
            let _:Prims.unit =
             let s0   = sampled_coefficients.[ sz 0 ] <: usize in
             if
                d1 <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS &&
                s0 <.
                Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
              then
                let _:Prims.unit =
                  Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize out
                      .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    (sampled_coefficients.[ sz 0 ] <: usize)
                    d1
                in
                Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize sampled_coefficients
                  (sz 0)
                  ((sampled_coefficients.[ sz 0 ] <: usize) +! sz 1 <: usize)
            in
            let _:Prims.unit =
              let s0 = (sampled_coefficients.[ sz 0 ] <: usize) in
              if
                d2 <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS &&
                s0 <.
                Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
              then
                let _:Prims.unit =
                  Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize out
                      .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    (sampled_coefficients.[ sz 0 ] <: usize)
                    d2
                in
                let _:Prims.unit =
                  Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize sampled_coefficients
                    (sz 0)
                    ((sampled_coefficients.[ sz 0 ] <: usize) +! sz 1 <: usize)
                in
                ()
            in
            if
              (sampled_coefficients.[ sz 0 ] <: usize) =.
              Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
            then
              let _:Prims.unit =
                Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize done (sz 0) true
              in
              ())
  in
  if done.[ sz 0 ]
  then
    out, (Core.Option.Option_None <: Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error)
    <:
    (Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement &
      Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error)
  else
    out,
    (Core.Option.Option_Some
      (Libcrux.Kem.Kyber.Types.Error_RejectionSampling <: Libcrux.Kem.Kyber.Types.t_Error)
      <:
      Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error)
    <:
    (Libcrux.Kem.Kyber.Arithmetic.t_KyberPolynomialRingElement &
      Core.Option.t_Option Libcrux.Kem.Kyber.Types.t_Error)
