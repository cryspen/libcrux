module Libcrux.Kem.Kyber.Sampling
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let rejection_sampling_panic_with_diagnostic (_: Prims.unit) =
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "explicit panic"
      <:
      Rust_primitives.Hax.t_Never)

let sample_from_binomial_distribution_2_ (randomness: t_Slice u8) =
  let (sampled: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement):Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
  =
    Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let sampled:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact randomness (sz 4) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      sampled
      (fun sampled temp_1_ ->
          let sampled:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = sampled in
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
                      Core.Ops.Range.t_Range pub_u32)
                    (sz 4)
                  <:
                  Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range pub_u32))
              <:
              Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range pub_u32))
            sampled
            (fun sampled outcome_set ->
                let sampled:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = sampled in
                let outcome_set:pub_u32 = outcome_set in
                let outcome_1_:i32 =
                  cast ((coin_toss_outcomes >>! outcome_set <: u32) &. 3ul <: u32) <: i32
                in
                let outcome_2_:i32 =
                  cast ((coin_toss_outcomes >>! (outcome_set +! 2ul <: pub_u32) <: u32) &. 3ul <: u32)
                  <:
                  i32
                in
                let offset:usize = cast (outcome_set >>! 2l <: pub_u32) <: usize in
                let sampled:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
                  {
                    sampled with
                    Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize sampled
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      ((sz 8 *! chunk_number <: usize) +! offset <: usize)
                      (outcome_1_ -! outcome_2_ <: i32)
                  }
                  <:
                  Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
                in
                sampled))
  in
  let _:Prims.unit = () <: Prims.unit in
  sampled

let sample_from_binomial_distribution_3_ (randomness: t_Slice u8) =
  let (sampled: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement):Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
  =
    Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let sampled:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__chunks_exact randomness (sz 3) <: Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
      sampled
      (fun sampled temp_1_ ->
          let sampled:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = sampled in
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
                      Core.Ops.Range.t_Range pub_i32)
                    (sz 6)
                  <:
                  Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range pub_i32))
              <:
              Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range pub_i32))
            sampled
            (fun sampled outcome_set ->
                let sampled:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = sampled in
                let outcome_set:pub_i32 = outcome_set in
                let outcome_1_:i32 =
                  cast ((coin_toss_outcomes >>! outcome_set <: pub_u32) &. 7ul <: u32) <: i32
                in
                let outcome_2_:i32 =
                  cast ((coin_toss_outcomes >>! (outcome_set +! 3l <: pub_i32) <: u32) &. 7ul <: u32)
                  <:
                  i32
                in
                let offset:usize = cast (outcome_set /! 6l <: pub_i32) <: usize in
                let sampled:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
                  {
                    sampled with
                    Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize sampled
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      ((sz 4 *! chunk_number <: usize) +! offset <: usize)
                      (outcome_1_ -! outcome_2_ <: i32)
                  }
                  <:
                  Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
                in
                sampled))
  in
  let _:Prims.unit = () <: Prims.unit in
  sampled

let sample_from_binomial_distribution (v_ETA: usize) (randomness: t_Slice u8) =
  let _:Prims.unit = () <: Prims.unit in
  match cast (v_ETA <: usize) <: pub_u32 with
  | 2ul -> sample_from_binomial_distribution_2_ randomness
  | 3ul -> sample_from_binomial_distribution_3_ randomness
  | _ ->
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

        <:
        Rust_primitives.Hax.t_Never)

let sample_from_uniform_distribution (randomness: t_Array u8 (sz 840)) =
  let (sampled_coefficients: usize):usize = sz 0 in
  let (out: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement):Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
  =
    Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let done:bool = false in
  let done, out, sampled_coefficients:(bool & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement &
    usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Slice.impl__chunks (
                Rust_primitives.unsize randomness <: t_Slice u8)
              (sz 3)
            <:
            Core.Slice.Iter.t_Chunks u8)
        <:
        Core.Slice.Iter.t_Chunks u8)
      (done, out, sampled_coefficients
        <:
        (bool & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement & usize))
      (fun temp_0_ bytes ->
          let done, out, sampled_coefficients:(bool &
            Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement &
            usize) =
            temp_0_
          in
          let bytes:t_Slice u8 = bytes in
          if ~.done <: bool
          then
            let b1:i32 = cast (bytes.[ sz 0 ] <: u8) <: i32 in
            let b2:i32 = cast (bytes.[ sz 1 ] <: u8) <: i32 in
            let b3:i32 = cast (bytes.[ sz 2 ] <: u8) <: i32 in
            let d1:i32 = ((b2 &. 15l <: i32) <<! 8l <: i32) |. b1 in
            let d2:i32 = (b3 <<! 4l <: i32) |. (b2 >>! 4l <: i32) in
            let out, sampled_coefficients:(Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement &
              usize) =
              if
                // NOTE: We declassify d1 here, and this should be carefully reviewed.
                //       We believe this is safe because d1 is derived from b1 and b2, 
                //       both of which are fresh random inputs, not used anywhere else.
                //       The comparison between d1 and 3329 tells the adversary whether d1
                //       is in the field. This is not secret information, since the
                //       failure of this comparison leads to d1 being discarded,
                declassify d1 <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS &&
                sampled_coefficients <. Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
              then
                let out:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
                  {
                    out with
                    Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      sampled_coefficients
                      d1
                  }
                  <:
                  Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
                in
                out, sampled_coefficients +! sz 1
                <:
                (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement & usize)
              else
                out, sampled_coefficients
                <:
                (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement & usize)
            in
            let out, sampled_coefficients:(Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement &
              usize) =
              if
                // NOTE: We declassify d2 here, and this should be carefully reviewed.
                //       We believe this is safe because d2 is derived from b2 and b3, 
                //       both of which are fresh random inputs, not used anywhere else.
                //       The comparison between d2 and 3329 tells the adversary whether d2
                //       is in the field. This is not secret information, since the
                //       failure of this comparison leads to d2 being discarded,
                declassify d2 <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS &&
                sampled_coefficients <. Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
              then
                let out:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
                  {
                    out with
                    Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                      sampled_coefficients
                      d2
                  }
                  <:
                  Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
                in
                let sampled_coefficients:usize = sampled_coefficients +! sz 1 in
                out, sampled_coefficients
                <:
                (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement & usize)
              else
                out, sampled_coefficients
                <:
                (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement & usize)
            in
            if sampled_coefficients =. Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
            then
              let done:bool = true in
              done, out, sampled_coefficients
              <:
              (bool & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement & usize)
            else
              done, out, sampled_coefficients
              <:
              (bool & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement & usize)
          else
            done, out, sampled_coefficients
            <:
            (bool & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement & usize))
  in
  let _:Prims.unit =
    if ~.done
    then
      let _:Prims.unit = rejection_sampling_panic_with_diagnostic () in
      ()
  in
  let _:Prims.unit = () <: Prims.unit in
  out
