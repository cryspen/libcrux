module Hacspec_kyber.Sampling
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let sum_coins (coins: t_Slice u8) : Hacspec_lib.Field.t_PrimeFieldElement 3329us =
  let (sum: u8):u8 = 0uy in
  let sum:u8 =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Slice.impl__iter coins

            <:
            Core.Slice.Iter.t_Iter u8)
        <:
        Core.Slice.Iter.t_Iter u8)
      sum
      (fun sum coin ->
          let sum:u8 = sum in
          let coin:u8 = coin in
          Core.Ops.Arith.f_add_assign sum coin <: u8)
  in
  Core.Convert.f_into sum

let sample_poly_cbd (eta: usize) (bytes: t_Slice u8)
    : Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
      (sz 256) =
  let _:Prims.unit =
    match Core.Slice.impl__len bytes, eta *! sz 64 <: (usize & usize) with
    | left_val, right_val ->
      if ~.(left_val =. right_val <: bool)
      then
        let kind:Core.Panicking.t_AssertKind =
          Core.Panicking.AssertKind_Eq <: Core.Panicking.t_AssertKind
        in
        Rust_primitives.Hax.never_to_any (Core.Panicking.assert_failed kind
              left_val
              right_val
              (Core.Option.Option_None <: Core.Option.t_Option Core.Fmt.t_Arguments)
            <:
            Rust_primitives.Hax.t_Never)
  in
  let bits:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = Hacspec_kyber.Serialize.bytes_to_bits bytes in
  let bits:Core.Slice.Iter.t_Chunks u8 =
    Core.Slice.impl__chunks (Core.Ops.Deref.f_deref bits <: t_Slice u8) eta
  in
  let
  (f:
    Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256)
  ):Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256)
  =
    Hacspec_lib.Ring.impl_2__ZERO
  in
  let bits, f:(Core.Slice.Iter.t_Chunks u8 &
    Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256)
  ) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Hacspec_lib.Ring.impl_2__len (sz 256) f <: usize
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      (bits, f
        <:
        (Core.Slice.Iter.t_Chunks u8 &
          Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            (sz 256)))
      (fun temp_0_ i ->
          let bits, f:(Core.Slice.Iter.t_Chunks u8 &
            Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
              (sz 256)) =
            temp_0_
          in
          let i:usize = i in
          let tmp0, out:(Core.Slice.Iter.t_Chunks u8 & Core.Option.t_Option (t_Slice u8)) =
            Core.Iter.Traits.Iterator.f_next bits
          in
          let bits:Core.Slice.Iter.t_Chunks u8 = tmp0 in
          let hoist1:Core.Option.t_Option (t_Slice u8) = out in
          let hoist2:t_Slice u8 = Core.Option.impl__unwrap hoist1 in
          let (x: Hacspec_lib.Field.t_PrimeFieldElement 3329us):Hacspec_lib.Field.t_PrimeFieldElement
          3329us =
            sum_coins hoist2
          in
          let tmp0, out:(Core.Slice.Iter.t_Chunks u8 & Core.Option.t_Option (t_Slice u8)) =
            Core.Iter.Traits.Iterator.f_next bits
          in
          let bits:Core.Slice.Iter.t_Chunks u8 = tmp0 in
          let hoist3:Core.Option.t_Option (t_Slice u8) = out in
          let hoist4:t_Slice u8 = Core.Option.impl__unwrap hoist3 in
          let (y: Hacspec_lib.Field.t_PrimeFieldElement 3329us):Hacspec_lib.Field.t_PrimeFieldElement
          3329us =
            sum_coins hoist4
          in
          let f:Hacspec_lib.Ring.t_PolynomialRingElement
            (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize f
              i
              (x -! y <: Hacspec_lib.Field.t_PrimeFieldElement 3329us)
          in
          bits, f
          <:
          (Core.Slice.Iter.t_Chunks u8 &
            Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
              (sz 256)))
  in
  f

let sample_ntt (bytes: t_Array u8 (sz 840))
    : Core.Result.t_Result
      (Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
          (sz 256)) Hacspec_kyber.t_BadRejectionSamplingRandomnessError =
  let (sampled_coefficients: usize):usize = sz 0 in
  let
  (a_hat:
    Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256)
  ):Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256)
  =
    Hacspec_lib.Ring.impl_2__ZERO
  in
  let a_hat, sampled_coefficients:(Hacspec_lib.Ring.t_PolynomialRingElement
      (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) &
    usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Slice.impl__chunks (
                Rust_primitives.unsize bytes <: t_Slice u8)
              (sz 3)
            <:
            Core.Slice.Iter.t_Chunks u8)
        <:
        Core.Slice.Iter.t_Chunks u8)
      (a_hat, sampled_coefficients
        <:
        (Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            (sz 256) &
          usize))
      (fun temp_0_ byte_chunk ->
          let a_hat, sampled_coefficients:(Hacspec_lib.Ring.t_PolynomialRingElement
              (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) &
            usize) =
            temp_0_
          in
          let byte_chunk:t_Slice u8 = byte_chunk in
          let b:u16 = Core.Convert.f_from (byte_chunk.[ sz 0 ] <: u8) in
          let b1:u16 = Core.Convert.f_from (byte_chunk.[ sz 1 ] <: u8) in
          let b2:u16 = Core.Convert.f_from (byte_chunk.[ sz 2 ] <: u8) in
          let d1:u16 = b +! (256us *! (b1 %! 16us <: u16) <: u16) in
          let d2:u16 = (b1 /! 16us <: u16) +! (16us *! b2 <: u16) in
          let a_hat, sampled_coefficients:(Hacspec_lib.Ring.t_PolynomialRingElement
              (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) &
            usize) =
            if
              d1 <. Hacspec_kyber.Parameters.v_FIELD_MODULUS &&
              sampled_coefficients <. (Hacspec_lib.Ring.impl_2__len (sz 256) a_hat <: usize)
            then
              let a_hat:Hacspec_lib.Ring.t_PolynomialRingElement
                (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a_hat
                  sampled_coefficients
                  (Core.Convert.f_into d1 <: Hacspec_lib.Field.t_PrimeFieldElement 3329us)
              in
              a_hat, sampled_coefficients +! sz 1
              <:
              (Hacspec_lib.Ring.t_PolynomialRingElement
                  (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) &
                usize)
            else
              a_hat, sampled_coefficients
              <:
              (Hacspec_lib.Ring.t_PolynomialRingElement
                  (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) &
                usize)
          in
          if
            d2 <. Hacspec_kyber.Parameters.v_FIELD_MODULUS &&
            sampled_coefficients <. (Hacspec_lib.Ring.impl_2__len (sz 256) a_hat <: usize)
          then
            let a_hat:Hacspec_lib.Ring.t_PolynomialRingElement
              (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a_hat
                sampled_coefficients
                (Core.Convert.f_into d2 <: Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            in
            let sampled_coefficients:usize = sampled_coefficients +! sz 1 in
            a_hat, sampled_coefficients
            <:
            (Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                (sz 256) &
              usize)
          else
            a_hat, sampled_coefficients
            <:
            (Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                (sz 256) &
              usize))
  in
  if sampled_coefficients =. (Hacspec_lib.Ring.impl_2__len (sz 256) a_hat <: usize)
  then
    Core.Result.Result_Ok a_hat
    <:
    Core.Result.t_Result
      (Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
          (sz 256)) Hacspec_kyber.t_BadRejectionSamplingRandomnessError
  else
    Core.Result.Result_Err
    (Hacspec_kyber.BadRejectionSamplingRandomnessError
      <:
      Hacspec_kyber.t_BadRejectionSamplingRandomnessError)
    <:
    Core.Result.t_Result
      (Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
          (sz 256)) Hacspec_kyber.t_BadRejectionSamplingRandomnessError
