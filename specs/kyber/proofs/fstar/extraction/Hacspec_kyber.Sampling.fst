module Hacspec_kyber.Sampling
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let sample_ntt (bytes: array u8 (sz 840))
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
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Slice.impl__chunks
              (Rust_primitives.unsize bytes <: slice u8)
              (sz 3)
            <:
            Core.Slice.Iter.t_Chunks u8)
        <:
        (Core.Iter.Traits.Collect.impl (Core.Slice.Iter.t_Chunks u8)).f_IntoIter)
      (a_hat, sampled_coefficients)
      (fun (a_hat, sampled_coefficients) byte_chunk ->
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
              sampled_coefficients <. (Hacspec_lib.Ring.impl_2__len a_hat <: usize)
            then
              let a_hat:Hacspec_lib.Ring.t_PolynomialRingElement
                (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
                Rust_primitives.Hax.update_at a_hat
                  sampled_coefficients
                  (Core.Convert.f_into d1 <: Hacspec_lib.Field.t_PrimeFieldElement 3329us)
              in
              a_hat, sampled_coefficients +! sz 1
            else a_hat, sampled_coefficients
          in
          if
            d2 <. Hacspec_kyber.Parameters.v_FIELD_MODULUS &&
            sampled_coefficients <. (Hacspec_lib.Ring.impl_2__len a_hat <: usize)
          then
            let a_hat:Hacspec_lib.Ring.t_PolynomialRingElement
              (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
              Rust_primitives.Hax.update_at a_hat
                sampled_coefficients
                (Core.Convert.f_into d2 <: Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            in
            let sampled_coefficients:usize = sampled_coefficients +! sz 1 in
            a_hat, sampled_coefficients
          else a_hat, sampled_coefficients)
  in
  if sampled_coefficients =. (Hacspec_lib.Ring.impl_2__len a_hat <: usize)
  then Core.Result.Result_Ok a_hat
  else Core.Result.Result_Err Hacspec_kyber.BadRejectionSamplingRandomnessError

let sum_coins (coins: slice u8) : Hacspec_lib.Field.t_PrimeFieldElement 3329us =
  let (sum: u8):u8 = 0uy in
  let sum:u8 =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Slice.impl__iter
              coins
            <:
            Core.Slice.Iter.t_Iter u8)
        <:
        (Core.Iter.Traits.Collect.impl (Core.Slice.Iter.t_Iter u8)).f_IntoIter)
      sum
      (fun sum coin -> Core.Ops.Arith.f_add_assign sum coin <: u8)
  in
  Core.Convert.f_into sum

let sample_poly_cbd (eta: usize) (bytes: slice u8)
    : Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
      (sz 256) =
  let _:Prims.unit =
    match Core.Slice.impl__len bytes, eta *! sz 64 with
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
  let bits:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = Hacspec_kyber.Serialize.bytes_to_bits bytes in
  let bits:Core.Slice.Iter.t_Chunks u8 =
    Core.Slice.impl__chunks (Core.Ops.Deref.f_deref bits <: slice u8) eta
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
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Hacspec_lib.Ring.impl_2__len f <: usize
            })
        <:
        (Core.Iter.Traits.Collect.impl (Core.Ops.Range.t_Range usize)).f_IntoIter)
      (bits, f)
      (fun (bits, f) i ->
          let tmp0, out:(Core.Slice.Iter.t_Chunks u8 &
            Core.Option.t_Option (Core.Slice.Iter.impl_70 u8).f_Item) =
            Core.Iter.Traits.Iterator.f_next bits
          in
          let bits:Core.Slice.Iter.t_Chunks u8 = tmp0 in
          let hoist9:Core.Option.t_Option (Core.Slice.Iter.impl_70 u8).f_Item = out in
          let hoist10:slice u8 = Core.Option.impl__unwrap hoist9 in
          let (x: Hacspec_lib.Field.t_PrimeFieldElement 3329us):Hacspec_lib.Field.t_PrimeFieldElement
          3329us =
            sum_coins hoist10
          in
          let tmp0, out:(Core.Slice.Iter.t_Chunks u8 &
            Core.Option.t_Option (Core.Slice.Iter.impl_70 u8).f_Item) =
            Core.Iter.Traits.Iterator.f_next bits
          in
          let bits:Core.Slice.Iter.t_Chunks u8 = tmp0 in
          let hoist11:Core.Option.t_Option (Core.Slice.Iter.impl_70 u8).f_Item = out in
          let hoist12:slice u8 = Core.Option.impl__unwrap hoist11 in
          let (y: Hacspec_lib.Field.t_PrimeFieldElement 3329us):Hacspec_lib.Field.t_PrimeFieldElement
          3329us =
            sum_coins hoist12
          in
          let f:Hacspec_lib.Ring.t_PolynomialRingElement
            (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
            Rust_primitives.Hax.update_at f i (x -! y <: (Hacspec_lib.Field.impl_8 3329us).f_Output)
          in
          bits, f)
  in
  f