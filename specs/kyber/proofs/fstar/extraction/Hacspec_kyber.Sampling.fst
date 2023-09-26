module Hacspec_kyber.Sampling
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let sample_ntt (bytes: array u8 840sz)
    : Core.Result.t_Result
      (Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz
      ) Hacspec_kyber.t_BadRejectionSamplingRandomnessError =
  let (sampled_coefficients: usize):usize = 0sz in
  let
  (a_hat:
    Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz):Hacspec_lib.Ring.t_PolynomialRingElement
    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz =
    Hacspec_lib.Ring.v_ZERO_under_impl_2
  in
  let a_hat, sampled_coefficients:(Hacspec_lib.Ring.t_PolynomialRingElement
      (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz &
    Prims.unit) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Slice.chunks_under_impl
              (Rust_primitives.unsize bytes <: slice u8)
              3sz
            <:
            Core.Slice.Iter.t_Chunks u8)
        <:
        _)
      (a_hat, sampled_coefficients)
      (fun (a_hat, sampled_coefficients) byte_chunk ->
          let b:u16 = Core.Convert.From.from (byte_chunk.[ 0sz ] <: u8) in
          let b1:u16 = Core.Convert.From.from (byte_chunk.[ 1sz ] <: u8) in
          let b2:u16 = Core.Convert.From.from (byte_chunk.[ 2sz ] <: u8) in
          let d1:u16 = b +. (256us *. (b1 %. 16us <: u16) <: u16) in
          let d2:u16 = (b1 /. 16us <: u16) +. (16us *. b2 <: u16) in
          let a_hat, sampled_coefficients:(Hacspec_lib.Ring.t_PolynomialRingElement
              (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz &
            Prims.unit) =
            if
              Prims.op_AmpAmp (d1 <. Hacspec_kyber.Parameters.v_FIELD_MODULUS)
                (sampled_coefficients <. (Hacspec_lib.Ring.len_under_impl_2 a_hat <: usize))
            then
              let a_hat:Hacspec_lib.Ring.t_PolynomialRingElement
                (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz =
                Rust_primitives.Hax.update_at a_hat
                  sampled_coefficients
                  (Core.Convert.Into.into d1 <: Hacspec_lib.Field.t_PrimeFieldElement 3329us)
              in
              a_hat, sampled_coefficients +. 1sz
            else a_hat, sampled_coefficients
          in
          if
            Prims.op_AmpAmp (d2 <. Hacspec_kyber.Parameters.v_FIELD_MODULUS)
              (sampled_coefficients <. (Hacspec_lib.Ring.len_under_impl_2 a_hat <: usize))
          then
            let a_hat:Hacspec_lib.Ring.t_PolynomialRingElement
              (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz =
              Rust_primitives.Hax.update_at a_hat
                sampled_coefficients
                (Core.Convert.Into.into d2 <: Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            in
            let sampled_coefficients:Prims.unit = sampled_coefficients +. 1sz in
            a_hat, sampled_coefficients
          else a_hat, sampled_coefficients)
  in
  if sampled_coefficients =. (Hacspec_lib.Ring.len_under_impl_2 a_hat <: usize)
  then Core.Result.Result_Ok a_hat
  else Core.Result.Result_Err Hacspec_kyber.BadRejectionSamplingRandomnessError

let sum_coins (coins: slice u8) : Hacspec_lib.Field.t_PrimeFieldElement 3329us =
  let (sum: u8):u8 = 0uy in
  let sum:u8 =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Slice.iter_under_impl
              coins
            <:
            Core.Slice.Iter.t_Iter u8)
        <:
        _)
      sum
      (fun sum coin -> Core.Ops.Arith.AddAssign.add_assign sum coin <: u8)
  in
  Core.Convert.Into.into sum

let sample_poly_cbd (eta: usize) (bytes: slice u8)
    : Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz =
  let _:Prims.unit =
    match Core.Slice.len_under_impl bytes, eta *. 64sz with
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
    Core.Slice.chunks_under_impl (Core.Ops.Deref.Deref.deref bits <: slice u8) eta
  in
  let
  (f: Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz):Hacspec_lib.Ring.t_PolynomialRingElement
    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz =
    Hacspec_lib.Ring.v_ZERO_under_impl_2
  in
  let bits, f:(Core.Slice.Iter.t_Chunks u8 &
    Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Hacspec_lib.Ring.len_under_impl_2 f <: usize
            })
        <:
        _)
      (bits, f)
      (fun (bits, f) i ->
          let tmp0, out:(Core.Slice.Iter.t_Chunks u8 & Core.Option.t_Option _) =
            Core.Iter.Traits.Iterator.Iterator.next bits
          in
          let bits:Core.Slice.Iter.t_Chunks u8 = tmp0 in
          let hoist9:(Core.Slice.Iter.t_Chunks u8 & Core.Option.t_Option _) = out in
          let hoist10:slice u8 = Core.Option.unwrap_under_impl hoist9 in
          let (x: Hacspec_lib.Field.t_PrimeFieldElement 3329us):Hacspec_lib.Field.t_PrimeFieldElement
          3329us =
            sum_coins hoist10
          in
          let tmp0, out:(Core.Slice.Iter.t_Chunks u8 & Core.Option.t_Option _) =
            Core.Iter.Traits.Iterator.Iterator.next bits
          in
          let bits:Core.Slice.Iter.t_Chunks u8 = tmp0 in
          let hoist11:(Core.Slice.Iter.t_Chunks u8 & Core.Option.t_Option _) = out in
          let hoist12:slice u8 = Core.Option.unwrap_under_impl hoist11 in
          let (y: Hacspec_lib.Field.t_PrimeFieldElement 3329us):Hacspec_lib.Field.t_PrimeFieldElement
          3329us =
            sum_coins hoist12
          in
          let f:Hacspec_lib.Ring.t_PolynomialRingElement
            (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz =
            Rust_primitives.Hax.update_at f i (x -. y <: _)
          in
          bits, f)
  in
  f