module Hacspec_kyber.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_ZETA: Hacspec_lib.Field.t_PrimeFieldElement 3329us =
  { Hacspec_lib.Field.PrimeFieldElement.f_value = 17us }

let v_INVERSE_OF_128_: Hacspec_lib.Field.t_PrimeFieldElement 3329us =
  { Hacspec_lib.Field.PrimeFieldElement.f_value = 3303us }

let v_NTT_LAYERS: array usize 7sz =
  let list = [2sz; 4sz; 8sz; 16sz; 32sz; 64sz; 128sz] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 7);
  Rust_primitives.Hax.array_of_list list

let bit_rev_7_ (value: u8) : u8 =
  let (reversed: u8):u8 = 0uy in
  let reversed:Prims.unit =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0ul;
              Core.Ops.Range.Range.f_end = Core.Num.v_BITS_under_impl_6 -. 1ul <: u32
            })
        <:
        _)
      reversed
      (fun reversed bit ->
          let reversed:Prims.unit = reversed >>. 1l in
          let reversed:Prims.unit =
            reversed |. ((value &. (1uy >>. bit <: u8) <: u8) <<. bit <: u8)
          in
          reversed)
  in
  reversed

let ntt
      (f:
          Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            256sz)
    : Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz =
  let f__hat:Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    256sz =
    f
  in
  let (k: u8):u8 = 1uy in
  let f__hat, k:(Hacspec_lib.Ring.t_PolynomialRingElement
      (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz &
    Prims.unit) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.rev
              (Core.Slice.iter_under_impl (Rust_primitives.unsize v_NTT_LAYERS <: slice usize)
                <:
                Core.Slice.Iter.t_Iter usize)
            <:
            Core.Iter.Adapters.Rev.t_Rev (Core.Slice.Iter.t_Iter usize))
        <:
        _)
      (f__hat, k)
      (fun (f__hat, k) len ->
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.step_by
                    ({
                        Core.Ops.Range.Range.f_start = 0sz;
                        Core.Ops.Range.Range.f_end
                        =
                        Hacspec_kyber.Parameters.v_COEFFICIENTS_IN_RING_ELEMENT -. len <: _
                      })
                    (2sz *. len <: _)
                  <:
                  Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
              <:
              _)
            (f__hat, k)
            (fun (f__hat, k) start ->
                let zeta:Hacspec_lib.Field.t_PrimeFieldElement 3329us =
                  Hacspec_lib.Field.pow_under_impl_1 v_ZETA (bit_rev_7_ k <: u8)
                in
                let k:Prims.unit = k +. 1uy in
                let f__hat:Hacspec_lib.Ring.t_PolynomialRingElement
                  (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz =
                  Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter
                        ({
                            Core.Ops.Range.Range.f_start = start;
                            Core.Ops.Range.Range.f_end = start +. len <: _
                          })
                      <:
                      _)
                    f__hat
                    (fun f__hat j ->
                        let t =
                          zeta *.
                          (f__hat.[ j +. len <: _ ] <: Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                        in
                        let f__hat:Hacspec_lib.Ring.t_PolynomialRingElement
                          (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz =
                          Rust_primitives.Hax.update_at f__hat
                            (j +. len <: _)
                            ((f__hat.[ j ] <: Hacspec_lib.Field.t_PrimeFieldElement 3329us) -. t
                              <:
                              _)
                        in
                        let f__hat:Hacspec_lib.Ring.t_PolynomialRingElement
                          (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz =
                          Rust_primitives.Hax.update_at f__hat
                            j
                            ((f__hat.[ j ] <: Hacspec_lib.Field.t_PrimeFieldElement 3329us) +. t
                              <:
                              _)
                        in
                        f__hat)
                in
                f__hat, k)
          <:
          (Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
              256sz &
            Prims.unit))
  in
  f__hat

let ntt_inverse
      (f__hat:
          Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            256sz)
    : Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz =
  let f:Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    256sz =
    f__hat
  in
  let (k: u8):u8 = 127uy in
  let f, k:(Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
      256sz &
    Prims.unit) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter v_NTT_LAYERS

        <:
        _)
      (f, k)
      (fun (f, k) len ->
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.step_by
                    ({
                        Core.Ops.Range.Range.f_start = 0sz;
                        Core.Ops.Range.Range.f_end
                        =
                        Hacspec_kyber.Parameters.v_COEFFICIENTS_IN_RING_ELEMENT -. len <: usize
                      })
                    (2sz *. len <: usize)
                  <:
                  Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
              <:
              _)
            (f, k)
            (fun (f, k) start ->
                let zeta:Hacspec_lib.Field.t_PrimeFieldElement 3329us =
                  Hacspec_lib.Field.pow_under_impl_1 v_ZETA (bit_rev_7_ k <: u8)
                in
                let k:Prims.unit = k -. 1uy in
                let f:Hacspec_lib.Ring.t_PolynomialRingElement
                  (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz =
                  Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter
                        ({
                            Core.Ops.Range.Range.f_start = start;
                            Core.Ops.Range.Range.f_end = start +. len <: usize
                          })
                      <:
                      _)
                    f
                    (fun f j ->
                        let t:Hacspec_lib.Field.t_PrimeFieldElement 3329us = f.[ j ] in
                        let f:Hacspec_lib.Ring.t_PolynomialRingElement
                          (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz =
                          Rust_primitives.Hax.update_at f
                            j
                            (t +.
                              (f.[ j +. len <: usize ]
                                <:
                                Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                              <:
                              _)
                        in
                        let f:Hacspec_lib.Ring.t_PolynomialRingElement
                          (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz =
                          Rust_primitives.Hax.update_at f
                            (j +. len <: usize)
                            (zeta *.
                              ((f.[ j +. len <: usize ]
                                  <:
                                  Hacspec_lib.Field.t_PrimeFieldElement 3329us) -.
                                t
                                <:
                                _)
                              <:
                              _)
                        in
                        f)
                in
                f, k)
          <:
          (Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
              256sz &
            Prims.unit))
  in
  let f:Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    256sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end
              =
              Core.Slice.len_under_impl (Rust_primitives.unsize (Hacspec_lib.Ring.coefficients_under_impl_2
                        f
                      <:
                      array (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz)
                  <:
                  slice (Hacspec_lib.Field.t_PrimeFieldElement 3329us))
              <:
              usize
            })
        <:
        _)
      f
      (fun f i ->
          Rust_primitives.Hax.update_at f
            i
            ((f.[ i ] <: Hacspec_lib.Field.t_PrimeFieldElement 3329us) *. v_INVERSE_OF_128_ <: _)
          <:
          Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            256sz)
  in
  f

let multiply_ntts
      (f__hat g_hat:
          Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            256sz)
    : Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz =
  let h_hat:Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    256sz =
    Hacspec_lib.Ring.v_ZERO_under_impl_2
  in
  let h_hat:Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    256sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = 128sz
            })
        <:
        _)
      h_hat
      (fun h_hat i ->
          let binomial_product:(Hacspec_lib.Field.t_PrimeFieldElement 3329us &
            Hacspec_lib.Field.t_PrimeFieldElement 3329us) =
            base_case_multiply ((f__hat.[ 2sz *. i <: usize ]
                  <:
                  Hacspec_lib.Field.t_PrimeFieldElement 3329us),
                (f__hat.[ (2sz *. i <: usize) +. 1sz <: usize ]
                  <:
                  Hacspec_lib.Field.t_PrimeFieldElement 3329us))
              ((g_hat.[ 2sz *. i <: usize ] <: Hacspec_lib.Field.t_PrimeFieldElement 3329us),
                (g_hat.[ (2sz *. i <: usize) +. 1sz <: usize ]
                  <:
                  Hacspec_lib.Field.t_PrimeFieldElement 3329us))
              (Hacspec_lib.Field.pow_under_impl_1 v_ZETA
                  ((2uy *. (bit_rev_7_ (Hacspec_lib.PanickingIntegerCasts.as_u8 i <: u8) <: u8)
                      <:
                      u8) +.
                    1uy
                    <:
                    u8)
                <:
                Hacspec_lib.Field.t_PrimeFieldElement 3329us)
          in
          let h_hat:Hacspec_lib.Ring.t_PolynomialRingElement
            (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz =
            Rust_primitives.Hax.update_at h_hat (2sz *. i <: usize) binomial_product._1
          in
          let h_hat:Hacspec_lib.Ring.t_PolynomialRingElement
            (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz =
            Rust_primitives.Hax.update_at h_hat
              ((2sz *. i <: usize) +. 1sz <: usize)
              binomial_product._2
          in
          h_hat)
  in
  h_hat

let t_KyberBinomial =
  (Hacspec_lib.Field.t_PrimeFieldElement 3329us & Hacspec_lib.Field.t_PrimeFieldElement 3329us)

let base_case_multiply
      (a b:
          (Hacspec_lib.Field.t_PrimeFieldElement 3329us &
            Hacspec_lib.Field.t_PrimeFieldElement 3329us))
      (zeta: Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    : (Hacspec_lib.Field.t_PrimeFieldElement 3329us & Hacspec_lib.Field.t_PrimeFieldElement 3329us) =
  let c:(Hacspec_lib.Field.t_PrimeFieldElement 3329us & Hacspec_lib.Field.t_PrimeFieldElement 3329us
  ) =
    Hacspec_lib.Field.FieldElement.v_ZERO, Hacspec_lib.Field.FieldElement.v_ZERO
  in
  let c:(Hacspec_lib.Field.t_PrimeFieldElement 3329us & Hacspec_lib.Field.t_PrimeFieldElement 3329us
  ) =
    { c with _1 = (a._1 *. b._1 <: _) +. ((a._2 *. b._2 <: _) *. zeta <: _) }
  in
  let c:(Hacspec_lib.Field.t_PrimeFieldElement 3329us & Hacspec_lib.Field.t_PrimeFieldElement 3329us
  ) =
    { c with _2 = (a._1 *. b._2 <: _) +. (a._2 *. b._1 <: _) }
  in
  c

let vector_ntt
      (vector: Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz)
    : Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz =
  let vector_as_ntt:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    256sz
    3sz =
    Hacspec_lib.Vector.v_ZERO_under_impl
  in
  let vector_as_ntt:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    256sz
    3sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Hacspec_lib.Vector.into_iter_under_impl vector
                <:
                Core.Array.Iter.t_IntoIter
                  (Hacspec_lib.Ring.t_PolynomialRingElement
                      (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz) 3sz)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Array.Iter.t_IntoIter
                (Hacspec_lib.Ring.t_PolynomialRingElement
                    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz) 3sz))
        <:
        _)
      vector_as_ntt
      (fun vector_as_ntt (i, re) ->
          Rust_primitives.Hax.update_at vector_as_ntt
            i
            (ntt re
              <:
              Hacspec_lib.Ring.t_PolynomialRingElement
                (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz)
          <:
          Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz)
  in
  vector_as_ntt

let vector_inverse_ntt
      (vector_as_ntt:
          Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz)
    : Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz =
  let vector:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz =
    Hacspec_lib.Vector.v_ZERO_under_impl
  in
  let vector:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Hacspec_lib.Vector.into_iter_under_impl vector_as_ntt
                <:
                Core.Array.Iter.t_IntoIter
                  (Hacspec_lib.Ring.t_PolynomialRingElement
                      (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz) 3sz)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Array.Iter.t_IntoIter
                (Hacspec_lib.Ring.t_PolynomialRingElement
                    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz) 3sz))
        <:
        _)
      vector
      (fun vector (i, re_ntt) ->
          Rust_primitives.Hax.update_at vector
            i
            (ntt_inverse re_ntt
              <:
              Hacspec_lib.Ring.t_PolynomialRingElement
                (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz)
          <:
          Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz)
  in
  vector