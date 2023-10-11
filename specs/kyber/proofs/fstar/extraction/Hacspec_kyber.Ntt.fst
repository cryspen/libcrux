module Hacspec_kyber.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_ZETA: Hacspec_lib.Field.t_PrimeFieldElement 3329us = { Hacspec_lib.Field.f_value = 17us }

let v_INVERSE_OF_128_: Hacspec_lib.Field.t_PrimeFieldElement 3329us =
  { Hacspec_lib.Field.f_value = 3303us }

let v_NTT_LAYERS: array usize (sz 7) =
  let list = [sz 2; sz 4; sz 8; sz 16; sz 32; sz 64; sz 128] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 7);
  Rust_primitives.Hax.array_of_list list

let bit_rev_7_ (value: u8) : u8 =
  let (reversed: u8):u8 = 0uy in
  let reversed:u8 =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = 0ul;
              Core.Ops.Range.f_end = Core.Num.impl_6__BITS -! 1ul <: u32
            })
        <:
        (Core.Iter.Traits.Collect.impl (Core.Ops.Range.t_Range u32)).f_IntoIter)
      reversed
      (fun reversed bit ->
          let reversed:u8 = reversed <<! 1l in
          let reversed:u8 = reversed |. ((value &. (1uy <<! bit <: u8) <: u8) >>! bit <: u8) in
          reversed)
  in
  reversed

let ntt
      (f:
          Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            (sz 256))
    : Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
      (sz 256) =
  let ff_hat:Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    (sz 256) =
    f
  in
  let (k: u8):u8 = 1uy in
  let ff_hat, k:(Hacspec_lib.Ring.t_PolynomialRingElement
      (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) &
    u8) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_rev
              (Core.Slice.impl__iter (Rust_primitives.unsize v_NTT_LAYERS <: slice usize)
                <:
                Core.Slice.Iter.t_Iter usize)
            <:
            Core.Iter.Adapters.Rev.t_Rev (Core.Slice.Iter.t_Iter usize))
        <:
        (Core.Iter.Traits.Collect.impl (Core.Iter.Adapters.Rev.t_Rev (Core.Slice.Iter.t_Iter usize))
        )
          .f_IntoIter)
      (ff_hat, k)
      (fun (ff_hat, k) len ->
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_step_by
                    ({
                        Core.Ops.Range.f_start = sz 0;
                        Core.Ops.Range.f_end
                        =
                        Hacspec_kyber.Parameters.v_COEFFICIENTS_IN_RING_ELEMENT -! len
                        <:
                        (Core.Ops.Arith.impl_71).f_Output
                      })
                    (sz 2 *! len <: (Core.Ops.Arith.impl_127).f_Output)
                  <:
                  Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
              <:
              (Core.Iter.Traits.Collect.impl
                (Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize)))
                .f_IntoIter)
            (ff_hat, k)
            (fun (ff_hat, k) start ->
                let zeta:Hacspec_lib.Field.t_PrimeFieldElement 3329us =
                  Hacspec_lib.Field.impl_1__pow v_ZETA (bit_rev_7_ k <: u8)
                in
                let k:u8 = k +! 1uy in
                let ff_hat:Hacspec_lib.Ring.t_PolynomialRingElement
                  (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
                  Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter ({
                            Core.Ops.Range.f_start = start;
                            Core.Ops.Range.f_end = start +! len <: (Core.Ops.Arith.impl_15).f_Output
                          })
                      <:
                      (Core.Iter.Traits.Collect.impl (Core.Ops.Range.t_Range usize)).f_IntoIter)
                    ff_hat
                    (fun ff_hat j ->
                        let t =
                          zeta *!
                          (ff_hat.[ j +! len <: (Core.Ops.Arith.impl_15).f_Output ]
                            <:
                            Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                        in
                        let ff_hat:Hacspec_lib.Ring.t_PolynomialRingElement
                          (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
                          Rust_primitives.Hax.update_at ff_hat
                            (j +! len <: (Core.Ops.Arith.impl_15).f_Output)
                            ((ff_hat.[ j ] <: Hacspec_lib.Field.t_PrimeFieldElement 3329us) -! t
                              <:
                              (Hacspec_lib.Field.impl_8 3329us).f_Output)
                        in
                        let ff_hat:Hacspec_lib.Ring.t_PolynomialRingElement
                          (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
                          Rust_primitives.Hax.update_at ff_hat
                            j
                            ((ff_hat.[ j ] <: Hacspec_lib.Field.t_PrimeFieldElement 3329us) +! t
                              <:
                              (Hacspec_lib.Field.impl_7 3329us).f_Output)
                        in
                        ff_hat)
                in
                ff_hat, k)
          <:
          (Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
              (sz 256) &
            u8))
  in
  ff_hat

let ntt_inverse
      (ff_hat:
          Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            (sz 256))
    : Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
      (sz 256) =
  let f:Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    (sz 256) =
    ff_hat
  in
  let (k: u8):u8 = 127uy in
  let f, k:(Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
      (sz 256) &
    u8) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter v_NTT_LAYERS
        <:
        (Core.Array.Iter.impl usize (sz 7)).f_IntoIter)
      (f, k)
      (fun (f, k) len ->
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_step_by
                    ({
                        Core.Ops.Range.f_start = sz 0;
                        Core.Ops.Range.f_end
                        =
                        Hacspec_kyber.Parameters.v_COEFFICIENTS_IN_RING_ELEMENT -! len <: usize
                      })
                    (sz 2 *! len <: usize)
                  <:
                  Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
              <:
              (Core.Iter.Traits.Collect.impl
                (Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize)))
                .f_IntoIter)
            (f, k)
            (fun (f, k) start ->
                let zeta:Hacspec_lib.Field.t_PrimeFieldElement 3329us =
                  Hacspec_lib.Field.impl_1__pow v_ZETA (bit_rev_7_ k <: u8)
                in
                let k:u8 = k -! 1uy in
                let f:Hacspec_lib.Ring.t_PolynomialRingElement
                  (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
                  Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter ({
                            Core.Ops.Range.f_start = start;
                            Core.Ops.Range.f_end = start +! len <: usize
                          })
                      <:
                      (Core.Iter.Traits.Collect.impl (Core.Ops.Range.t_Range usize)).f_IntoIter)
                    f
                    (fun f j ->
                        let t:Hacspec_lib.Field.t_PrimeFieldElement 3329us = f.[ j ] in
                        let f:Hacspec_lib.Ring.t_PolynomialRingElement
                          (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
                          Rust_primitives.Hax.update_at f
                            j
                            (t +!
                              (f.[ j +! len <: usize ]
                                <:
                                Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                              <:
                              (Hacspec_lib.Field.impl_7 3329us).f_Output)
                        in
                        let f:Hacspec_lib.Ring.t_PolynomialRingElement
                          (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
                          Rust_primitives.Hax.update_at f
                            (j +! len <: usize)
                            (zeta *!
                              ((f.[ j +! len <: usize ]
                                  <:
                                  Hacspec_lib.Field.t_PrimeFieldElement 3329us) -!
                                t
                                <:
                                (Hacspec_lib.Field.impl_8 3329us).f_Output)
                              <:
                              (Hacspec_lib.Field.impl_9 3329us).f_Output)
                        in
                        f)
                in
                f, k)
          <:
          (Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
              (sz 256) &
            u8))
  in
  let f:Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    (sz 256) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end
              =
              Core.Slice.impl__len (Rust_primitives.unsize (Hacspec_lib.Ring.impl_2__coefficients f
                      <:
                      array (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256))
                  <:
                  slice (Hacspec_lib.Field.t_PrimeFieldElement 3329us))
              <:
              usize
            })
        <:
        (Core.Iter.Traits.Collect.impl (Core.Ops.Range.t_Range usize)).f_IntoIter)
      f
      (fun f i ->
          Rust_primitives.Hax.update_at f
            i
            ((f.[ i ] <: Hacspec_lib.Field.t_PrimeFieldElement 3329us) *! v_INVERSE_OF_128_
              <:
              (Hacspec_lib.Field.impl_9 3329us).f_Output)
          <:
          Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            (sz 256))
  in
  f

let multiply_ntts
      (ff_hat g_hat:
          Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            (sz 256))
    : Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
      (sz 256) =
  let h_hat:Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    (sz 256) =
    Hacspec_lib.Ring.impl_2__ZERO
  in
  let h_hat:Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    (sz 256) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 128
            })
        <:
        (Core.Iter.Traits.Collect.impl (Core.Ops.Range.t_Range usize)).f_IntoIter)
      h_hat
      (fun h_hat i ->
          let binomial_product:(Hacspec_lib.Field.t_PrimeFieldElement 3329us &
            Hacspec_lib.Field.t_PrimeFieldElement 3329us) =
            base_case_multiply ((ff_hat.[ sz 2 *! i <: usize ]
                  <:
                  Hacspec_lib.Field.t_PrimeFieldElement 3329us),
                (ff_hat.[ (sz 2 *! i <: usize) +! sz 1 <: usize ]
                  <:
                  Hacspec_lib.Field.t_PrimeFieldElement 3329us))
              ((g_hat.[ sz 2 *! i <: usize ] <: Hacspec_lib.Field.t_PrimeFieldElement 3329us),
                (g_hat.[ (sz 2 *! i <: usize) +! sz 1 <: usize ]
                  <:
                  Hacspec_lib.Field.t_PrimeFieldElement 3329us))
              (Hacspec_lib.Field.impl_1__pow v_ZETA
                  ((2uy *! (bit_rev_7_ (Hacspec_lib.f_as_u8 i <: u8) <: u8) <: u8) +! 1uy <: u8)
                <:
                Hacspec_lib.Field.t_PrimeFieldElement 3329us)
          in
          let h_hat:Hacspec_lib.Ring.t_PolynomialRingElement
            (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
            Rust_primitives.Hax.update_at h_hat (sz 2 *! i <: usize) binomial_product._1
          in
          let h_hat:Hacspec_lib.Ring.t_PolynomialRingElement
            (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
            Rust_primitives.Hax.update_at h_hat
              ((sz 2 *! i <: usize) +! sz 1 <: usize)
              binomial_product._2
          in
          h_hat)
  in
  h_hat

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
    {
      c with
      _1
      =
      (a._1 *! b._1 <: (Hacspec_lib.Field.impl_9 3329us).f_Output) +!
      ((a._2 *! b._2 <: (Hacspec_lib.Field.impl_9 3329us).f_Output) *! zeta
        <:
        (Hacspec_lib.Field.impl_9 3329us).f_Output)
    }
  in
  let c:(Hacspec_lib.Field.t_PrimeFieldElement 3329us & Hacspec_lib.Field.t_PrimeFieldElement 3329us
  ) =
    {
      c with
      _2
      =
      (a._1 *! b._2 <: (Hacspec_lib.Field.impl_9 3329us).f_Output) +!
      (a._2 *! b._1 <: (Hacspec_lib.Field.impl_9 3329us).f_Output)
    }
  in
  c

let vector_ntt
      (vector:
          Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3)
        )
    : Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3) =
  let vector_as_ntt:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    (sz 256)
    (sz 3) =
    Hacspec_lib.Vector.impl__ZERO
  in
  let vector_as_ntt:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    (sz 256)
    (sz 3) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Hacspec_lib.Vector.impl__into_iter vector
                <:
                Core.Array.Iter.t_IntoIter
                  (Hacspec_lib.Ring.t_PolynomialRingElement
                      (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256)) (sz 3))
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Array.Iter.t_IntoIter
                (Hacspec_lib.Ring.t_PolynomialRingElement
                    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256)) (sz 3)))
        <:
        (Core.Iter.Traits.Collect.impl
          (Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Array.Iter.t_IntoIter
                (Hacspec_lib.Ring.t_PolynomialRingElement
                    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256)) (sz 3))))
          .f_IntoIter)
      vector_as_ntt
      (fun vector_as_ntt (i, re) ->
          Rust_primitives.Hax.update_at vector_as_ntt
            i
            (ntt re
              <:
              Hacspec_lib.Ring.t_PolynomialRingElement
                (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256))
          <:
          Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3)
      )
  in
  vector_as_ntt

let vector_inverse_ntt
      (vector_as_ntt:
          Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3)
        )
    : Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3) =
  let vector:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    (sz 256)
    (sz 3) =
    Hacspec_lib.Vector.impl__ZERO
  in
  let vector:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    (sz 256)
    (sz 3) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Hacspec_lib.Vector.impl__into_iter vector_as_ntt
                <:
                Core.Array.Iter.t_IntoIter
                  (Hacspec_lib.Ring.t_PolynomialRingElement
                      (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256)) (sz 3))
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Array.Iter.t_IntoIter
                (Hacspec_lib.Ring.t_PolynomialRingElement
                    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256)) (sz 3)))
        <:
        (Core.Iter.Traits.Collect.impl
          (Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Array.Iter.t_IntoIter
                (Hacspec_lib.Ring.t_PolynomialRingElement
                    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256)) (sz 3))))
          .f_IntoIter)
      vector
      (fun vector (i, re_ntt) ->
          Rust_primitives.Hax.update_at vector
            i
            (ntt_inverse re_ntt
              <:
              Hacspec_lib.Ring.t_PolynomialRingElement
                (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256))
          <:
          Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3)
      )
  in
  vector