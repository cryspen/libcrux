module Hacspec_kyber.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_NTT_LAYERS: t_Array usize (sz 7) =
  let list = [sz 2; sz 4; sz 8; sz 16; sz 32; sz 64; sz 128] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 7);
  Rust_primitives.Hax.array_of_list list

let base_case_multiply
      (a b:
          (Hacspec_lib.Field.t_PrimeFieldElement 3329us &
            Hacspec_lib.Field.t_PrimeFieldElement 3329us))
      (zeta: Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    : (Hacspec_lib.Field.t_PrimeFieldElement 3329us & Hacspec_lib.Field.t_PrimeFieldElement 3329us) =
  let c:(Hacspec_lib.Field.t_PrimeFieldElement 3329us & Hacspec_lib.Field.t_PrimeFieldElement 3329us
  ) =
    Hacspec_lib.Field.f_ZERO, Hacspec_lib.Field.f_ZERO
    <:
    (Hacspec_lib.Field.t_PrimeFieldElement 3329us & Hacspec_lib.Field.t_PrimeFieldElement 3329us)
  in
  let c:(Hacspec_lib.Field.t_PrimeFieldElement 3329us & Hacspec_lib.Field.t_PrimeFieldElement 3329us
  ) =
    {
      c with
      _1
      =
      (a._1 *! b._1 <: Hacspec_lib.Field.t_PrimeFieldElement 3329us) +!
      ((a._2 *! b._2 <: Hacspec_lib.Field.t_PrimeFieldElement 3329us) *! zeta
        <:
        Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    }
    <:
    (Hacspec_lib.Field.t_PrimeFieldElement 3329us & Hacspec_lib.Field.t_PrimeFieldElement 3329us)
  in
  let c:(Hacspec_lib.Field.t_PrimeFieldElement 3329us & Hacspec_lib.Field.t_PrimeFieldElement 3329us
  ) =
    {
      c with
      _2
      =
      (a._1 *! b._2 <: Hacspec_lib.Field.t_PrimeFieldElement 3329us) +!
      (a._2 *! b._1 <: Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    }
    <:
    (Hacspec_lib.Field.t_PrimeFieldElement 3329us & Hacspec_lib.Field.t_PrimeFieldElement 3329us)
  in
  c

let v_INVERSE_OF_128_: Hacspec_lib.Field.t_PrimeFieldElement 3329us =
  { Hacspec_lib.Field.f_value = 3303us } <: Hacspec_lib.Field.t_PrimeFieldElement 3329us

let v_ZETA: Hacspec_lib.Field.t_PrimeFieldElement 3329us =
  { Hacspec_lib.Field.f_value = 17us } <: Hacspec_lib.Field.t_PrimeFieldElement 3329us

let bit_rev_7_ (value: u8) : u8 =
  let (reversed: u8):u8 = 0uy in
  let reversed:u8 =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = 0ul;
              Core.Ops.Range.f_end = Core.Num.impl__u8__BITS -! 1ul <: u32
            }
            <:
            Core.Ops.Range.t_Range u32)
        <:
        Core.Ops.Range.t_Range u32)
      reversed
      (fun reversed bit ->
          let reversed:u8 = reversed in
          let bit:u32 = bit in
          let reversed:u8 = reversed <<! 1l in
          let reversed:u8 = reversed |. ((value &. (1uy <<! bit <: u8) <: u8) >>! bit <: u8) in
          reversed)
  in
  reversed

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
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 128
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      h_hat
      (fun h_hat i ->
          let h_hat:Hacspec_lib.Ring.t_PolynomialRingElement
            (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
            h_hat
          in
          let i:usize = i in
          let binomial_product:(Hacspec_lib.Field.t_PrimeFieldElement 3329us &
            Hacspec_lib.Field.t_PrimeFieldElement 3329us) =
            base_case_multiply ((ff_hat.[ sz 2 *! i <: usize ]
                  <:
                  Hacspec_lib.Field.t_PrimeFieldElement 3329us),
                (ff_hat.[ (sz 2 *! i <: usize) +! sz 1 <: usize ]
                  <:
                  Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                <:
                (Hacspec_lib.Field.t_PrimeFieldElement 3329us &
                  Hacspec_lib.Field.t_PrimeFieldElement 3329us))
              ((g_hat.[ sz 2 *! i <: usize ] <: Hacspec_lib.Field.t_PrimeFieldElement 3329us),
                (g_hat.[ (sz 2 *! i <: usize) +! sz 1 <: usize ]
                  <:
                  Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                <:
                (Hacspec_lib.Field.t_PrimeFieldElement 3329us &
                  Hacspec_lib.Field.t_PrimeFieldElement 3329us))
              (Hacspec_lib.Field.impl_1__pow 3329us
                  v_ZETA
                  ((2uy *! (bit_rev_7_ (Hacspec_lib.f_as_u8 i <: u8) <: u8) <: u8) +! 1uy <: u8)
                <:
                Hacspec_lib.Field.t_PrimeFieldElement 3329us)
          in
          let h_hat:Hacspec_lib.Ring.t_PolynomialRingElement
            (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize h_hat
              (sz 2 *! i <: usize)
              binomial_product._1
          in
          let h_hat:Hacspec_lib.Ring.t_PolynomialRingElement
            (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize h_hat
              ((sz 2 *! i <: usize) +! sz 1 <: usize)
              binomial_product._2
          in
          h_hat)
  in
  h_hat

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
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_rev
              (Core.Slice.impl__iter (Rust_primitives.unsize v_NTT_LAYERS <: t_Slice usize)
                <:
                Core.Slice.Iter.t_Iter usize)
            <:
            Core.Iter.Adapters.Rev.t_Rev (Core.Slice.Iter.t_Iter usize))
        <:
        Core.Iter.Adapters.Rev.t_Rev (Core.Slice.Iter.t_Iter usize))
      (ff_hat, k
        <:
        (Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            (sz 256) &
          u8))
      (fun temp_0_ len ->
          let ff_hat, k:(Hacspec_lib.Ring.t_PolynomialRingElement
              (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) &
            u8) =
            temp_0_
          in
          let len:usize = len in
          Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_step_by
                    ({
                        Core.Ops.Range.f_start = sz 0;
                        Core.Ops.Range.f_end
                        =
                        Hacspec_kyber.Parameters.v_COEFFICIENTS_IN_RING_ELEMENT -! len <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                    (sz 2 *! len <: usize)
                  <:
                  Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
              <:
              Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
            (ff_hat, k
              <:
              (Hacspec_lib.Ring.t_PolynomialRingElement
                  (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) &
                u8))
            (fun temp_0_ start ->
                let ff_hat, k:(Hacspec_lib.Ring.t_PolynomialRingElement
                    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) &
                  u8) =
                  temp_0_
                in
                let start:usize = start in
                let zeta:Hacspec_lib.Field.t_PrimeFieldElement 3329us =
                  Hacspec_lib.Field.impl_1__pow 3329us v_ZETA (bit_rev_7_ k <: u8)
                in
                let k:u8 = k +! 1uy in
                let ff_hat:Hacspec_lib.Ring.t_PolynomialRingElement
                  (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
                  Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                            Core.Ops.Range.f_start = start;
                            Core.Ops.Range.f_end = start +! len <: usize
                          }
                          <:
                          Core.Ops.Range.t_Range usize)
                      <:
                      Core.Ops.Range.t_Range usize)
                    ff_hat
                    (fun ff_hat j ->
                        let ff_hat:Hacspec_lib.Ring.t_PolynomialRingElement
                          (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
                          ff_hat
                        in
                        let j:usize = j in
                        let t:Hacspec_lib.Field.t_PrimeFieldElement 3329us =
                          zeta *!
                          (ff_hat.[ j +! len <: usize ]
                            <:
                            Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                        in
                        let ff_hat:Hacspec_lib.Ring.t_PolynomialRingElement
                          (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
                          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize ff_hat
                            (j +! len <: usize)
                            ((ff_hat.[ j ] <: Hacspec_lib.Field.t_PrimeFieldElement 3329us) -! t
                              <:
                              Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                        in
                        let ff_hat:Hacspec_lib.Ring.t_PolynomialRingElement
                          (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
                          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize ff_hat
                            j
                            ((ff_hat.[ j ] <: Hacspec_lib.Field.t_PrimeFieldElement 3329us) +! t
                              <:
                              Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                        in
                        ff_hat)
                in
                ff_hat, k
                <:
                (Hacspec_lib.Ring.t_PolynomialRingElement
                    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) &
                  u8))
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
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter v_NTT_LAYERS
        <:
        Core.Array.Iter.t_IntoIter usize (sz 7))
      (f, k
        <:
        (Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            (sz 256) &
          u8))
      (fun temp_0_ len ->
          let f, k:(Hacspec_lib.Ring.t_PolynomialRingElement
              (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) &
            u8) =
            temp_0_
          in
          let len:usize = len in
          Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_step_by
                    ({
                        Core.Ops.Range.f_start = sz 0;
                        Core.Ops.Range.f_end
                        =
                        Hacspec_kyber.Parameters.v_COEFFICIENTS_IN_RING_ELEMENT -! len <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                    (sz 2 *! len <: usize)
                  <:
                  Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
              <:
              Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
            (f, k
              <:
              (Hacspec_lib.Ring.t_PolynomialRingElement
                  (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) &
                u8))
            (fun temp_0_ start ->
                let f, k:(Hacspec_lib.Ring.t_PolynomialRingElement
                    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) &
                  u8) =
                  temp_0_
                in
                let start:usize = start in
                let zeta:Hacspec_lib.Field.t_PrimeFieldElement 3329us =
                  Hacspec_lib.Field.impl_1__pow 3329us v_ZETA (bit_rev_7_ k <: u8)
                in
                let k:u8 = k -! 1uy in
                let f:Hacspec_lib.Ring.t_PolynomialRingElement
                  (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
                  Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                            Core.Ops.Range.f_start = start;
                            Core.Ops.Range.f_end = start +! len <: usize
                          }
                          <:
                          Core.Ops.Range.t_Range usize)
                      <:
                      Core.Ops.Range.t_Range usize)
                    f
                    (fun f j ->
                        let f:Hacspec_lib.Ring.t_PolynomialRingElement
                          (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
                          f
                        in
                        let j:usize = j in
                        let t:Hacspec_lib.Field.t_PrimeFieldElement 3329us = f.[ j ] in
                        let f:Hacspec_lib.Ring.t_PolynomialRingElement
                          (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
                          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize f
                            j
                            (t +!
                              (f.[ j +! len <: usize ]
                                <:
                                Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                              <:
                              Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                        in
                        let f:Hacspec_lib.Ring.t_PolynomialRingElement
                          (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
                          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize f
                            (j +! len <: usize)
                            (zeta *!
                              ((f.[ j +! len <: usize ]
                                  <:
                                  Hacspec_lib.Field.t_PrimeFieldElement 3329us) -!
                                t
                                <:
                                Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                              <:
                              Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                        in
                        f)
                in
                f, k
                <:
                (Hacspec_lib.Ring.t_PolynomialRingElement
                    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) &
                  u8))
          <:
          (Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
              (sz 256) &
            u8))
  in
  let f:Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    (sz 256) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end
              =
              Core.Slice.impl__len (Rust_primitives.unsize (Hacspec_lib.Ring.impl_2__coefficients (sz
                          256)
                        f
                      <:
                      t_Array (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256))
                  <:
                  t_Slice (Hacspec_lib.Field.t_PrimeFieldElement 3329us))
              <:
              usize
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      f
      (fun f i ->
          let f:Hacspec_lib.Ring.t_PolynomialRingElement
            (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
            f
          in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize f
            i
            ((f.[ i ] <: Hacspec_lib.Field.t_PrimeFieldElement 3329us) *! v_INVERSE_OF_128_
              <:
              Hacspec_lib.Field.t_PrimeFieldElement 3329us)
          <:
          Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            (sz 256))
  in
  f

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
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Hacspec_lib.Vector.impl__into_iter (sz 3) (sz 256) vector_as_ntt
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
        Core.Iter.Adapters.Enumerate.t_Enumerate
        (Core.Array.Iter.t_IntoIter
            (Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                (sz 256)) (sz 3)))
      vector
      (fun vector temp_1_ ->
          let vector:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            (sz 256)
            (sz 3) =
            vector
          in
          let i, re_ntt:(usize &
            Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
              (sz 256)) =
            temp_1_
          in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize vector
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
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Hacspec_lib.Vector.impl__into_iter (sz 3) (sz 256) vector
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
        Core.Iter.Adapters.Enumerate.t_Enumerate
        (Core.Array.Iter.t_IntoIter
            (Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                (sz 256)) (sz 3)))
      vector_as_ntt
      (fun vector_as_ntt temp_1_ ->
          let vector_as_ntt:Hacspec_lib.Vector.t_Vector
            (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3) =
            vector_as_ntt
          in
          let i, re:(usize &
            Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
              (sz 256)) =
            temp_1_
          in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize vector_as_ntt
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
