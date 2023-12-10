module Libcrux.Kem.Kyber.Sampling
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let rejection_sampling_panic_with_diagnostic () : Prims.unit =
  admit(); // This should never happen
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "explicit panic"
      <:
      Rust_primitives.Hax.t_Never)

val sample_from_binomial_distribution_2_ (randomness: t_Slice u8)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      (requires (Core.Slice.impl__len randomness <: usize) =. (sz 2 *! sz 64 <: usize))
      (ensures
        fun result ->
          let result:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = result in
          Libcrux.Kem.Kyber.Arithmetic.to_spec_poly result == 
          Spec.Kyber.sample_poly_binomial (sz 2) randomness /\
          (forall (i:usize). i <. length result.Libcrux.Kem.Kyber.Arithmetic.f_coefficients ==>
                  (Core.Num.impl__i32__abs (result.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ]
                          <:
                          i32) 
                      <:
                      i32) <=.
                    2l))

let sample_from_binomial_distribution_2_ (randomness: t_Slice u8) =
  let (sampled: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement):Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
  =
    Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in

  let acc_t = Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement in
  [@ inline_let]
  let inv = fun (acc:acc_t) (i:usize) -> True in
  let sl : t_Slice u8 = randomness in
  let chunk_len = sz 4 in
  assert (v (length sl) == 128);
  assert (Seq.length sl == 128);
  assert_norm (128 % 4 == 0);
  let sampled:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
   Rust_primitives.Iterators.foldi_chunks_exact #u8 #acc_t #inv
      sl
      chunk_len
      sampled
      (fun sampled temp_1_ ->
          let sampled:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = sampled in
          let chunk_number, byte_chunk:(usize & t_Slice u8) = temp_1_ in
          assert(chunk_number <. sz 32);
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
          assume(even_bits <=. 1431655765ul);
          let odd_bits:u32 = (random_bits_as_u32 >>! 1l <: u32) &. 1431655765ul in
          assume(odd_bits <=. 1431655765ul);
          let coin_toss_outcomes:u32 = even_bits +! odd_bits in
          let acc_t = Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement in
          [@ inline_let]
          let inv : acc_t -> u32 -> Type = fun acc i -> True in
            Rust_primitives.Iterators.foldi_range_step_by #u32_inttype #(acc_t) #inv ({
                        Core.Ops.Range.f_start = 0ul;
                        Core.Ops.Range.f_end = Core.Num.impl__u32__BITS
                        }
                        <:
                        Core.Ops.Range.t_Range u32)
            (sz 4)
            sampled
            (fun sampled outcome_set ->
                let sampled:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = sampled in
                let outcome_set:u32 = outcome_set in
                let outcome_1_:i32 =
                  cast ((coin_toss_outcomes >>! outcome_set <: u32) &. 3ul <: u32) <: i32
                in
                let outcome_2_:i32 =
                  cast ((coin_toss_outcomes >>! (outcome_set +! 2ul <: u32) <: u32) &. 3ul <: u32)
                  <:
                  i32
                in
                assume (outcome_1_ >=. 0l /\ outcome_1_ <. 3l);
                assume (outcome_2_ >=. 0l /\ outcome_2_ <. 3l);
                let offset:usize = cast (outcome_set >>! 2l <: u32) <: usize in
                assert (outcome_set <. 32ul);
                assume (offset <. sz 8);
                assert (8 * v chunk_number + v offset < 256);
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
  admit(); // P-F
  sampled 

val sample_from_binomial_distribution_3_ (randomness: t_Slice u8)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      (requires (Core.Slice.impl__len randomness <: usize) =. (sz 3 *! sz 64 <: usize))
      (ensures
        fun result ->
          let result:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = result in
          Libcrux.Kem.Kyber.Arithmetic.to_spec_poly result == 
          Spec.Kyber.sample_poly_binomial (sz 3) randomness /\
          (forall (i:usize). i <. length result.Libcrux.Kem.Kyber.Arithmetic.f_coefficients ==>
                  (Core.Num.impl__i32__abs (result.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ]
                          <:
                          i32) 
                      <:
                      i32) <=.
                    3l))

let sample_from_binomial_distribution_3_ (randomness: t_Slice u8) =
  let (sampled: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement):Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
  =
    Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let acc_t = Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement in
  [@ inline_let]
  let inv = fun (acc:acc_t) (i:usize) -> True in
  let sl : t_Slice u8 = randomness in
  let chunk_len = sz 3 in
  assert (v (length sl) == 192);
  assert (Seq.length sl == 192);
  assert_norm (192 % 3 == 0);
  let sampled:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
   Rust_primitives.Iterators.foldi_chunks_exact #u8 #acc_t #inv
      sl
      chunk_len
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
          assume (first_bits <=. 2396745ul);
          let second_bits:u32 = (random_bits_as_u24 >>! 1l <: u32) &. 2396745ul in
          assume (second_bits <=. 2396745ul);
          let third_bits:u32 = (random_bits_as_u24 >>! 2l <: u32) &. 2396745ul in
          assume (third_bits <=. 2396745ul);
          let coin_toss_outcomes:u32 = (first_bits +! second_bits <: u32) +! third_bits in
          let acc_t = Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement in
          [@ inline_let]
          let inv : acc_t -> i32 -> Type = fun acc i -> True in
            Rust_primitives.Iterators.foldi_range_step_by #i32_inttype #(acc_t) #inv ({
                        Core.Ops.Range.f_start = 0l;
                        Core.Ops.Range.f_end = 24l
                        }
                        <:
                        Core.Ops.Range.t_Range i32)
            (sz 6)
            sampled
            (fun sampled outcome_set ->
                let sampled:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = sampled in
                let outcome_set:i32 = outcome_set in
                let outcome_1_:i32 =
                  cast ((coin_toss_outcomes >>! outcome_set <: u32) &. 7ul <: u32) <: i32
                in
                let outcome_2_:i32 =
                  cast ((coin_toss_outcomes >>! (outcome_set +! 3l <: i32) <: u32) &. 7ul <: u32)
                  <:
                  i32
                in
                assume (outcome_1_ >=. 0l /\ outcome_1_ <. 7l);
                assume (outcome_2_ >=. 0l /\ outcome_2_ <. 7l);
                let offset:usize = cast (outcome_set /! 6l <: i32) <: usize in
                assume(offset <. sz 4);
                assert(4 * v chunk_number + v offset < 256);
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
  admit();
  sampled

let sample_from_binomial_distribution (v_ETA: usize) (randomness: t_Slice u8) =
  let _:Prims.unit = () <: Prims.unit in
  Rust_primitives.Integers.mk_int_equiv_lemma #u32_inttype (v v_ETA);
  match cast (v_ETA <: usize) <: u32 with
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
  let acc_t = (bool & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement & usize) in
  [@ inline_let]
  let inv = fun (acc:acc_t) -> True in
  let sl : t_Slice u8 = randomness in
  let chunk_len = sz 3 in
  let done, out, sampled_coefficients:(bool & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement &
    usize) =
   Rust_primitives.Iterators.fold_chunks_exact #u8 #acc_t #inv
      sl
      chunk_len
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
                d1 <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS &&
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
                d2 <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS &&
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
