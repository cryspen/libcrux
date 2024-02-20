module Libcrux.Kem.Kyber.Sampling
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let rejection_sampling_panic_with_diagnostic () : Prims.unit =
  admit(); // This should never be reachable
  Rust_primitives.Hax.never_to_any (Core.Panicking.panic "explicit panic"
      <:
      Rust_primitives.Hax.t_Never)

#push-options "--ifuel 0 --z3rlimit 100"
let sample_from_binomial_distribution_2_ (randomness: t_Slice u8) =
  let sampled: t_PolynomialRingElement_b 3 = 
    cast_poly_b Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in

  let acc_t = Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 3 in
  [@ inline_let]
  let inv = fun (acc:acc_t) (i:usize) -> True in
  let sl : t_Slice u8 = randomness in
  let chunk_len = sz 4 in
  assert (v (length sl) == 128);
  assert (Seq.length sl == 128);
  assert_norm (128 % 4 == 0);
  let sampled =
   Rust_primitives.Iterators.foldi_chunks_exact #u8 #acc_t #inv
      sl
      chunk_len
      sampled
      (fun sampled temp_1_ ->
          let chunk_number, byte_chunk:(usize & t_Array u8 chunk_len) = temp_1_ in
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
          logand_lemma random_bits_as_u32 1431655765ul;
          assert(even_bits <=. 1431655765ul);
          let odd_bits:u32 = (random_bits_as_u32 >>! 1l <: u32) &. 1431655765ul in
          logand_lemma (random_bits_as_u32 >>! 1l <: u32) 1431655765ul;
          assert(odd_bits <=. 1431655765ul);
          let coin_toss_outcomes:u32 = even_bits +! odd_bits in
          let acc_t = Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 3 in
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
                let outcome_set:u32 = outcome_set in
                assert (v outcome_set + 4 <= 32);
                let out_1 = ((coin_toss_outcomes >>! outcome_set <: u32) &. 3ul <: u32) in
                let outcome_1_:i32 =
                  cast out_1  <: i32
                in
                let out_2 = ((coin_toss_outcomes >>! (outcome_set +! 2ul <: u32) <: u32) &. 3ul <: u32) in
                let outcome_2_:i32 =
                  cast out_2  <: i32
                in
                logand_lemma (coin_toss_outcomes >>! outcome_set <: u32) 3ul;
                assert (v out_1 >= 0);
                assert (v out_1 <= 3);
                assert (v outcome_1_ == v out_1 @% pow2 32);
                Math.Lemmas.small_modulo_lemma_1 (v out_1) (pow2 32);
                assert (v outcome_1_ == v out_1);
                assert (v outcome_1_ >= 0 /\ v outcome_1_ <= 3);
                logand_lemma (coin_toss_outcomes >>! (outcome_set +! 2ul <: u32) <: u32) 3ul;
                assert (v out_2 >= 0);
                assert (v out_2 <= 3);
                assert (v outcome_2_ == v out_2 @% pow2 32);
                Math.Lemmas.small_modulo_lemma_1 (v out_2) (pow2 32);
                assert (v outcome_2_ == v out_2);
                assert (v outcome_2_ >= 0 /\ v outcome_2_ <= 3);
                let offset:usize = cast (outcome_set >>! 2l <: u32) <: usize in
                assert (outcome_set <. 32ul);
                assert (v (outcome_set >>! 2l <: u32) = v outcome_set / 4);
                assert (v (outcome_set >>! 2l <: u32) < 8);
                Math.Lemmas.small_modulo_lemma_1 (v (outcome_set >>! 2l <: u32)) (pow2 32);
                Math.Lemmas.small_modulo_lemma_1 (v (outcome_set >>! 2l <: u32)) (pow2 64);
                assert (v offset < 8);
                assert (8 * v chunk_number + 8 <= 256);
                assert (8 * v chunk_number + v offset < 256);
                let sampled:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 3 =
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
                  Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 3
                in
                sampled))
  in 
  let _:Prims.unit = () <: Prims.unit in 
  admit(); // P-F
  sampled 
#pop-options

#push-options "--ifuel 0 --z3rlimit 200"
let sample_from_binomial_distribution_3_ (randomness: t_Slice u8) =
  let sampled:t_PolynomialRingElement_b 7 =
    (Libcrux.Kem.Kyber.Arithmetic.cast_poly_b Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO)
  in
  let acc_t = Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 7 in
  [@ inline_let]
  let inv = fun (acc:acc_t) (i:usize) -> True in
  let sl : t_Slice u8 = randomness in
  let chunk_len = sz 3 in
  assert (v (length sl) == 192);
  assert (Seq.length sl == 192);
  assert_norm (192 % 3 == 0);
  let sampled:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 7 =
   Rust_primitives.Iterators.foldi_chunks_exact #u8 #acc_t #inv
      sl
      chunk_len
      sampled
      (fun sampled temp_1_ ->
          let sampled:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 7 = sampled in
          let chunk_number, byte_chunk:(usize & t_Array u8 chunk_len) = temp_1_ in
          let (random_bits_as_u24: u32):u32 =
            ((cast (byte_chunk.[ sz 0 ] <: u8) <: u32) |.
              ((cast (byte_chunk.[ sz 1 ] <: u8) <: u32) <<! 8l <: u32)
              <:
              u32) |.
            ((cast (byte_chunk.[ sz 2 ] <: u8) <: u32) <<! 16l <: u32)
          in
          let first_bits:u32 = random_bits_as_u24 &. 2396745ul in
          logand_lemma random_bits_as_u24 2396745ul;
          assert (first_bits <=. 2396745ul);
          let second_bits:u32 = (random_bits_as_u24 >>! 1l <: u32) &. 2396745ul in
          logand_lemma (random_bits_as_u24 >>! 1l <: u32) 2396745ul;
          assert (second_bits <=. 2396745ul);
          let third_bits:u32 = (random_bits_as_u24 >>! 2l <: u32) &. 2396745ul in
          logand_lemma (random_bits_as_u24 >>! 2l <: u32) 2396745ul;
          assert (third_bits <=. 2396745ul);
          let coin_toss_outcomes:u32 = (first_bits +! second_bits <: u32) +! third_bits in
          let acc_t = Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 7 in
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
                let sampled:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 7 = sampled in
                let outcome_set:i32 = outcome_set in
                let outcome_1_:i32 =
                  cast ((coin_toss_outcomes >>! outcome_set <: u32) &. 7ul <: u32) <: i32
                in
                let outcome_2_:i32 =
                  cast ((coin_toss_outcomes >>! (outcome_set +! 3l <: i32) <: u32) &. 7ul <: u32)
                  <:
                  i32
                in
                logand_lemma (coin_toss_outcomes >>! outcome_set <: u32) 7ul;
                Math.Lemmas.small_modulo_lemma_1 (v ((coin_toss_outcomes >>! outcome_set <: u32) &. 7ul <: u32)) (pow2 32);
                assert (v outcome_1_ >= 0 /\ v outcome_1_ <= 7);
                logand_lemma (coin_toss_outcomes >>! (outcome_set +! 3l <: i32) <: u32) 7ul;
                Math.Lemmas.small_modulo_lemma_1 (v ((coin_toss_outcomes >>! (outcome_set +! 3l <: i32) <: u32) &. 7ul <: u32)) (pow2 32);
                assert (v outcome_2_ >= 0 /\ v outcome_2_ <= 7);
                let offset:usize = cast (outcome_set /! 6l <: i32) <: usize in
                assert (outcome_set <. 24l);
                assert (v (outcome_set /! 6l <: i32) = v outcome_set / 6);
                assert (v (outcome_set /! 6l <: i32) < 4);
                Math.Lemmas.small_modulo_lemma_1 (v (outcome_set /! 6l <: i32)) (pow2 32);
                Math.Lemmas.small_modulo_lemma_1 (v (outcome_set /! 6l <: i32)) (pow2 64);
                assert (v offset < 4);
                assert (4 * v chunk_number + 4 <= 256);
                assert (4 * v chunk_number + v offset < 256);
                let sampled:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 7 =
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
                  Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 7
                in
                sampled))
  in
  let _:Prims.unit = () <: Prims.unit in
  admit();
  sampled
#pop-options

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

#push-options "--z3rlimit 50"
let sample_from_uniform_distribution (randomness: t_Array u8 (sz 840)) =
  let (sampled_coefficients: usize):usize = sz 0 in
  let (out: Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement):Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
  =
    Libcrux.Kem.Kyber.Arithmetic.cast_poly_b Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let done:bool = false in
  let acc_t = (bool & Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement & usize) in
  [@ inline_let]
  let inv = fun (acc:acc_t) -> True in
  let sl : t_Slice u8 = randomness in
  let chunk_len = sz 3 in
  let done, out, sampled_coefficients:(bool & Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement &
    usize) =
   Rust_primitives.Iterators.fold_chunks_exact #u8 #acc_t #inv
      sl
      chunk_len
      (done, out, sampled_coefficients
        <:
        (bool & Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement & usize))
      (fun temp_0_ bytes ->
          let done, out, sampled_coefficients:(bool &
            Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement &
            usize) =
            temp_0_
          in
          let bytes:t_Array u8 chunk_len = bytes in
          if ~.done <: bool
          then
            let b1:i32 = cast (bytes.[ sz 0 ] <: u8) <: i32 in
            let b2:i32 = cast (bytes.[ sz 1 ] <: u8) <: i32 in
            let b3:i32 = cast (bytes.[ sz 2 ] <: u8) <: i32 in
            assert(v b1 >= 0 /\ v b1 < pow2 8);
            assert(v b2 >= 0 /\ v b2 < pow2 8);
            assert(v b3 >= 0 /\ v b3 < pow2 8);
            let d1:i32 = ((b2 &. 15l <: i32) <<! 8l <: i32) |. b1 in
            assert (15 = pow2 4 - 1);
            mk_int_equiv_lemma #i32_inttype 15;
            assert (15l = mk_int (pow2 4) -! mk_int 1);
            logand_mask_lemma b2 4;
            assert (v ((b2 &. 15l <: i32) <<! 8l <: i32) == (v b2 % 16) * pow2 8);
            logor_lemma ((b2 &. 15l <: i32) <<! 8l <: i32) b1;
            assert (v d1 >= v b1);
            assert (v d1 >= 0);
            let d2:i32 = (b3 <<! 4l <: i32) |. (b2 >>! 4l <: i32) in
            logor_lemma (b3 <<! 4l <: i32) (b2 >>! 4l <: i32);
            assert (v d2 >= v b3 * pow2 4);
            assert (v d2 >= 0);
            let out, sampled_coefficients:(Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement &
              usize) =
              if
                d1 <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS &&
                sampled_coefficients <. Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
              then
                let out:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
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
                  Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
                in
                out, sampled_coefficients +! sz 1
                <:
                (Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement & usize)
              else
                out, sampled_coefficients
                <:
                (Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement & usize)
            in
            let out, sampled_coefficients:(Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement &
              usize) =
              if
                d2 <. Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS &&
                sampled_coefficients <. Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
              then
                let out:Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement =
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
                  Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
                in
                let sampled_coefficients:usize = sampled_coefficients +! sz 1 in
                out, sampled_coefficients
                <:
                (Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement & usize)
              else
                out, sampled_coefficients
                <:
                (Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement & usize)
            in
            if sampled_coefficients =. Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
            then
              let done:bool = true in
              done, out, sampled_coefficients
              <:
              (bool & Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement & usize)
            else
              done, out, sampled_coefficients
              <:
              (bool & Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement & usize)
          else
            done, out, sampled_coefficients
            <:
            (bool & Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement & usize))
  in
  let _:Prims.unit =
    if ~.done
    then
      let _:Prims.unit = rejection_sampling_panic_with_diagnostic () in
      ()
  in
  let _:Prims.unit = () <: Prims.unit in
  out 
#pop-options
