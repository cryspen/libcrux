module Libcrux_ml_kem.Sampling
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Hash_functions in
  let open Libcrux_ml_kem.Vector.Traits in
  ()

let sample_from_uniform_distribution_next
      (#v_Vector: Type0)
      (v_K v_N: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (randomness: t_Array (t_Array u8 v_N) v_K)
      (sampled_coefficients: t_Array usize v_K)
      (out: t_Array (t_Array i16 (mk_usize 272)) v_K)
     =
  let out, sampled_coefficients:(t_Array (t_Array i16 (mk_usize 272)) v_K & t_Array usize v_K) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_K
      (fun temp_0_ temp_1_ ->
          let out, sampled_coefficients:(t_Array (t_Array i16 (mk_usize 272)) v_K &
            t_Array usize v_K) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (out, sampled_coefficients <: (t_Array (t_Array i16 (mk_usize 272)) v_K & t_Array usize v_K))
      (fun temp_0_ i ->
          let out, sampled_coefficients:(t_Array (t_Array i16 (mk_usize 272)) v_K &
            t_Array usize v_K) =
            temp_0_
          in
          let i:usize = i in
          Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
            (v_N /! mk_usize 24 <: usize)
            (fun temp_0_ temp_1_ ->
                let out, sampled_coefficients:(t_Array (t_Array i16 (mk_usize 272)) v_K &
                  t_Array usize v_K) =
                  temp_0_
                in
                let _:usize = temp_1_ in
                true)
            (out, sampled_coefficients
              <:
              (t_Array (t_Array i16 (mk_usize 272)) v_K & t_Array usize v_K))
            (fun temp_0_ r ->
                let out, sampled_coefficients:(t_Array (t_Array i16 (mk_usize 272)) v_K &
                  t_Array usize v_K) =
                  temp_0_
                in
                let r:usize = r in
                if
                  (sampled_coefficients.[ i ] <: usize) <.
                  Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
                  <:
                  bool
                then
                  let tmp0, out1:(t_Slice i16 & usize) =
                    Libcrux_ml_kem.Vector.Traits.f_rej_sample #v_Vector
                      #FStar.Tactics.Typeclasses.solve
                      ((randomness.[ i ] <: t_Array u8 v_N).[ {
                            Core.Ops.Range.f_start = r *! mk_usize 24 <: usize;
                            Core.Ops.Range.f_end
                            =
                            (r *! mk_usize 24 <: usize) +! mk_usize 24 <: usize
                          }
                          <:
                          Core.Ops.Range.t_Range usize ]
                        <:
                        t_Slice u8)
                      ((out.[ i ] <: t_Array i16 (mk_usize 272)).[ {
                            Core.Ops.Range.f_start = sampled_coefficients.[ i ] <: usize;
                            Core.Ops.Range.f_end
                            =
                            (sampled_coefficients.[ i ] <: usize) +! mk_usize 16 <: usize
                          }
                          <:
                          Core.Ops.Range.t_Range usize ]
                        <:
                        t_Slice i16)
                  in
                  let out:t_Array (t_Array i16 (mk_usize 272)) v_K =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                      i
                      (Rust_primitives.Hax.Monomorphized_update_at.update_at_range (out.[ i ]
                            <:
                            t_Array i16 (mk_usize 272))
                          ({
                              Core.Ops.Range.f_start = sampled_coefficients.[ i ] <: usize;
                              Core.Ops.Range.f_end
                              =
                              (sampled_coefficients.[ i ] <: usize) +! mk_usize 16 <: usize
                            }
                            <:
                            Core.Ops.Range.t_Range usize)
                          tmp0
                        <:
                        t_Array i16 (mk_usize 272))
                  in
                  let sampled:usize = out1 in
                  let sampled_coefficients:t_Array usize v_K =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize sampled_coefficients
                      i
                      ((sampled_coefficients.[ i ] <: usize) +! sampled <: usize)
                  in
                  out, sampled_coefficients
                  <:
                  (t_Array (t_Array i16 (mk_usize 272)) v_K & t_Array usize v_K)
                else
                  out, sampled_coefficients
                  <:
                  (t_Array (t_Array i16 (mk_usize 272)) v_K & t_Array usize v_K))
          <:
          (t_Array (t_Array i16 (mk_usize 272)) v_K & t_Array usize v_K))
  in
  let done:bool = true in
  let done, sampled_coefficients:(bool & t_Array usize v_K) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_K
      (fun temp_0_ temp_1_ ->
          let done, sampled_coefficients:(bool & t_Array usize v_K) = temp_0_ in
          let _:usize = temp_1_ in
          true)
      (done, sampled_coefficients <: (bool & t_Array usize v_K))
      (fun temp_0_ i ->
          let done, sampled_coefficients:(bool & t_Array usize v_K) = temp_0_ in
          let i:usize = i in
          if
            (sampled_coefficients.[ i ] <: usize) >=.
            Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
            <:
            bool
          then
            let sampled_coefficients:t_Array usize v_K =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize sampled_coefficients
                i
                Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
            in
            done, sampled_coefficients <: (bool & t_Array usize v_K)
          else false, sampled_coefficients <: (bool & t_Array usize v_K))
  in
  let hax_temp_output:bool = done in
  sampled_coefficients, out, hax_temp_output
  <:
  (t_Array usize v_K & t_Array (t_Array i16 (mk_usize 272)) v_K & bool)

#push-options "--admit_smt_queries true"

let sample_from_xof
      (v_K: usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (seeds: t_Array (t_Array u8 (mk_usize 34)) v_K)
     =
  let (sampled_coefficients: t_Array usize v_K):t_Array usize v_K =
    Rust_primitives.Hax.repeat (mk_usize 0) v_K
  in
  let (out: t_Array (t_Array i16 (mk_usize 272)) v_K):t_Array (t_Array i16 (mk_usize 272)) v_K =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat (mk_i16 0) (mk_usize 272)
        <:
        t_Array i16 (mk_usize 272))
      v_K
  in
  let xof_state:v_Hasher =
    Libcrux_ml_kem.Hash_functions.f_shake128_init_absorb_final #v_Hasher
      #v_K
      #FStar.Tactics.Typeclasses.solve
      seeds
  in
  let tmp0, out1:(v_Hasher & t_Array (t_Array u8 (mk_usize 504)) v_K) =
    Libcrux_ml_kem.Hash_functions.f_shake128_squeeze_first_three_blocks #v_Hasher
      #v_K
      #FStar.Tactics.Typeclasses.solve
      xof_state
  in
  let xof_state:v_Hasher = tmp0 in
  let randomness:t_Array (t_Array u8 (mk_usize 504)) v_K = out1 in
  let tmp0, tmp1, out1:(t_Array usize v_K & t_Array (t_Array i16 (mk_usize 272)) v_K & bool) =
    sample_from_uniform_distribution_next #v_Vector
      v_K
      (mk_usize 504)
      randomness
      sampled_coefficients
      out
  in
  let sampled_coefficients:t_Array usize v_K = tmp0 in
  let out:t_Array (t_Array i16 (mk_usize 272)) v_K = tmp1 in
  let done:bool = out1 in
  let done, out, sampled_coefficients, xof_state:(bool & t_Array (t_Array i16 (mk_usize 272)) v_K &
    t_Array usize v_K &
    v_Hasher) =
    Rust_primitives.Hax.while_loop (fun temp_0_ ->
          let done, out, sampled_coefficients, xof_state:(bool &
            t_Array (t_Array i16 (mk_usize 272)) v_K &
            t_Array usize v_K &
            v_Hasher) =
            temp_0_
          in
          ~.done <: bool)
      (done, out, sampled_coefficients, xof_state
        <:
        (bool & t_Array (t_Array i16 (mk_usize 272)) v_K & t_Array usize v_K & v_Hasher))
      (fun temp_0_ ->
          let done, out, sampled_coefficients, xof_state:(bool &
            t_Array (t_Array i16 (mk_usize 272)) v_K &
            t_Array usize v_K &
            v_Hasher) =
            temp_0_
          in
          let tmp0, out1:(v_Hasher & t_Array (t_Array u8 (mk_usize 168)) v_K) =
            Libcrux_ml_kem.Hash_functions.f_shake128_squeeze_next_block #v_Hasher
              #v_K
              #FStar.Tactics.Typeclasses.solve
              xof_state
          in
          let xof_state:v_Hasher = tmp0 in
          let randomness:t_Array (t_Array u8 (mk_usize 168)) v_K = out1 in
          let tmp0, tmp1, out1:(t_Array usize v_K & t_Array (t_Array i16 (mk_usize 272)) v_K & bool)
          =
            sample_from_uniform_distribution_next #v_Vector
              v_K
              (mk_usize 168)
              randomness
              sampled_coefficients
              out
          in
          let sampled_coefficients:t_Array usize v_K = tmp0 in
          let out:t_Array (t_Array i16 (mk_usize 272)) v_K = tmp1 in
          let done:bool = out1 in
          done, out, sampled_coefficients, xof_state
          <:
          (bool & t_Array (t_Array i16 (mk_usize 272)) v_K & t_Array usize v_K & v_Hasher))
  in
  Core.Array.impl_23__map #(t_Array i16 (mk_usize 272))
    v_K
    #(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
    out
    (fun s ->
        let s:t_Array i16 (mk_usize 272) = s in
        Libcrux_ml_kem.Polynomial.impl_2__from_i16_array #v_Vector
          (s.[ { Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 256 }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice i16)
        <:
        Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)

#pop-options

#push-options "--z3rlimit 800"

let sample_from_binomial_distribution_2_
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (randomness: t_Slice u8)
     =
  let _:Prims.unit =
    assert (v (sz 2 *! sz 64) == 128);
    assert (Seq.length randomness == 128)
  in
  let sampled_i16s:t_Array i16 (mk_usize 256) =
    Rust_primitives.Hax.repeat (mk_i16 0) (mk_usize 256)
  in
  let sampled_i16s:t_Array i16 (mk_usize 256) =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (mk_usize 4)
      randomness
      (fun sampled_i16s temp_1_ ->
          let sampled_i16s:t_Array i16 (mk_usize 256) = sampled_i16s in
          let _:usize = temp_1_ in
          true)
      sampled_i16s
      (fun sampled_i16s temp_1_ ->
          let sampled_i16s:t_Array i16 (mk_usize 256) = sampled_i16s in
          let chunk_number, byte_chunk:(usize & t_Slice u8) = temp_1_ in
          let (random_bits_as_u32: u32):u32 =
            (((cast (byte_chunk.[ mk_usize 0 ] <: u8) <: u32) |.
                ((cast (byte_chunk.[ mk_usize 1 ] <: u8) <: u32) <<! mk_i32 8 <: u32)
                <:
                u32) |.
              ((cast (byte_chunk.[ mk_usize 2 ] <: u8) <: u32) <<! mk_i32 16 <: u32)
              <:
              u32) |.
            ((cast (byte_chunk.[ mk_usize 3 ] <: u8) <: u32) <<! mk_i32 24 <: u32)
          in
          let even_bits:u32 = random_bits_as_u32 &. mk_u32 1431655765 in
          let odd_bits:u32 = (random_bits_as_u32 >>! mk_i32 1 <: u32) &. mk_u32 1431655765 in
          let _:Prims.unit =
            logand_lemma random_bits_as_u32 (mk_u32 1431655765);
            logand_lemma (random_bits_as_u32 >>! (mk_i32 1)) (mk_u32 1431655765)
          in
          let coin_toss_outcomes:u32 = even_bits +! odd_bits in
          Rust_primitives.Hax.Folds.fold_range_step_by (mk_u32 0)
            Core.Num.impl_u32__BITS
            (mk_usize 4)
            (fun sampled_i16s temp_1_ ->
                let sampled_i16s:t_Array i16 (mk_usize 256) = sampled_i16s in
                let _:u32 = temp_1_ in
                true)
            sampled_i16s
            (fun sampled_i16s outcome_set ->
                let sampled_i16s:t_Array i16 (mk_usize 256) = sampled_i16s in
                let outcome_set:u32 = outcome_set in
                let outcome_1_:i16 =
                  cast ((coin_toss_outcomes >>! outcome_set <: u32) &. mk_u32 3 <: u32) <: i16
                in
                let outcome_2_:i16 =
                  cast ((coin_toss_outcomes >>! (outcome_set +! mk_u32 2 <: u32) <: u32) &. mk_u32 3
                      <:
                      u32)
                  <:
                  i16
                in
                let _:Prims.unit =
                  logand_lemma (coin_toss_outcomes >>! outcome_set <: u32) (mk_u32 3);
                  logand_lemma (coin_toss_outcomes >>! (outcome_set +! (mk_u32 2) <: u32) <: u32)
                    (mk_u32 3);
                  assert (v outcome_1_ >= 0 /\ v outcome_1_ <= 3);
                  assert (v outcome_2_ >= 0 /\ v outcome_2_ <= 3);
                  assert (v chunk_number <= 31);
                  assert (v (sz 8 *! chunk_number <: usize) <= 248);
                  assert (v (cast (outcome_set >>! (mk_i32 2) <: u32) <: usize) <= 7)
                in
                let offset:usize = cast (outcome_set >>! mk_i32 2 <: u32) <: usize in
                let sampled_i16s:t_Array i16 (mk_usize 256) =
                  Rust_primitives.Hax.Monomorphized_update_at.update_at_usize sampled_i16s
                    ((mk_usize 8 *! chunk_number <: usize) +! offset <: usize)
                    (outcome_1_ -! outcome_2_ <: i16)
                in
                sampled_i16s))
  in
  Libcrux_ml_kem.Polynomial.impl_2__from_i16_array #v_Vector (sampled_i16s <: t_Slice i16)

#pop-options

#push-options "--z3rlimit 800"

let sample_from_binomial_distribution_3_
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (randomness: t_Slice u8)
     =
  let _:Prims.unit =
    assert (v (sz 3 *! sz 64) == 192);
    assert (Seq.length randomness == 192)
  in
  let sampled_i16s:t_Array i16 (mk_usize 256) =
    Rust_primitives.Hax.repeat (mk_i16 0) (mk_usize 256)
  in
  let sampled_i16s:t_Array i16 (mk_usize 256) =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice (mk_usize 3)
      randomness
      (fun sampled_i16s temp_1_ ->
          let sampled_i16s:t_Array i16 (mk_usize 256) = sampled_i16s in
          let _:usize = temp_1_ in
          true)
      sampled_i16s
      (fun sampled_i16s temp_1_ ->
          let sampled_i16s:t_Array i16 (mk_usize 256) = sampled_i16s in
          let chunk_number, byte_chunk:(usize & t_Slice u8) = temp_1_ in
          let (random_bits_as_u24: u32):u32 =
            ((cast (byte_chunk.[ mk_usize 0 ] <: u8) <: u32) |.
              ((cast (byte_chunk.[ mk_usize 1 ] <: u8) <: u32) <<! mk_i32 8 <: u32)
              <:
              u32) |.
            ((cast (byte_chunk.[ mk_usize 2 ] <: u8) <: u32) <<! mk_i32 16 <: u32)
          in
          let first_bits:u32 = random_bits_as_u24 &. mk_u32 2396745 in
          let second_bits:u32 = (random_bits_as_u24 >>! mk_i32 1 <: u32) &. mk_u32 2396745 in
          let third_bits:u32 = (random_bits_as_u24 >>! mk_i32 2 <: u32) &. mk_u32 2396745 in
          let _:Prims.unit =
            logand_lemma random_bits_as_u24 (mk_u32 2396745);
            logand_lemma (random_bits_as_u24 >>! (mk_i32 1) <: u32) (mk_u32 2396745);
            logand_lemma (random_bits_as_u24 >>! (mk_i32 2) <: u32) (mk_u32 2396745)
          in
          let coin_toss_outcomes:u32 = (first_bits +! second_bits <: u32) +! third_bits in
          Rust_primitives.Hax.Folds.fold_range_step_by (mk_i32 0)
            (mk_i32 24)
            (mk_usize 6)
            (fun sampled_i16s temp_1_ ->
                let sampled_i16s:t_Array i16 (mk_usize 256) = sampled_i16s in
                let _:i32 = temp_1_ in
                true)
            sampled_i16s
            (fun sampled_i16s outcome_set ->
                let sampled_i16s:t_Array i16 (mk_usize 256) = sampled_i16s in
                let outcome_set:i32 = outcome_set in
                let outcome_1_:i16 =
                  cast ((coin_toss_outcomes >>! outcome_set <: u32) &. mk_u32 7 <: u32) <: i16
                in
                let outcome_2_:i16 =
                  cast ((coin_toss_outcomes >>! (outcome_set +! mk_i32 3 <: i32) <: u32) &. mk_u32 7
                      <:
                      u32)
                  <:
                  i16
                in
                let _:Prims.unit =
                  logand_lemma (coin_toss_outcomes >>! outcome_set <: u32) (mk_u32 7);
                  logand_lemma (coin_toss_outcomes >>! (outcome_set +! (mk_i32 3) <: i32) <: u32)
                    (mk_u32 7);
                  assert (v outcome_1_ >= 0 /\ v outcome_1_ <= 7);
                  assert (v outcome_2_ >= 0 /\ v outcome_2_ <= 7);
                  assert (v chunk_number <= 63);
                  assert (v (sz 4 *! chunk_number <: usize) <= 252);
                  assert (v (cast (outcome_set /! (mk_i32 6) <: i32) <: usize) <= 3)
                in
                let offset:usize = cast (outcome_set /! mk_i32 6 <: i32) <: usize in
                let sampled_i16s:t_Array i16 (mk_usize 256) =
                  Rust_primitives.Hax.Monomorphized_update_at.update_at_usize sampled_i16s
                    ((mk_usize 4 *! chunk_number <: usize) +! offset <: usize)
                    (outcome_1_ -! outcome_2_ <: i16)
                in
                sampled_i16s))
  in
  Libcrux_ml_kem.Polynomial.impl_2__from_i16_array #v_Vector (sampled_i16s <: t_Slice i16)

#pop-options

let sample_from_binomial_distribution
      (v_ETA: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (randomness: t_Slice u8)
     =
  let _:Prims.unit = assert ((v (cast v_ETA <: u32) == 2) \/ (v (cast v_ETA <: u32) == 3)) in
  let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    match cast (v_ETA <: usize) <: u32 with
    | Rust_primitives.Integers.MkInt 2 -> sample_from_binomial_distribution_2_ #v_Vector randomness
    | Rust_primitives.Integers.MkInt 3 -> sample_from_binomial_distribution_3_ #v_Vector randomness
    | _ ->
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "internal error: entered unreachable code"

          <:
          Rust_primitives.Hax.t_Never)
  in
  let _:Prims.unit = admit () (* Panic freedom *) in
  result
