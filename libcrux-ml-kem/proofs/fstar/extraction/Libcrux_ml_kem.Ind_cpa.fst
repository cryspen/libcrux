module Libcrux_ml_kem.Ind_cpa
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Hash_functions in
  let open Libcrux_ml_kem.Ind_cpa.Unpacked in
  let open Libcrux_ml_kem.Variant in
  let open Libcrux_ml_kem.Vector.Traits in
  ()

#push-options "--z3rlimit 1000 --ext context_pruning --z3refresh"

let serialize_secret_key
      (v_K v_OUT_LEN: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (key: t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
     =
  let _:Prims.unit = assert_norm (Spec.MLKEM.polynomial_d 12 == Spec.MLKEM.polynomial) in
  let out:t_Array u8 v_OUT_LEN = Rust_primitives.Hax.repeat (mk_u8 0) v_OUT_LEN in
  let out:t_Array u8 v_OUT_LEN =
    Rust_primitives.Hax.Folds.fold_enumerated_slice key
      (fun out i ->
          let out:t_Array u8 v_OUT_LEN = out in
          let i:usize = i in
          (v i < v v_K ==>
            Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index key (v i))) /\
          (forall (j: nat).
              j < v i ==>
              (j + 1) * v Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT <= Seq.length out /\
              (Seq.slice out
                  (j * v Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT)
                  ((j + 1) * v Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT) ==
                Spec.MLKEM.byte_encode 12
                  (Libcrux_ml_kem.Polynomial.to_spec_poly_t #v_Vector (Seq.index key j)))))
      out
      (fun out temp_1_ ->
          let out:t_Array u8 v_OUT_LEN = out in
          let i, re:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            temp_1_
          in
          let out:t_Array u8 v_OUT_LEN =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
              ({
                  Core.Ops.Range.f_start
                  =
                  i *! Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT <: usize;
                  Core.Ops.Range.f_end
                  =
                  (i +! mk_usize 1 <: usize) *! Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT
                  <:
                  usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice #u8
                  (out.[ {
                        Core.Ops.Range.f_start
                        =
                        i *! Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT <: usize;
                        Core.Ops.Range.f_end
                        =
                        (i +! mk_usize 1 <: usize) *!
                        Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT
                        <:
                        usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (Libcrux_ml_kem.Serialize.serialize_uncompressed_ring_element #v_Vector re
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
          in
          let _:Prims.unit =
            let lemma_aux (j: nat{j < v i})
                : Lemma
                (Seq.slice out
                    (j * v Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT)
                    ((j + 1) * v Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT) ==
                  Spec.MLKEM.byte_encode 12
                    (Libcrux_ml_kem.Polynomial.to_spec_poly_t #v_Vector (Seq.index key j))) =
              Lib.Sequence.eq_intro #u8
                #(v Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT)
                (Seq.slice out
                    (j * v Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT)
                    ((j + 1) * v Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT))
                (Spec.MLKEM.byte_encode 12
                    (Libcrux_ml_kem.Polynomial.to_spec_poly_t #v_Vector (Seq.index key j)))
            in
            Classical.forall_intro lemma_aux
          in
          out)
  in
  let _:Prims.unit =
    assert (Spec.MLKEM.coerce_vector_12 (Libcrux_ml_kem.Polynomial.to_spec_vector_t #v_K
              #v_Vector
              key) ==
        Libcrux_ml_kem.Polynomial.to_spec_vector_t #v_K #v_Vector key);
    reveal_opaque (`%Spec.MLKEM.vector_encode_12) (Spec.MLKEM.vector_encode_12 #v_K);
    Lib.Sequence.eq_intro #u8
      #(v v_OUT_LEN)
      out
      (Spec.MLKEM.vector_encode_12 #v_K
          (Libcrux_ml_kem.Polynomial.to_spec_vector_t #v_K #v_Vector key))
  in
  out

#pop-options

let serialize_public_key_mut
      (v_K v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (tt_as_ntt: t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (seed_for_a: t_Slice u8)
      (serialized: t_Array u8 v_PUBLIC_KEY_SIZE)
     =
  let serialized:t_Array u8 v_PUBLIC_KEY_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range serialized
      ({
          Core.Ops.Range.f_start = mk_usize 0;
          Core.Ops.Range.f_end = v_RANKED_BYTES_PER_RING_ELEMENT
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (serialized.[ {
                Core.Ops.Range.f_start = mk_usize 0;
                Core.Ops.Range.f_end = v_RANKED_BYTES_PER_RING_ELEMENT
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (serialize_secret_key v_K v_RANKED_BYTES_PER_RING_ELEMENT #v_Vector tt_as_ntt
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let serialized:t_Array u8 v_PUBLIC_KEY_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from serialized
      ({ Core.Ops.Range.f_start = v_RANKED_BYTES_PER_RING_ELEMENT }
        <:
        Core.Ops.Range.t_RangeFrom usize)
      (Core.Slice.impl__copy_from_slice #u8
          (serialized.[ { Core.Ops.Range.f_start = v_RANKED_BYTES_PER_RING_ELEMENT }
              <:
              Core.Ops.Range.t_RangeFrom usize ]
            <:
            t_Slice u8)
          seed_for_a
        <:
        t_Slice u8)
  in
  let _:Prims.unit =
    Lib.Sequence.eq_intro #u8
      #(v v_PUBLIC_KEY_SIZE)
      serialized
      (Seq.append (Spec.MLKEM.vector_encode_12 #v_K
              (Libcrux_ml_kem.Polynomial.to_spec_vector_t #v_K #v_Vector tt_as_ntt))
          seed_for_a)
  in
  serialized

let serialize_public_key
      (v_K v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (tt_as_ntt: t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (seed_for_a: t_Slice u8)
     =
  let public_key_serialized:t_Array u8 v_PUBLIC_KEY_SIZE =
    Rust_primitives.Hax.repeat (mk_u8 0) v_PUBLIC_KEY_SIZE
  in
  let public_key_serialized:t_Array u8 v_PUBLIC_KEY_SIZE =
    serialize_public_key_mut v_K
      v_RANKED_BYTES_PER_RING_ELEMENT
      v_PUBLIC_KEY_SIZE
      #v_Vector
      tt_as_ntt
      seed_for_a
      public_key_serialized
  in
  public_key_serialized

#push-options "--max_fuel 15 --z3rlimit 1500 --ext context_pruning --z3refresh --split_queries always"

let sample_ring_element_cbd_helper_2
      (v_K v_ETA2 v_ETA2_RANDOMNESS_SIZE: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (error_1: t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (prf_input: t_Array u8 (sz 33))
      (domain_separator: u8) : Lemma
        (requires Spec.MLKEM.is_rank v_K /\ v_ETA2 == Spec.MLKEM.v_ETA2 v_K /\
          v_ETA2_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA2_RANDOMNESS_SIZE v_K /\
          v domain_separator < 2 * v v_K /\ 
          (let prf_outputs = Spec.MLKEM.v_PRFxN v_K v_ETA2_RANDOMNESS_SIZE
            (createi v_K (Spec.MLKEM.sample_vector_cbd2_prf_input #v_K
              (Seq.slice prf_input 0 32) (sz (v domain_separator)))) in 
          forall (i: nat). i < v v_K ==>
            Libcrux_ml_kem.Polynomial.to_spec_poly_t #v_Vector error_1.[ sz i ] ==
            Spec.MLKEM.sample_poly_cbd v_ETA2 prf_outputs.[ sz i ]))
        (ensures Libcrux_ml_kem.Polynomial.to_spec_vector_t #v_K #v_Vector error_1 ==
          (Spec.MLKEM.sample_vector_cbd2 #v_K
            (Seq.slice prf_input 0 32) (sz (v domain_separator))))
    =
    Lib.Sequence.eq_intro #(Spec.MLKEM.polynomial) #(v v_K)
    (Libcrux_ml_kem.Polynomial.to_spec_vector_t #v_K #v_Vector error_1) 
    (Spec.MLKEM.sample_vector_cbd2 #v_K (Seq.slice prf_input 0 32) (sz (v domain_separator)))

let sample_ring_element_cbd_helper_1
      (v_K: usize)
      (prf_inputs: t_Array (t_Array u8 (sz 33)) v_K)
      (prf_input: t_Array u8 (sz 33))
      (domain_separator: u8) : Lemma 
        (requires Spec.MLKEM.is_rank v_K /\ v domain_separator < 2 * v v_K /\
          (forall (i: nat). i < v v_K ==>
            v (Seq.index (Seq.index prf_inputs i) 32) == v domain_separator + i /\
            Seq.slice (Seq.index prf_inputs i) 0 32 == Seq.slice prf_input 0 32))
        (ensures prf_inputs == createi v_K
          (Spec.MLKEM.sample_vector_cbd2_prf_input #v_K
            (Seq.slice prf_input 0 32) (sz (v domain_separator))))
    =
    let lemma_aux (i: nat{i < v v_K}) : Lemma
        (prf_inputs.[ sz i ] == (Seq.append (Seq.slice prf_input 0 32) (Seq.create 1
          (mk_int #u8_inttype (v (domain_separator +! (mk_int #u8_inttype i))))))) =
      Lib.Sequence.eq_intro #u8 #33 prf_inputs.[ sz i ]
        (Seq.append (Seq.slice prf_input 0 32)
          (Seq.create 1 (mk_int #u8_inttype (v domain_separator + i))))
    in
    Classical.forall_intro lemma_aux;
    Lib.Sequence.eq_intro #(t_Array u8 (sz 33)) #(v v_K) prf_inputs
      (createi v_K (Spec.MLKEM.sample_vector_cbd2_prf_input #v_K
        (Seq.slice prf_input 0 32) (sz (v domain_separator))))

let sample_ring_element_cbd
      (v_K v_ETA2_RANDOMNESS_SIZE v_ETA2: usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (prf_input: t_Array u8 (mk_usize 33))
      (domain_separator: u8)
     =
  let error_1_:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Core.Array.from_fn #(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      v_K
      (fun v__i ->
          let v__i:usize = v__i in
          Libcrux_ml_kem.Polynomial.impl_2__ZERO #v_Vector ()
          <:
          Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
  in
  let prf_inputs:t_Array (t_Array u8 (mk_usize 33)) v_K =
    Rust_primitives.Hax.repeat prf_input v_K
  in
  let v__domain_separator_init:u8 = domain_separator in
  let tmp0, out:(t_Array (t_Array u8 (mk_usize 33)) v_K & u8) =
    Libcrux_ml_kem.Utils.prf_input_inc v_K prf_inputs domain_separator
  in
  let prf_inputs:t_Array (t_Array u8 (mk_usize 33)) v_K = tmp0 in
  let domain_separator:u8 = out in
  let _:Prims.unit =
    sample_ring_element_cbd_helper_1 v_K prf_inputs prf_input v__domain_separator_init
  in
  let (prf_outputs: t_Array (t_Array u8 v_ETA2_RANDOMNESS_SIZE) v_K):t_Array
    (t_Array u8 v_ETA2_RANDOMNESS_SIZE) v_K =
    Libcrux_ml_kem.Hash_functions.f_PRFxN #v_Hasher
      #v_K
      #FStar.Tactics.Typeclasses.solve
      v_ETA2_RANDOMNESS_SIZE
      prf_inputs
  in
  let error_1_:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_K
      (fun error_1_ i ->
          let error_1_:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            error_1_
          in
          let i:usize = i in
          forall (j: nat).
            j < v i ==>
            Libcrux_ml_kem.Polynomial.to_spec_poly_t #v_Vector error_1_.[ sz j ] ==
            Spec.MLKEM.sample_poly_cbd v_ETA2 prf_outputs.[ sz j ])
      error_1_
      (fun error_1_ i ->
          let error_1_:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            error_1_
          in
          let i:usize = i in
          let error_1_:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize error_1_
              i
              (Libcrux_ml_kem.Sampling.sample_from_binomial_distribution v_ETA2
                  #v_Vector
                  (prf_outputs.[ i ] <: t_Slice u8)
                <:
                Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          error_1_)
  in
  let _:Prims.unit =
    sample_ring_element_cbd_helper_2 v_K
      v_ETA2
      v_ETA2_RANDOMNESS_SIZE
      #v_Vector
      error_1_
      prf_input
      v__domain_separator_init
  in
  error_1_, domain_separator
  <:
  (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K & u8)

#pop-options

#push-options "--max_fuel 25 --z3rlimit 2500 --ext context_pruning --z3refresh --split_queries always"

let sample_vector_cbd_then_ntt_helper_2
      (v_K v_ETA v_ETA_RANDOMNESS_SIZE: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (re_as_ntt: t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (prf_input: t_Array u8 (sz 33))
      (domain_separator: u8) : Lemma
        (requires Spec.MLKEM.is_rank v_K /\ v_ETA == Spec.MLKEM.v_ETA1 v_K /\
          v_ETA_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE v_K /\
          v domain_separator < 2 * v v_K /\ 
          (let prf_outputs = Spec.MLKEM.v_PRFxN v_K v_ETA_RANDOMNESS_SIZE
            (createi v_K (Spec.MLKEM.sample_vector_cbd1_prf_input #v_K
              (Seq.slice prf_input 0 32) (sz (v domain_separator)))) in 
          forall (i: nat). i < v v_K ==>
            Libcrux_ml_kem.Polynomial.to_spec_poly_t #v_Vector re_as_ntt.[ sz i ] ==
            Spec.MLKEM.poly_ntt (Spec.MLKEM.sample_poly_cbd v_ETA prf_outputs.[ sz i ])))
        (ensures Libcrux_ml_kem.Polynomial.to_spec_vector_t #v_K #v_Vector re_as_ntt ==
          (Spec.MLKEM.sample_vector_cbd_then_ntt #v_K
            (Seq.slice prf_input 0 32) (sz (v domain_separator))))
    =
    reveal_opaque (`%Spec.MLKEM.sample_vector_cbd_then_ntt) (Spec.MLKEM.sample_vector_cbd_then_ntt #v_K);
    Lib.Sequence.eq_intro #(Spec.MLKEM.polynomial) #(v v_K)
      (Libcrux_ml_kem.Polynomial.to_spec_vector_t #v_K #v_Vector re_as_ntt)
      (Spec.MLKEM.sample_vector_cbd_then_ntt #v_K
        (Seq.slice prf_input 0 32) (sz (v domain_separator)))

let sample_vector_cbd_then_ntt_helper_1
      (v_K: usize)
      (prf_inputs: t_Array (t_Array u8 (sz 33)) v_K)
      (prf_input: t_Array u8 (sz 33))
      (domain_separator: u8) : Lemma 
        (requires Spec.MLKEM.is_rank v_K /\ v domain_separator < 2 * v v_K /\
          (forall (i: nat). i < v v_K ==>
            v (Seq.index (Seq.index prf_inputs i) 32) == v domain_separator + i /\
            Seq.slice (Seq.index prf_inputs i) 0 32 == Seq.slice prf_input 0 32))
        (ensures prf_inputs == createi v_K
          (Spec.MLKEM.sample_vector_cbd1_prf_input #v_K
            (Seq.slice prf_input 0 32) (sz (v domain_separator))))
    =
    let lemma_aux (i: nat{i < v v_K}) : Lemma
        (prf_inputs.[ sz i ] == (Seq.append (Seq.slice prf_input 0 32) (Seq.create 1
          (mk_int #u8_inttype (v (domain_separator +! (mk_int #u8_inttype i))))))) =
      Lib.Sequence.eq_intro #u8 #33 prf_inputs.[ sz i ]
        (Seq.append (Seq.slice prf_input 0 32)
          (Seq.create 1 (mk_int #u8_inttype (v domain_separator + i))))
    in
    Classical.forall_intro lemma_aux;
    Lib.Sequence.eq_intro #(t_Array u8 (sz 33)) #(v v_K) prf_inputs
      (createi v_K (Spec.MLKEM.sample_vector_cbd1_prf_input #v_K
        (Seq.slice prf_input 0 32) (sz (v domain_separator))))

let sample_vector_cbd_then_ntt
      (v_K v_ETA v_ETA_RANDOMNESS_SIZE: usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (re_as_ntt: t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (prf_input: t_Array u8 (mk_usize 33))
      (domain_separator: u8)
     =
  let prf_inputs:t_Array (t_Array u8 (mk_usize 33)) v_K =
    Rust_primitives.Hax.repeat prf_input v_K
  in
  let v__domain_separator_init:u8 = domain_separator in
  let tmp0, out:(t_Array (t_Array u8 (mk_usize 33)) v_K & u8) =
    Libcrux_ml_kem.Utils.prf_input_inc v_K prf_inputs domain_separator
  in
  let prf_inputs:t_Array (t_Array u8 (mk_usize 33)) v_K = tmp0 in
  let domain_separator:u8 = out in
  let _:Prims.unit =
    sample_vector_cbd_then_ntt_helper_1 v_K prf_inputs prf_input v__domain_separator_init
  in
  let (prf_outputs: t_Array (t_Array u8 v_ETA_RANDOMNESS_SIZE) v_K):t_Array
    (t_Array u8 v_ETA_RANDOMNESS_SIZE) v_K =
    Libcrux_ml_kem.Hash_functions.f_PRFxN #v_Hasher
      #v_K
      #FStar.Tactics.Typeclasses.solve
      v_ETA_RANDOMNESS_SIZE
      prf_inputs
  in
  let re_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_K
      (fun re_as_ntt i ->
          let re_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            re_as_ntt
          in
          let i:usize = i in
          forall (j: nat).
            j < v i ==>
            Libcrux_ml_kem.Polynomial.to_spec_poly_t #v_Vector re_as_ntt.[ sz j ] ==
            Spec.MLKEM.poly_ntt (Spec.MLKEM.sample_poly_cbd v_ETA prf_outputs.[ sz j ]) /\
            Libcrux_ml_kem.Serialize.coefficients_field_modulus_range #v_Vector re_as_ntt.[ sz j ])
      re_as_ntt
      (fun re_as_ntt i ->
          let re_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            re_as_ntt
          in
          let i:usize = i in
          let re_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re_as_ntt
              i
              (Libcrux_ml_kem.Sampling.sample_from_binomial_distribution v_ETA
                  #v_Vector
                  (prf_outputs.[ i ] <: t_Slice u8)
                <:
                Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          let re_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re_as_ntt
              i
              (Libcrux_ml_kem.Ntt.ntt_binomially_sampled_ring_element #v_Vector
                  (re_as_ntt.[ i ] <: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                <:
                Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          re_as_ntt)
  in
  let _:Prims.unit =
    sample_vector_cbd_then_ntt_helper_2 v_K
      v_ETA
      v_ETA_RANDOMNESS_SIZE
      #v_Vector
      re_as_ntt
      prf_input
      v__domain_separator_init
  in
  let hax_temp_output:u8 = domain_separator in
  re_as_ntt, hax_temp_output
  <:
  (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K & u8)

#pop-options

let sample_vector_cbd_then_ntt_out
      (v_K v_ETA v_ETA_RANDOMNESS_SIZE: usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (prf_input: t_Array u8 (mk_usize 33))
      (domain_separator: u8)
     =
  let re_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Core.Array.from_fn #(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      v_K
      (fun v__i ->
          let v__i:usize = v__i in
          Libcrux_ml_kem.Polynomial.impl_2__ZERO #v_Vector ()
          <:
          Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
  in
  let tmp0, out:(t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K & u8) =
    sample_vector_cbd_then_ntt v_K
      v_ETA
      v_ETA_RANDOMNESS_SIZE
      #v_Vector
      #v_Hasher
      re_as_ntt
      prf_input
      domain_separator
  in
  let re_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K = tmp0 in
  let domain_separator:u8 = out in
  re_as_ntt, domain_separator
  <:
  (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K & u8)

#push-options "--z3rlimit 500 --ext context_pruning --z3refresh"

let generate_keypair_unpacked
      (v_K v_ETA1 v_ETA1_RANDOMNESS_SIZE: usize)
      (#v_Vector #v_Hasher #v_Scheme: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i4:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i5: Libcrux_ml_kem.Variant.t_Variant v_Scheme)
      (key_generation_seed: t_Slice u8)
      (private_key: Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector)
      (public_key: Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector)
     =
  let hashed:t_Array u8 (mk_usize 64) =
    Libcrux_ml_kem.Variant.f_cpa_keygen_seed #v_Scheme
      #FStar.Tactics.Typeclasses.solve
      v_K
      #v_Hasher
      key_generation_seed
  in
  let seed_for_A, seed_for_secret_and_error:(t_Slice u8 & t_Slice u8) =
    Core.Slice.impl__split_at #u8 (hashed <: t_Slice u8) (mk_usize 32)
  in
  let _:Prims.unit =
    Lib.Sequence.eq_intro #u8
      #32
      seed_for_A
      (Seq.slice (Libcrux_ml_kem.Utils.into_padded_array (sz 34) seed_for_A) 0 32)
  in
  let public_key:Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector =
    {
      public_key with
      Libcrux_ml_kem.Ind_cpa.Unpacked.f_A
      =
      Libcrux_ml_kem.Matrix.sample_matrix_A v_K
        #v_Vector
        #v_Hasher
        public_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_A
        (Libcrux_ml_kem.Utils.into_padded_array (mk_usize 34) seed_for_A <: t_Array u8 (mk_usize 34)
        )
        true
    }
    <:
    Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector
  in
  let _:Prims.unit =
    let matrix_A_as_ntt, valid = Spec.MLKEM.sample_matrix_A_ntt #v_K seed_for_A in
    assert (valid ==> matrix_A_as_ntt == Libcrux_ml_kem.Polynomial.to_spec_matrix_t public_key.f_A)
  in
  let (prf_input: t_Array u8 (mk_usize 33)):t_Array u8 (mk_usize 33) =
    Libcrux_ml_kem.Utils.into_padded_array (mk_usize 33) seed_for_secret_and_error
  in
  let _:Prims.unit =
    Lib.Sequence.eq_intro #u8 #32 seed_for_secret_and_error (Seq.slice prf_input 0 32)
  in
  let tmp0, out:(t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K & u8) =
    sample_vector_cbd_then_ntt v_K
      v_ETA1
      v_ETA1_RANDOMNESS_SIZE
      #v_Vector
      #v_Hasher
      private_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_secret_as_ntt
      prf_input
      (mk_u8 0)
  in
  let private_key:Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector =
    { private_key with Libcrux_ml_kem.Ind_cpa.Unpacked.f_secret_as_ntt = tmp0 }
    <:
    Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector
  in
  let domain_separator:u8 = out in
  let error_as_ntt, _:(t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K & u8
  ) =
    sample_vector_cbd_then_ntt_out v_K
      v_ETA1
      v_ETA1_RANDOMNESS_SIZE
      #v_Vector
      #v_Hasher
      prf_input
      domain_separator
  in
  let public_key:Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector =
    {
      public_key with
      Libcrux_ml_kem.Ind_cpa.Unpacked.f_t_as_ntt
      =
      Libcrux_ml_kem.Matrix.compute_As_plus_e v_K
        #v_Vector
        public_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_t_as_ntt
        public_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_A
        private_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_secret_as_ntt
        error_as_ntt
    }
    <:
    Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector
  in
  let public_key:Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector =
    {
      public_key with
      Libcrux_ml_kem.Ind_cpa.Unpacked.f_seed_for_A
      =
      Core.Result.impl__unwrap #(t_Array u8 (mk_usize 32))
        #Core.Array.t_TryFromSliceError
        (Core.Convert.f_try_into #(t_Slice u8)
            #(t_Array u8 (mk_usize 32))
            #FStar.Tactics.Typeclasses.solve
            seed_for_A
          <:
          Core.Result.t_Result (t_Array u8 (mk_usize 32)) Core.Array.t_TryFromSliceError)
    }
    <:
    Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector
  in
  let _:Prims.unit =
    let (((t_as_ntt, seed_for_A), matrix_A_as_ntt), secret_as_ntt), valid =
      Spec.MLKEM.ind_cpa_generate_keypair_unpacked v_K key_generation_seed
    in
    assert (valid ==>
        ((Libcrux_ml_kem.Polynomial.to_spec_vector_t #v_K
              #v_Vector
              public_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_t_as_ntt) ==
          t_as_ntt) /\ (public_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_seed_for_A == seed_for_A) /\
        (Libcrux_ml_kem.Polynomial.to_spec_matrix_t #v_K
            #v_Vector
            public_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_A ==
          matrix_A_as_ntt) /\
        ((Libcrux_ml_kem.Polynomial.to_spec_vector_t #v_K
              #v_Vector
              private_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_secret_as_ntt) ==
          secret_as_ntt));
    assert ((forall (i: nat).
            i < v v_K ==>
            Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index private_key
                    .Libcrux_ml_kem.Ind_cpa.Unpacked.f_secret_as_ntt
                  i)) /\
        (forall (i: nat).
            i < v v_K ==>
            Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index public_key
                    .Libcrux_ml_kem.Ind_cpa.Unpacked.f_t_as_ntt
                  i)))
  in
  private_key, public_key
  <:
  (Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector &
    Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector)

#pop-options

#push-options "--admit_smt_queries true"

let serialize_unpacked_secret_key
      (v_K v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_RANKED_BYTES_PER_RING_ELEMENT: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (public_key: Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector)
      (private_key: Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector)
     =
  let public_key_serialized:t_Array u8 v_PUBLIC_KEY_SIZE =
    serialize_public_key v_K
      v_RANKED_BYTES_PER_RING_ELEMENT
      v_PUBLIC_KEY_SIZE
      #v_Vector
      public_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_t_as_ntt
      (public_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_seed_for_A <: t_Slice u8)
  in
  let secret_key_serialized:t_Array u8 v_PRIVATE_KEY_SIZE =
    serialize_secret_key v_K
      v_PRIVATE_KEY_SIZE
      #v_Vector
      private_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_secret_as_ntt
  in
  secret_key_serialized, public_key_serialized
  <:
  (t_Array u8 v_PRIVATE_KEY_SIZE & t_Array u8 v_PUBLIC_KEY_SIZE)

#pop-options

let generate_keypair
      (v_K v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_RANKED_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher #v_Scheme: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i4:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i5: Libcrux_ml_kem.Variant.t_Variant v_Scheme)
      (key_generation_seed: t_Slice u8)
     =
  let private_key:Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector =
    Core.Default.f_default #(Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector
      )
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let public_key:Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector =
    Core.Default.f_default #(Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector)
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let tmp0, tmp1:(Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector &
    Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector) =
    generate_keypair_unpacked v_K
      v_ETA1
      v_ETA1_RANDOMNESS_SIZE
      #v_Vector
      #v_Hasher
      #v_Scheme
      key_generation_seed
      private_key
      public_key
  in
  let private_key:Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector = tmp0 in
  let public_key:Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector = tmp1 in
  let _:Prims.unit = () in
  serialize_unpacked_secret_key v_K
    v_PRIVATE_KEY_SIZE
    v_PUBLIC_KEY_SIZE
    v_RANKED_BYTES_PER_RING_ELEMENT
    #v_Vector
    public_key
    private_key

#push-options "--z3rlimit 1500 --ext context_pruning --z3refresh"

let compress_then_serialize_u
      (v_K v_OUT_LEN v_COMPRESSION_FACTOR v_BLOCK_LEN: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (input: t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (out: t_Slice u8)
     =
  let _:Prims.unit =
    assert (v (sz 32 *! v_COMPRESSION_FACTOR) == 32 * v v_COMPRESSION_FACTOR);
    assert (v (v_OUT_LEN /! v_K) == v v_OUT_LEN / v v_K);
    assert (v v_OUT_LEN / v v_K == 32 * v v_COMPRESSION_FACTOR)
  in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Folds.fold_enumerated_slice input
      (fun out i ->
          let out:t_Slice u8 = out in
          let i:usize = i in
          (v i < v v_K ==>
            Seq.length out == v v_OUT_LEN /\
            Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index input (v i))) /\
          (forall (j: nat).
              j < v i ==>
              Seq.length out == v v_OUT_LEN /\ (j + 1) * (v v_OUT_LEN / v v_K) <= Seq.length out /\
              (Seq.slice out (j * (v v_OUT_LEN / v v_K)) (((j + 1)) * (v v_OUT_LEN / v v_K)) ==
                Spec.MLKEM.compress_then_byte_encode (v v_COMPRESSION_FACTOR)
                  (Libcrux_ml_kem.Polynomial.to_spec_poly_t #v_Vector (Seq.index input j)))))
      out
      (fun out temp_1_ ->
          let out:t_Slice u8 = out in
          let i, re:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
            temp_1_
          in
          let _:Prims.unit =
            assert (forall (j: nat).
                  j < v i ==>
                  ((Seq.slice out (j * (v v_OUT_LEN / v v_K)) (((j + 1)) * (v v_OUT_LEN / v v_K)) ==
                      Spec.MLKEM.compress_then_byte_encode (v v_COMPRESSION_FACTOR)
                        (Libcrux_ml_kem.Polynomial.to_spec_poly_t #v_Vector (Seq.index input j)))))
          in
          let out:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
              ({
                  Core.Ops.Range.f_start = i *! (v_OUT_LEN /! v_K <: usize) <: usize;
                  Core.Ops.Range.f_end
                  =
                  (i +! mk_usize 1 <: usize) *! (v_OUT_LEN /! v_K <: usize) <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
              (Core.Slice.impl__copy_from_slice #u8
                  (out.[ {
                        Core.Ops.Range.f_start = i *! (v_OUT_LEN /! v_K <: usize) <: usize;
                        Core.Ops.Range.f_end
                        =
                        (i +! mk_usize 1 <: usize) *! (v_OUT_LEN /! v_K <: usize) <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (Libcrux_ml_kem.Serialize.compress_then_serialize_ring_element_u v_COMPRESSION_FACTOR
                      v_BLOCK_LEN
                      #v_Vector
                      re
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
          in
          let _:Prims.unit =
            let lemma_aux (j: nat{j < v i})
                : Lemma
                (Seq.slice out (j * (v v_OUT_LEN / v v_K)) (((j + 1)) * (v v_OUT_LEN / v v_K)) ==
                  Spec.MLKEM.compress_then_byte_encode (v v_COMPRESSION_FACTOR)
                    (Libcrux_ml_kem.Polynomial.to_spec_poly_t #v_Vector (Seq.index input j))) =
              Lib.Sequence.eq_intro #u8
                #(v v_OUT_LEN / v v_K)
                (Seq.slice out (j * (v v_OUT_LEN / v v_K)) (((j + 1)) * (v v_OUT_LEN / v v_K)))
                (Spec.MLKEM.compress_then_byte_encode (v v_COMPRESSION_FACTOR)
                    (Libcrux_ml_kem.Polynomial.to_spec_poly_t #v_Vector (Seq.index input j)))
            in
            Classical.forall_intro lemma_aux
          in
          out)
  in
  let _:Prims.unit =
    Lib.Sequence.eq_intro #u8
      #(v v_OUT_LEN)
      out
      (Spec.MLKEM.compress_then_encode_u #v_K
          (Libcrux_ml_kem.Polynomial.to_spec_vector_t #v_K #v_Vector input))
  in
  out

#pop-options

#push-options "--z3rlimit 800 --ext context_pruning --z3refresh"

let encrypt_unpacked
      (v_K v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_LEN v_C2_LEN v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR v_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (public_key: Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector)
      (message: t_Array u8 (mk_usize 32))
      (randomness: t_Slice u8)
     =
  let (prf_input: t_Array u8 (mk_usize 33)):t_Array u8 (mk_usize 33) =
    Libcrux_ml_kem.Utils.into_padded_array (mk_usize 33) randomness
  in
  let r_as_ntt, domain_separator:(t_Array
      (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K &
    u8) =
    sample_vector_cbd_then_ntt_out v_K
      v_ETA1
      v_ETA1_RANDOMNESS_SIZE
      #v_Vector
      #v_Hasher
      prf_input
      (mk_u8 0)
  in
  let _:Prims.unit =
    Lib.Sequence.eq_intro #u8 #32 randomness (Seq.slice prf_input 0 32);
    assert (v domain_separator == v v_K)
  in
  let error_1_, domain_separator:(t_Array
      (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K &
    u8) =
    sample_ring_element_cbd v_K
      v_ETA2_RANDOMNESS_SIZE
      v_ETA2
      #v_Vector
      #v_Hasher
      prf_input
      domain_separator
  in
  let prf_input:t_Array u8 (mk_usize 33) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize prf_input
      (mk_usize 32)
      domain_separator
  in
  let _:Prims.unit =
    assert (Seq.equal prf_input (Seq.append randomness (Seq.create 1 domain_separator)));
    assert (prf_input == Seq.append randomness (Seq.create 1 domain_separator))
  in
  let (prf_output: t_Array u8 v_ETA2_RANDOMNESS_SIZE):t_Array u8 v_ETA2_RANDOMNESS_SIZE =
    Libcrux_ml_kem.Hash_functions.f_PRF #v_Hasher
      #v_K
      #FStar.Tactics.Typeclasses.solve
      v_ETA2_RANDOMNESS_SIZE
      (prf_input <: t_Slice u8)
  in
  let error_2_:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Sampling.sample_from_binomial_distribution v_ETA2
      #v_Vector
      (prf_output <: t_Slice u8)
  in
  let u:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Libcrux_ml_kem.Matrix.compute_vector_u v_K
      #v_Vector
      public_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_A
      r_as_ntt
      error_1_
  in
  let message_as_ring_element:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Serialize.deserialize_then_decompress_message #v_Vector message
  in
  let v:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Matrix.compute_ring_element_v v_K
      #v_Vector
      public_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_t_as_ntt
      r_as_ntt
      error_2_
      message_as_ring_element
  in
  let _:Prims.unit =
    assert (v_C1_LEN = Spec.MLKEM.v_C1_SIZE v_K);
    assert (v_C2_LEN = Spec.MLKEM.v_C2_SIZE v_K);
    assert (v_CIPHERTEXT_SIZE == v_C1_LEN +! v_C2_LEN);
    assert (v_C1_LEN <=. v_CIPHERTEXT_SIZE)
  in
  let ciphertext:t_Array u8 v_CIPHERTEXT_SIZE =
    Rust_primitives.Hax.repeat (mk_u8 0) v_CIPHERTEXT_SIZE
  in
  let ciphertext:t_Array u8 v_CIPHERTEXT_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range ciphertext
      ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = v_C1_LEN }
        <:
        Core.Ops.Range.t_Range usize)
      (compress_then_serialize_u v_K
          v_C1_LEN
          v_U_COMPRESSION_FACTOR
          v_BLOCK_LEN
          #v_Vector
          u
          (ciphertext.[ { Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = v_C1_LEN }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let ciphertext:t_Array u8 v_CIPHERTEXT_SIZE =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from ciphertext
      ({ Core.Ops.Range.f_start = v_C1_LEN } <: Core.Ops.Range.t_RangeFrom usize)
      (Libcrux_ml_kem.Serialize.compress_then_serialize_ring_element_v v_K
          v_V_COMPRESSION_FACTOR
          v_C2_LEN
          #v_Vector
          v
          (ciphertext.[ { Core.Ops.Range.f_start = v_C1_LEN } <: Core.Ops.Range.t_RangeFrom usize ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let _:Prims.unit =
    lemma_slice_append ciphertext
      (Seq.slice ciphertext 0 (Rust_primitives.v v_C1_LEN))
      (Seq.slice ciphertext (Rust_primitives.v v_C1_LEN) (Seq.length ciphertext))
  in
  ciphertext

#pop-options

let build_unpacked_public_key_mut
      (v_K v_T_AS_NTT_ENCODED_SIZE: usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (public_key: t_Slice u8)
      (unpacked_public_key: Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector)
     =
  let unpacked_public_key:Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector =
    {
      unpacked_public_key with
      Libcrux_ml_kem.Ind_cpa.Unpacked.f_t_as_ntt
      =
      Libcrux_ml_kem.Serialize.deserialize_ring_elements_reduced v_K
        #v_Vector
        (public_key.[ { Core.Ops.Range.f_end = v_T_AS_NTT_ENCODED_SIZE }
            <:
            Core.Ops.Range.t_RangeTo usize ]
          <:
          t_Slice u8)
        unpacked_public_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_t_as_ntt
    }
    <:
    Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector
  in
  let seed:t_Slice u8 =
    public_key.[ { Core.Ops.Range.f_start = v_T_AS_NTT_ENCODED_SIZE }
      <:
      Core.Ops.Range.t_RangeFrom usize ]
  in
  let _:Prims.unit =
    Lib.Sequence.eq_intro #u8
      #32
      seed
      (Seq.slice (Libcrux_ml_kem.Utils.into_padded_array (sz 34) seed) 0 32)
  in
  let unpacked_public_key:Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector =
    {
      unpacked_public_key with
      Libcrux_ml_kem.Ind_cpa.Unpacked.f_A
      =
      Libcrux_ml_kem.Matrix.sample_matrix_A v_K
        #v_Vector
        #v_Hasher
        unpacked_public_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_A
        (Libcrux_ml_kem.Utils.into_padded_array (mk_usize 34) seed <: t_Array u8 (mk_usize 34))
        false
    }
    <:
    Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector
  in
  unpacked_public_key

let build_unpacked_public_key
      (v_K v_T_AS_NTT_ENCODED_SIZE: usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (public_key: t_Slice u8)
     =
  let unpacked_public_key:Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector =
    Core.Default.f_default #(Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector)
      #FStar.Tactics.Typeclasses.solve
      ()
  in
  let unpacked_public_key:Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector =
    build_unpacked_public_key_mut v_K
      v_T_AS_NTT_ENCODED_SIZE
      #v_Vector
      #v_Hasher
      public_key
      unpacked_public_key
  in
  unpacked_public_key

#push-options "--z3rlimit 500 --ext context_pruning"

let encrypt
      (v_K v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_LEN v_C2_LEN v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR v_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (public_key: t_Slice u8)
      (message: t_Array u8 (mk_usize 32))
      (randomness: t_Slice u8)
     =
  let _:Prims.unit = reveal_opaque (`%Spec.MLKEM.ind_cpa_encrypt) Spec.MLKEM.ind_cpa_encrypt in
  let unpacked_public_key:Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector =
    build_unpacked_public_key v_K v_T_AS_NTT_ENCODED_SIZE #v_Vector #v_Hasher public_key
  in
  encrypt_unpacked v_K v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_LEN v_C2_LEN
    v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR v_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2
    v_ETA2_RANDOMNESS_SIZE #v_Vector #v_Hasher unpacked_public_key message randomness

#pop-options

#push-options "--z3rlimit 800 --ext context_pruning"

let deserialize_then_decompress_u
      (v_K v_CIPHERTEXT_SIZE v_U_COMPRESSION_FACTOR: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (ciphertext: t_Array u8 v_CIPHERTEXT_SIZE)
     =
  let _:Prims.unit =
    assert (v ((Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *! v_U_COMPRESSION_FACTOR) /!
            sz 8) ==
        v (Spec.MLKEM.v_C1_BLOCK_SIZE v_K))
  in
  let u_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Core.Array.from_fn #(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      v_K
      (fun temp_0_ ->
          let _:usize = temp_0_ in
          Libcrux_ml_kem.Polynomial.impl_2__ZERO #v_Vector ()
          <:
          Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
  in
  let u_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice ((Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT *!
          v_U_COMPRESSION_FACTOR
          <:
          usize) /!
        mk_usize 8
        <:
        usize)
      (ciphertext <: t_Slice u8)
      (fun u_as_ntt i ->
          let u_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            u_as_ntt
          in
          let i:usize = i in
          forall (j: nat).
            j < v i ==>
            j * v (Spec.MLKEM.v_C1_BLOCK_SIZE v_K) + v (Spec.MLKEM.v_C1_BLOCK_SIZE v_K) <=
            v v_CIPHERTEXT_SIZE /\
            Libcrux_ml_kem.Polynomial.to_spec_poly_t #v_Vector (Seq.index u_as_ntt j) ==
            Spec.MLKEM.poly_ntt (Spec.MLKEM.byte_decode_then_decompress (v v_U_COMPRESSION_FACTOR)
                  (Seq.slice ciphertext
                      (j * v (Spec.MLKEM.v_C1_BLOCK_SIZE v_K))
                      (j * v (Spec.MLKEM.v_C1_BLOCK_SIZE v_K) + v (Spec.MLKEM.v_C1_BLOCK_SIZE v_K)))
              ))
      u_as_ntt
      (fun u_as_ntt temp_1_ ->
          let u_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            u_as_ntt
          in
          let i, u_bytes:(usize & t_Slice u8) = temp_1_ in
          let u_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize u_as_ntt
              i
              (Libcrux_ml_kem.Serialize.deserialize_then_decompress_ring_element_u v_U_COMPRESSION_FACTOR
                  #v_Vector
                  u_bytes
                <:
                Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          let u_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize u_as_ntt
              i
              (Libcrux_ml_kem.Ntt.ntt_vector_u v_U_COMPRESSION_FACTOR
                  #v_Vector
                  (u_as_ntt.[ i ] <: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                <:
                Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          u_as_ntt)
  in
  let _:Prims.unit =
    Lib.Sequence.eq_intro #Spec.MLKEM.polynomial
      #(v v_K)
      (Libcrux_ml_kem.Polynomial.to_spec_vector_t #v_K #v_Vector u_as_ntt)
      (let open Spec.MLKEM in
        vector_ntt (decode_then_decompress_u #v_K
              (Seq.slice ciphertext 0 (v (Spec.MLKEM.v_C1_SIZE v_K)))))
  in
  u_as_ntt

#pop-options

#push-options "--z3rlimit 800 --ext context_pruning"

let deserialize_secret_key
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (secret_key: t_Slice u8)
     =
  let _:Prims.unit = assert_norm (Spec.MLKEM.polynomial_d 12 == Spec.MLKEM.polynomial) in
  let secret_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Core.Array.from_fn #(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      v_K
      (fun temp_0_ ->
          let _:usize = temp_0_ in
          Libcrux_ml_kem.Polynomial.impl_2__ZERO #v_Vector ()
          <:
          Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
  in
  let secret_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Rust_primitives.Hax.Folds.fold_enumerated_chunked_slice Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT
      secret_key
      (fun secret_as_ntt i ->
          let secret_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K
          =
            secret_as_ntt
          in
          let i:usize = i in
          forall (j: nat).
            j < v i ==>
            j * v Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT +
            v Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT <=
            v (Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE v_K) /\
            Libcrux_ml_kem.Polynomial.to_spec_poly_t #v_Vector (Seq.index secret_as_ntt j) ==
            Spec.MLKEM.byte_decode 12
              (Seq.slice secret_key
                  (j * v Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT)
                  (j * v Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT +
                    v Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT)))
      secret_as_ntt
      (fun secret_as_ntt temp_1_ ->
          let secret_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K
          =
            secret_as_ntt
          in
          let i, secret_bytes:(usize & t_Slice u8) = temp_1_ in
          let secret_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K
          =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize secret_as_ntt
              i
              (Libcrux_ml_kem.Serialize.deserialize_to_uncompressed_ring_element #v_Vector
                  secret_bytes
                <:
                Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          secret_as_ntt)
  in
  let _:Prims.unit =
    Lib.Sequence.eq_intro #Spec.MLKEM.polynomial
      #(v v_K)
      (Libcrux_ml_kem.Polynomial.to_spec_vector_t #v_K #v_Vector secret_as_ntt)
      (Spec.MLKEM.vector_decode_12 #v_K secret_key)
  in
  secret_as_ntt

#pop-options

let decrypt_unpacked
      (v_K v_CIPHERTEXT_SIZE v_VECTOR_U_ENCODED_SIZE v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR:
          usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (secret_key: Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector)
      (ciphertext: t_Array u8 v_CIPHERTEXT_SIZE)
     =
  let u_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    deserialize_then_decompress_u v_K v_CIPHERTEXT_SIZE v_U_COMPRESSION_FACTOR #v_Vector ciphertext
  in
  let v:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Serialize.deserialize_then_decompress_ring_element_v v_K
      v_V_COMPRESSION_FACTOR
      #v_Vector
      (ciphertext.[ { Core.Ops.Range.f_start = v_VECTOR_U_ENCODED_SIZE }
          <:
          Core.Ops.Range.t_RangeFrom usize ]
        <:
        t_Slice u8)
  in
  let message:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Matrix.compute_message v_K
      #v_Vector
      v
      secret_key.Libcrux_ml_kem.Ind_cpa.Unpacked.f_secret_as_ntt
      u_as_ntt
  in
  Libcrux_ml_kem.Serialize.compress_then_serialize_message #v_Vector message

let decrypt
      (v_K v_CIPHERTEXT_SIZE v_VECTOR_U_ENCODED_SIZE v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR:
          usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (secret_key: t_Slice u8)
      (ciphertext: t_Array u8 v_CIPHERTEXT_SIZE)
     =
  let _:Prims.unit = reveal_opaque (`%Spec.MLKEM.ind_cpa_decrypt) Spec.MLKEM.ind_cpa_decrypt in
  let secret_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    deserialize_secret_key v_K #v_Vector secret_key
  in
  let secret_key_unpacked:Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector =
    { Libcrux_ml_kem.Ind_cpa.Unpacked.f_secret_as_ntt = secret_as_ntt }
    <:
    Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector
  in
  decrypt_unpacked v_K
    v_CIPHERTEXT_SIZE
    v_VECTOR_U_ENCODED_SIZE
    v_U_COMPRESSION_FACTOR
    v_V_COMPRESSION_FACTOR
    #v_Vector
    secret_key_unpacked
    ciphertext
