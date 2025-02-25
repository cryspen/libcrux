use core::array::from_fn;

use crate::{
    constants::{
        ranked_bytes_per_ring_element, BYTES_PER_RING_ELEMENT, COEFFICIENTS_IN_RING_ELEMENT,
        SHARED_SECRET_SIZE,
    },
    hash_functions::Hash,
    helper::cloop,
    matrix::*,
    ntt::{ntt_binomially_sampled_ring_element, ntt_vector_u},
    polynomial::PolynomialRingElement,
    sampling::sample_from_binomial_distribution,
    serialize::{
        compress_then_serialize_message, compress_then_serialize_ring_element_u,
        compress_then_serialize_ring_element_v, deserialize_ring_elements_reduced,
        deserialize_then_decompress_message, deserialize_then_decompress_ring_element_u,
        deserialize_then_decompress_ring_element_v, deserialize_to_uncompressed_ring_element,
        serialize_uncompressed_ring_element,
    },
    utils::{into_padded_array, prf_input_inc},
    variant::Variant,
    vector::Operations,
};

// #[libcrux_macros::ml_kem_parameter_sets(512,768,1024)]
#[libcrux_macros::ml_kem_parameter_sets_ind_cpa(512)]
pub(crate) mod generic {
    use super::*;

    use crate::constants::{BITS_PER_COEFFICIENT, H_DIGEST_SIZE};

    // These constants are derived from the ones injected from
    // [crate::constants::mlkem<id>] by
    // [libcrux_macros::ml_kem_parameter_sets].
    #[cfg(any(feature = "incremental", eurydice))]
    const RANKED_BYTES_PER_RING_ELEMENT: usize = RANK * BITS_PER_RING_ELEMENT / 8;
    const T_AS_NTT_ENCODED_SIZE: usize =
        (RANK * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;
    const C1_BLOCK_SIZE: usize = (COEFFICIENTS_IN_RING_ELEMENT * VECTOR_U_COMPRESSION_FACTOR) / 8;
    const C1_SIZE: usize = C1_BLOCK_SIZE * RANK;
    const C2_SIZE: usize = (COEFFICIENTS_IN_RING_ELEMENT * VECTOR_V_COMPRESSION_FACTOR) / 8;
    const CPA_PKE_SECRET_KEY_SIZE: usize =
        (RANK * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;
    pub(crate) const CPA_PKE_PUBLIC_KEY_SIZE: usize = T_AS_NTT_ENCODED_SIZE + 32;
    const CPA_PKE_CIPHERTEXT_SIZE: usize = C1_SIZE + C2_SIZE;
    pub(crate) const SECRET_KEY_SIZE: usize =
        CPA_PKE_SECRET_KEY_SIZE + CPA_PKE_PUBLIC_KEY_SIZE + H_DIGEST_SIZE + SHARED_SECRET_SIZE;
    const ETA1_RANDOMNESS_SIZE: usize = ETA1 * 64;
    const ETA2_RANDOMNESS_SIZE: usize = ETA2 * 64;
    const IMPLICIT_REJECTION_HASH_INPUT_SIZE: usize = SHARED_SECRET_SIZE + CPA_PKE_CIPHERTEXT_SIZE;

    /// Types for the unpacked API.
    #[allow(non_snake_case)]
    pub(crate) mod unpacked {
        use super::*;
        use crate::{polynomial::PolynomialRingElement, vector::traits::Operations};

        /// An unpacked ML-KEM IND-CPA Private Key
        pub(crate) struct IndCpaPrivateKeyUnpacked<Vector: Operations> {
            pub(crate) secret_as_ntt: [PolynomialRingElement<Vector>; RANK],
        }

        impl<Vector: Operations> Default for IndCpaPrivateKeyUnpacked<Vector> {
            fn default() -> Self {
                Self {
                    secret_as_ntt: [PolynomialRingElement::<Vector>::ZERO(); RANK],
                }
            }
        }

        /// An unpacked ML-KEM IND-CPA Public Key
        #[derive(Clone)]
        pub(crate) struct IndCpaPublicKeyUnpacked<Vector: Operations> {
            pub(crate) t_as_ntt: [PolynomialRingElement<Vector>; RANK],
            pub(crate) seed_for_A: [u8; 32],
            pub(crate) A: [PolynomialRingElement<Vector>; RANK * RANK],
        }

        impl<Vector: Operations> Default for IndCpaPublicKeyUnpacked<Vector> {
            fn default() -> Self {
                Self {
                    t_as_ntt: [PolynomialRingElement::<Vector>::ZERO(); RANK],
                    seed_for_A: [0u8; 32],
                    A: [PolynomialRingElement::<Vector>::ZERO(); RANK * RANK],
                }
            }
        }
    }
    use unpacked::*;

    /// Concatenate `t` and `ρ` into the public key.
    #[inline(always)]
    #[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
    $PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K /\
    length $seed_for_a == sz 32 /\
    (forall (i:nat). i < v $K ==>
        Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index $t_as_ntt i))"#))]
    #[hax_lib::ensures(|res|
    fstar!(r#"${serialized}_future == 
                        Seq.append (Spec.MLKEM.vector_encode_12 #$K
                            (Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector $t_as_ntt))
                        $seed_for_a)"#)
)]
    pub(crate) fn serialize_public_key_mut<Vector: Operations>(
        t_as_ntt: &[PolynomialRingElement<Vector>; RANK],
        seed_for_a: &[u8],
        serialized: &mut [u8; CPA_PKE_PUBLIC_KEY_SIZE],
    ) {
        serialize_vector::<Vector>(
            t_as_ntt,
            &mut serialized[0..ranked_bytes_per_ring_element(RANK)],
        );

        serialized[ranked_bytes_per_ring_element(RANK)..].copy_from_slice(seed_for_a);
        hax_lib::fstar!(
            "Lib.Sequence.eq_intro #u8 #(v $PUBLIC_KEY_SIZE) serialized
        (Seq.append (Spec.MLKEM.vector_encode_12 #$K (Libcrux_ml_kem.Polynomial.to_spec_vector_t
            #$K #$:Vector $t_as_ntt)) $seed_for_a)"
        );
    }

    /// Call [`serialize_uncompressed_ring_element`] for each ring element.
    #[inline(always)]
    #[hax_lib::fstar::options("--z3rlimit 1000 --ext context_pruning --z3refresh")]
    #[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
    ${out.len()} == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K /\
    (forall (i:nat). i < v $K ==>
        Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index $key i))"#))]
    #[hax_lib::ensures(|()|
    fstar!(r#"$out == Spec.MLKEM.vector_encode_12 #$K
            (Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector $key)"#)
)]
    pub(crate) fn serialize_vector<Vector: Operations>(
        key: &[PolynomialRingElement<Vector>; RANK],
        out: &mut [u8],
    ) {
        hax_lib::fstar!(r#"assert_norm (Spec.MLKEM.polynomial_d 12 == Spec.MLKEM.polynomial)"#);

        cloop! {
            for (i, re) in key.into_iter().enumerate() {
                hax_lib::loop_invariant!(|i: usize| {
                    fstar!(r#"
                    (v $i < v $K ==>
                    Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index $key (v $i))) /\
                    (forall (j: nat). j < v $i ==>
                    (j + 1) * v $BYTES_PER_RING_ELEMENT <= Seq.length $out /\
                    (Seq.slice $out (j * v $BYTES_PER_RING_ELEMENT) ((j + 1) * v $BYTES_PER_RING_ELEMENT) ==
                        Spec.MLKEM.byte_encode 12 (Libcrux_ml_kem.Polynomial.to_spec_poly_t #$:Vector (Seq.index $key j))))"#
                    )
                });

                out[i * BYTES_PER_RING_ELEMENT..(i + 1) * BYTES_PER_RING_ELEMENT]
                .copy_from_slice(&serialize_uncompressed_ring_element(&re));

                hax_lib::fstar!(r#"
                let lemma_aux (j: nat{ j < v $i }) : Lemma
                (Seq.slice out (j * v $BYTES_PER_RING_ELEMENT) ((j + 1) * v $BYTES_PER_RING_ELEMENT) ==
                    Spec.MLKEM.byte_encode 12 (Libcrux_ml_kem.Polynomial.to_spec_poly_t #$:Vector (Seq.index $key j))) =
                Lib.Sequence.eq_intro #u8 #(v $BYTES_PER_RING_ELEMENT)
                (Seq.slice out (j * v $BYTES_PER_RING_ELEMENT) ((j + 1) * v $BYTES_PER_RING_ELEMENT))
                (Spec.MLKEM.byte_encode 12 (Libcrux_ml_kem.Polynomial.to_spec_poly_t #$:Vector (Seq.index $key j)))
                in
                Classical.forall_intro lemma_aux"#
                );
            }
        }

        hax_lib::fstar!(
            r#"assert (Spec.MLKEM.coerce_vector_12 (Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector $key) ==
        Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector $key);
        reveal_opaque (`%Spec.MLKEM.vector_encode_12) (Spec.MLKEM.vector_encode_12 #$K);
        Lib.Sequence.eq_intro #u8 #(v (Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K)) $out
          (Spec.MLKEM.vector_encode_12 #$K
            (Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector $key))"#
        );
    }

    /// Sample a vector of ring elements from a centered binomial distribution.
    #[inline(always)]
    #[hax_lib::fstar::options(
        "--max_fuel 15 --z3rlimit 1500 --ext context_pruning --z3refresh --split_queries always"
    )]
    #[cfg_attr(
        hax,
        hax_lib::fstar::before(
            r#"let sample_ring_element_cbd_helper_2
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
    (Spec.MLKEM.sample_vector_cbd2 #v_K (Seq.slice prf_input 0 32) (sz (v domain_separator)))"#
        )
    )]
    #[cfg_attr(
        hax,
        hax_lib::fstar::before(
            r#"let sample_ring_element_cbd_helper_1
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
        (Seq.slice prf_input 0 32) (sz (v domain_separator))))"#
        )
    )]
    #[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
    $ETA2_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA2_RANDOMNESS_SIZE $K /\
    $ETA2 == Spec.MLKEM.v_ETA2 $K /\
    v $domain_separator < 2 * v $K /\
    range (v $domain_separator + v $K) u8_inttype"#))]
    #[hax_lib::ensures(|(err1,ds)|
    fstar!(r#"v $ds == v $domain_separator + v $K /\
                Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector $err1 ==
                Spec.MLKEM.sample_vector_cbd2 #$K (Seq.slice $prf_input 0 32) (sz (v $domain_separator))"#)
)]
    fn sample_ring_element_cbd<Vector: Operations, Hasher: Hash>(
        prf_input: [u8; 33],
        mut domain_separator: u8,
        error_1: &mut [PolynomialRingElement<Vector>],
    ) -> u8 {
        let mut prf_inputs = [prf_input; RANK];
        // See https://github.com/hacspec/hax/issues/1167
        let _domain_separator_init = domain_separator;
        domain_separator = prf_input_inc(&mut prf_inputs, domain_separator);
        hax_lib::fstar!(
            "sample_ring_element_cbd_helper_1 $K $prf_inputs $prf_input $_domain_separator_init"
        );
        let mut prf_outputs = [0u8; ETA2_RANDOMNESS_SIZE * RANK];
        Hasher::PRFxN(&prf_inputs, &mut prf_outputs, ETA2_RANDOMNESS_SIZE);
        for i in 0..RANK {
            hax_lib::loop_invariant!(|i: usize| {
                fstar!(
                    "forall (j:nat). j < v $i ==>
            Libcrux_ml_kem.Polynomial.to_spec_poly_t #$:Vector ${error_1}.[ sz j ] ==
              Spec.MLKEM.sample_poly_cbd $ETA2 ${prf_outputs}.[ sz j ]"
                )
            });
            error_1[i] = sample_from_binomial_distribution::<Vector>(
                &prf_outputs[i * ETA2_RANDOMNESS_SIZE..(i + 1) * ETA2_RANDOMNESS_SIZE],
                ETA2,
            );
        }
        hax_lib::fstar!(
            "sample_ring_element_cbd_helper_2
        $K $ETA2 $ETA2_RANDOMNESS_SIZE #$:Vector error_1_ $prf_input $_domain_separator_init"
        );
        domain_separator
    }

    /// Sample a vector of ring elements from a centered binomial distribution and
    /// convert them into their NTT representations.
    #[inline(always)]
    #[hax_lib::fstar::options(
        "--max_fuel 25 --z3rlimit 2500 --ext context_pruning --z3refresh --split_queries always"
    )]
    #[cfg_attr(hax, hax_lib::fstar::before(r#"let sample_vector_cbd_then_ntt_helper_2
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
        (Seq.slice prf_input 0 32) (sz (v domain_separator)))"#))]
    #[cfg_attr(
        hax,
        hax_lib::fstar::before(
            r#"let sample_vector_cbd_then_ntt_helper_1
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
        (Seq.slice prf_input 0 32) (sz (v domain_separator))))"#
        )
    )]
    #[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
    $ETA_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE $K /\
    $ETA == Spec.MLKEM.v_ETA1 $K /\
    v $domain_separator < 2 * v $K /\
    range (v $domain_separator + v $K) u8_inttype"#))]
    #[hax_lib::ensures(|ds|
    fstar!(r#"v $ds == v $domain_separator + v $K /\
            Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector ${re_as_ntt}_future ==
            Spec.MLKEM.sample_vector_cbd_then_ntt #$K (Seq.slice $prf_input 0 32) (sz (v $domain_separator)) /\
            (forall (i: nat). i < v $K ==>
              Libcrux_ml_kem.Serialize.coefficients_field_modulus_range #$:Vector (Seq.index ${re_as_ntt}_future i))"#)
)]
    fn sample_vector_cbd_then_ntt<Vector: Operations, Hasher: Hash>(
        re_as_ntt: &mut [PolynomialRingElement<Vector>; RANK],
        prf_input: [u8; 33],
        mut domain_separator: u8,
    ) -> u8 {
        let mut prf_inputs = [prf_input; RANK];
        let _domain_separator_init = domain_separator;
        domain_separator = prf_input_inc(&mut prf_inputs, domain_separator);
        hax_lib::fstar!(
            "sample_vector_cbd_then_ntt_helper_1 $K $prf_inputs $prf_input $_domain_separator_init"
        );
        let mut prf_outputs = [0u8; ETA1_RANDOMNESS_SIZE * RANK];
        Hasher::PRFxN(&prf_inputs, &mut prf_outputs, ETA1_RANDOMNESS_SIZE);
        for i in 0..RANK {
            hax_lib::loop_invariant!(|i: usize| {
                fstar!(
                    r#"forall (j:nat). j < v $i ==>
            Libcrux_ml_kem.Polynomial.to_spec_poly_t #$:Vector re_as_ntt.[ sz j ] ==
              Spec.MLKEM.poly_ntt (Spec.MLKEM.sample_poly_cbd $ETA ${prf_outputs}.[ sz j ]) /\
            Libcrux_ml_kem.Serialize.coefficients_field_modulus_range #$:Vector re_as_ntt.[ sz j ]"#
                )
            });
            re_as_ntt[i] = sample_from_binomial_distribution::<Vector>(
                &prf_outputs[i * ETA1_RANDOMNESS_SIZE..(i + 1) * ETA1_RANDOMNESS_SIZE],
                ETA1,
            );
            ntt_binomially_sampled_ring_element(&mut re_as_ntt[i]);
        }
        hax_lib::fstar!(
            "sample_vector_cbd_then_ntt_helper_2
        $K $ETA $ETA_RANDOMNESS_SIZE #$:Vector re_as_ntt $prf_input $_domain_separator_init"
        );
        domain_separator
    }

    #[inline(always)]
    #[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
    $ETA_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE $K /\
    $ETA == Spec.MLKEM.v_ETA1 $K /\
    v $domain_separator < 2 * v $K /\
    range (v $domain_separator + v $K) u8_inttype"#))]
    #[hax_lib::ensures(|(re,ds)|
    fstar!(r#"v $ds == v $domain_separator + v $K /\
                Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector ${re} ==
                Spec.MLKEM.sample_vector_cbd_then_ntt #$K (Seq.slice $prf_input 0 32) (sz (v $domain_separator))"#)
)]
    fn sample_vector_cbd_then_ntt_out<Vector: Operations, Hasher: Hash>(
        prf_input: [u8; 33],
        mut domain_separator: u8,
        re_as_ntt: &mut [PolynomialRingElement<Vector>; RANK],
    ) -> u8 {
        domain_separator =
            sample_vector_cbd_then_ntt::<Vector, Hasher>(re_as_ntt, prf_input, domain_separator);
        domain_separator
    }

    /// This function implements most of <strong>Algorithm 12</strong> of the
    /// NIST FIPS 203 specification; this is the Kyber CPA-PKE key generation algorithm.
    ///
    /// We say "most of" since Algorithm 12 samples the required randomness within
    /// the function itself, whereas this implementation expects it to be provided
    /// through the `key_generation_seed` parameter.
    ///
    /// Algorithm 12 is reproduced below:
    ///
    /// ```plaintext
    /// Output: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
    /// Output: decryption key dkₚₖₑ ∈ 𝔹^{384k}.
    ///
    /// d ←$ B
    /// (ρ,σ) ← G(d)
    /// N ← 0
    /// for (i ← 0; i < k; i++)
    ///     for(j ← 0; j < k; j++)
    ///         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
    ///     end for
    /// end for
    /// for(i ← 0; i < k; i++)
    ///     s[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(σ,N))
    ///     N ← N + 1
    /// end for
    /// for(i ← 0; i < k; i++)
    ///     e[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(σ,N))
    ///     N ← N + 1
    /// end for
    /// ŝ ← NTT(s)
    /// ê ← NTT(e)
    /// t̂ ← Â◦ŝ + ê
    /// ekₚₖₑ ← ByteEncode₁₂(t̂) ‖ ρ
    /// dkₚₖₑ ← ByteEncode₁₂(ŝ)
    /// ```
    ///
    /// The NIST FIPS 203 standard can be found at
    /// <https://csrc.nist.gov/pubs/fips/203/ipd>.
    #[allow(non_snake_case)]
    #[hax_lib::fstar::options("--z3rlimit 500 --ext context_pruning --z3refresh")]
    #[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
    $ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE $K /\
    $ETA1 == Spec.MLKEM.v_ETA1 $K /\
    length $key_generation_seed == Spec.MLKEM.v_CPA_KEY_GENERATION_SEED_SIZE"#))]
    #[hax_lib::ensures(|_|
    {
    let public_key_future = future(public_key);
    {fstar!(r#"let ((((t_as_ntt,seed_for_A), matrix_A_as_ntt), secret_as_ntt), valid) = Spec.MLKEM.ind_cpa_generate_keypair_unpacked $K $key_generation_seed in 
    (valid ==> (Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector ${public_key_future.t_as_ntt} == t_as_ntt) /\
        (${public_key}_future.f_seed_for_A == seed_for_A) /\
        (Libcrux_ml_kem.Polynomial.to_spec_matrix_t #$K #$:Vector ${public_key}_future.f_A == matrix_A_as_ntt) /\
        (Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector ${private_key}_future.f_secret_as_ntt == secret_as_ntt)) /\
    (forall (i:nat). i < v $K ==>
        Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index ${private_key}_future.f_secret_as_ntt i)) /\
    (forall (i:nat). i < v $K ==>
        Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index ${public_key_future.t_as_ntt} i))
"#)}})]
    #[inline(always)]
    pub(crate) fn generate_keypair_unpacked<Vector: Operations, Hasher: Hash, Scheme: Variant>(
        key_generation_seed: &[u8],
        private_key: &mut IndCpaPrivateKeyUnpacked<Vector>,
        public_key: &mut IndCpaPublicKeyUnpacked<Vector>,
    ) {
        // (ρ,σ) := G(d) for Kyber, (ρ,σ) := G(d || K) for ML-KEM
        let mut hashed = [0u8; 64];
        Scheme::cpa_keygen_seed::<Hasher>(key_generation_seed, RANK, &mut hashed);
        let (seed_for_A, seed_for_secret_and_error) = hashed.split_at(32);

        hax_lib::fstar!(
            "Lib.Sequence.eq_intro #u8 #32 $seed_for_A
        (Seq.slice (Libcrux_ml_kem.Utils.into_padded_array (sz 34) $seed_for_A) 0 32)"
        );
        let mut seeds = [[0u8; 34]; RANK];
        sample_matrix_A::<Vector, Hasher>(
            &mut public_key.A,
            RANK,
            into_padded_array(seed_for_A),
            &mut seeds,
            true,
        );

        hax_lib::fstar!(
            r#"let (matrix_A_as_ntt, valid) = Spec.MLKEM.sample_matrix_A_ntt #$K $seed_for_A in
        assert (valid ==> matrix_A_as_ntt == Libcrux_ml_kem.Polynomial.to_spec_matrix_t public_key.f_A)"#
        );
        let prf_input: [u8; 33] = into_padded_array(seed_for_secret_and_error);
        hax_lib::fstar!(
            "Lib.Sequence.eq_intro #u8 #32 $seed_for_secret_and_error (Seq.slice $prf_input 0 32)"
        );

        let domain_separator = sample_vector_cbd_then_ntt::<Vector, Hasher>(
            &mut private_key.secret_as_ntt,
            prf_input,
            0,
        );
        let mut error_as_ntt = from_fn(|_i| PolynomialRingElement::<Vector>::ZERO());
        sample_vector_cbd_then_ntt_out::<Vector, Hasher>(
            prf_input,
            domain_separator,
            &mut error_as_ntt,
        );

        // tˆ := Aˆ ◦ sˆ + eˆ
        compute_As_plus_e(
            &mut public_key.t_as_ntt,
            &public_key.A,
            &private_key.secret_as_ntt,
            &error_as_ntt,
        );

        public_key.seed_for_A = seed_for_A.try_into().unwrap();

        hax_lib::fstar!(
            r#"let (((t_as_ntt,seed_for_A), matrix_A_as_ntt), secret_as_ntt), valid =
        Spec.MLKEM.ind_cpa_generate_keypair_unpacked $K $key_generation_seed in
        assert (valid ==>
            ((Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector ${public_key.t_as_ntt}) ==
              t_as_ntt) /\ (${public_key.seed_for_A} == seed_for_A) /\
            (Libcrux_ml_kem.Polynomial.to_spec_matrix_t #$K #$:Vector ${public_key.A} == matrix_A_as_ntt) /\
            ((Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector ${private_key.secret_as_ntt}) ==
              secret_as_ntt));
        assert ((forall (i: nat). i < v $K ==>
              Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index ${private_key.secret_as_ntt} i)) /\
          (forall (i: nat). i < v $K ==>
              Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index ${public_key.t_as_ntt} i)))"#
        );

        // For encapsulation, we need to store A not Aˆ, and so we untranspose A
        // However, we pass A_transpose here and let the IND-CCA layer do the untranspose.
        // We could do it here, but then we would pay the performance cost (if any) for the packed API as well.
    }

    #[allow(non_snake_case)]
    #[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
    $PRIVATE_KEY_SIZE == Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE $K /\
    $PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K /\
    $ETA1 == Spec.MLKEM.v_ETA1 $K /\
    $ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE $K /\
    length $key_generation_seed == Spec.MLKEM.v_CPA_KEY_GENERATION_SEED_SIZE"#))]
    #[hax_lib::ensures(|result| fstar!(r#"let (expected, valid) = Spec.MLKEM.ind_cpa_generate_keypair $K $key_generation_seed in 
                                    valid ==> $result == expected"#))]
    #[inline(always)]
    pub(crate) fn generate_keypair<
        Vector: Operations,
        Hasher: Hash,
        Scheme: Variant,
    >(
        key_generation_seed: &[u8],
        private_key: &mut [u8; CPA_PKE_SECRET_KEY_SIZE],
        public_key: &mut [u8; CPA_PKE_PUBLIC_KEY_SIZE],
    ) {
        let mut private_key_unpacked = IndCpaPrivateKeyUnpacked::default();
        let mut public_key_unpacked = IndCpaPublicKeyUnpacked::default();

        generate_keypair_unpacked::<Vector, Hasher, Scheme>(
            key_generation_seed,
            &mut private_key_unpacked,
            &mut public_key_unpacked,
        );

        serialize_unpacked_secret_key::<Vector>(
            &public_key_unpacked,
            &private_key_unpacked,
            public_key,
            private_key,
        );
    }

    /// Serialize the secret key from the unpacked key pair generation.
    #[hax_lib::fstar::verification_status(lax)]
    pub(crate) fn serialize_unpacked_secret_key<
        Vector: Operations,
    >(
        public_key: &IndCpaPublicKeyUnpacked<Vector>,
        private_key: &IndCpaPrivateKeyUnpacked<Vector>,
        public_key_out: &mut [u8; CPA_PKE_PUBLIC_KEY_SIZE],
        private_key_out: &mut [u8; CPA_PKE_SECRET_KEY_SIZE],
    ) {
        // pk := (Encode_12(tˆ mod^{+}q) || ρ)
        serialize_public_key_mut::<Vector>(
            &public_key.t_as_ntt,
            &public_key.seed_for_A,
            public_key_out,
        );

        // sk := Encode_12(sˆ mod^{+}q)
        serialize_vector(&private_key.secret_as_ntt, private_key_out);
    }

    /// Call [`compress_then_serialize_ring_element_u`] on each ring element.
    #[hax_lib::fstar::options("--z3rlimit 1500 --ext context_pruning --z3refresh")]
    #[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
    $OUT_LEN == Spec.MLKEM.v_C1_SIZE $K /\
    $COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_U_COMPRESSION_FACTOR $K /\
    $BLOCK_LEN == Spec.MLKEM.v_C1_BLOCK_SIZE $K /\
    ${out.len()} == $OUT_LEN /\
    (forall (i:nat). i < v $K ==>
        Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index $input i))"#))]
    #[hax_lib::ensures(|_|
    fstar!(r#"$out_future == Spec.MLKEM.compress_then_encode_u #$K
               (Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector $input)"#)
)]
    #[inline(always)]
    fn compress_then_serialize_u<
        const K: usize,
        const OUT_LEN: usize,
        const COMPRESSION_FACTOR: usize,
        const BLOCK_LEN: usize,
        Vector: Operations,
    >(
        input: [PolynomialRingElement<Vector>; K],
        out: &mut [u8],
    ) {
        hax_lib::fstar!(
            "assert (v (sz 32 *! $COMPRESSION_FACTOR) == 32 * v $COMPRESSION_FACTOR);
        assert (v ($OUT_LEN /! $K) == v $OUT_LEN / v $K);
        assert (v $OUT_LEN / v $K == 32 * v $COMPRESSION_FACTOR)"
        );
        cloop! {
            for (i, re) in input.into_iter().enumerate() {
                hax_lib::loop_invariant!(|i: usize| { fstar!(r#"(v $i < v $K ==> Seq.length out == v $OUT_LEN /\
                    Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index $input (v $i))) /\
            (forall (j: nat). j < v $i ==>
                Seq.length out == v $OUT_LEN /\
                    (j + 1) * (v $OUT_LEN / v $K) <= Seq.length out /\
                (Seq.slice out (j * (v $OUT_LEN / v $K)) (((j + 1)) * (v $OUT_LEN / v $K)) == 
                    Spec.MLKEM.compress_then_byte_encode (v $COMPRESSION_FACTOR)
                        (Libcrux_ml_kem.Polynomial.to_spec_poly_t #$:Vector (Seq.index $input j))))"#) });
                hax_lib::fstar!(r#"assert (forall (j: nat). j < v $i ==>
                ((Seq.slice out (j * (v $OUT_LEN / v $K)) (((j + 1)) * (v $OUT_LEN / v $K)) == 
                Spec.MLKEM.compress_then_byte_encode (v $COMPRESSION_FACTOR)
                    (Libcrux_ml_kem.Polynomial.to_spec_poly_t #$:Vector (Seq.index $input j)))))"#);
                out[i * (OUT_LEN / K)..(i + 1) * (OUT_LEN / K)].copy_from_slice(
                    &compress_then_serialize_ring_element_u::<COMPRESSION_FACTOR, BLOCK_LEN, Vector>(&re),
                );
                hax_lib::fstar!(r#"let lemma_aux (j: nat{ j < v $i }) : Lemma
                (Seq.slice out (j * (v $OUT_LEN / v $K)) (((j + 1)) * (v $OUT_LEN / v $K)) ==
                Spec.MLKEM.compress_then_byte_encode (v $COMPRESSION_FACTOR)
                    (Libcrux_ml_kem.Polynomial.to_spec_poly_t #v_Vector (Seq.index $input j))) =
                Lib.Sequence.eq_intro #u8 #(v $OUT_LEN / v $K) 
                (Seq.slice out (j * (v $OUT_LEN / v $K)) (((j + 1)) * (v $OUT_LEN / v $K)))
                (Spec.MLKEM.compress_then_byte_encode (v $COMPRESSION_FACTOR)
                    (Libcrux_ml_kem.Polynomial.to_spec_poly_t #$:Vector (Seq.index $input j)))
            in
            Classical.forall_intro lemma_aux"#);
            }
        };
        hax_lib::fstar!(
            "Lib.Sequence.eq_intro #u8 #(v $OUT_LEN) out
        (Spec.MLKEM.compress_then_encode_u #$K
            (Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector $input))"
        )
    }

    /// This function implements <strong>Algorithm 13</strong> of the
    /// NIST FIPS 203 specification; this is the Kyber CPA-PKE encryption algorithm.
    ///
    /// Algorithm 13 is reproduced below:
    ///
    /// ```plaintext
    /// Input: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
    /// Input: message m ∈ 𝔹^{32}.
    /// Input: encryption randomness r ∈ 𝔹^{32}.
    /// Output: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.
    ///
    /// N ← 0
    /// t̂ ← ByteDecode₁₂(ekₚₖₑ[0:384k])
    /// ρ ← ekₚₖₑ[384k: 384k + 32]
    /// for (i ← 0; i < k; i++)
    ///     for(j ← 0; j < k; j++)
    ///         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
    ///     end for
    /// end for
    /// for(i ← 0; i < k; i++)
    ///     r[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(r,N))
    ///     N ← N + 1
    /// end for
    /// for(i ← 0; i < k; i++)
    ///     e₁[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
    ///     N ← N + 1
    /// end for
    /// e₂ ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
    /// r̂ ← NTT(r)
    /// u ← NTT-¹(Âᵀ ◦ r̂) + e₁
    /// μ ← Decompress₁(ByteDecode₁(m)))
    /// v ← NTT-¹(t̂ᵀ ◦ rˆ) + e₂ + μ
    /// c₁ ← ByteEncode_{dᵤ}(Compress_{dᵤ}(u))
    /// c₂ ← ByteEncode_{dᵥ}(Compress_{dᵥ}(v))
    /// return c ← (c₁ ‖ c₂)
    /// ```
    ///
    /// The NIST FIPS 203 standard can be found at
    /// <https://csrc.nist.gov/pubs/fips/203/ipd>.
    #[allow(non_snake_case)]
    #[hax_lib::fstar::options("--z3rlimit 800 --ext context_pruning --z3refresh")]
    #[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
      $ETA1 == Spec.MLKEM.v_ETA1 $K /\
      $ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE $K /\
      $ETA2 == Spec.MLKEM.v_ETA2 $K /\
      $ETA2_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA2_RANDOMNESS_SIZE $K /\
      $C1_LEN == Spec.MLKEM.v_C1_SIZE $K /\
      $C2_LEN == Spec.MLKEM.v_C2_SIZE $K /\
      $U_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_U_COMPRESSION_FACTOR $K /\
      $V_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_V_COMPRESSION_FACTOR $K /\
      $BLOCK_LEN == Spec.MLKEM.v_C1_BLOCK_SIZE $K /\
      $CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE $K /\
      length $randomness == Spec.MLKEM.v_SHARED_SECRET_SIZE"#))]
    #[hax_lib::ensures(|result|
    fstar!(r#"$result == Spec.MLKEM.ind_cpa_encrypt_unpacked $K $message $randomness
        (Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector ${public_key.t_as_ntt})
        (Libcrux_ml_kem.Polynomial.to_spec_matrix_t #$K #$:Vector ${public_key.A})"#)
)]
    #[inline(always)]
    pub(crate) fn encrypt_unpacked<
        const K: usize,
        const CIPHERTEXT_SIZE: usize,
        const T_AS_NTT_ENCODED_SIZE: usize,
        const C1_LEN: usize,
        const C2_LEN: usize,
        const U_COMPRESSION_FACTOR: usize,
        const V_COMPRESSION_FACTOR: usize,
        const BLOCK_LEN: usize,
        const ETA1: usize,
        const ETA1_RANDOMNESS_SIZE: usize,
        const ETA2: usize,
        const ETA2_RANDOMNESS_SIZE: usize,
        Vector: Operations,
        Hasher: Hash<K>,
    >(
        public_key: &IndCpaPublicKeyUnpacked<K, Vector>,
        message: [u8; SHARED_SECRET_SIZE],
        randomness: &[u8],
    ) -> [u8; CIPHERTEXT_SIZE] {
        let mut ciphertext = [0u8; CIPHERTEXT_SIZE];

        let (r_as_ntt, error_2) = encrypt_c1::<
            K,
            C1_LEN,
            U_COMPRESSION_FACTOR,
            BLOCK_LEN,
            ETA1,
            ETA1_RANDOMNESS_SIZE,
            ETA2,
            ETA2_RANDOMNESS_SIZE,
            Vector,
            Hasher,
        >(randomness, &public_key.A, &mut ciphertext[0..C1_LEN]);

        encrypt_c2::<K, V_COMPRESSION_FACTOR, C2_LEN, Vector>(
            &public_key.t_as_ntt,
            &r_as_ntt,
            &error_2,
            message,
            &mut ciphertext[C1_LEN..],
        );

        ciphertext
    }

    #[inline(always)]
    pub(crate) fn encrypt_c1<
        const K: usize,
        const C1_LEN: usize,
        const U_COMPRESSION_FACTOR: usize,
        const BLOCK_LEN: usize,
        const ETA1: usize,
        const ETA1_RANDOMNESS_SIZE: usize,
        const ETA2: usize,
        const ETA2_RANDOMNESS_SIZE: usize,
        Vector: Operations,
        Hasher: Hash<K>,
    >(
        randomness: &[u8],
        matrix: &[[PolynomialRingElement<Vector>; K]; K],
        ciphertext: &mut [u8], // C1_LEN
    ) -> (
        [PolynomialRingElement<Vector>; K],
        PolynomialRingElement<Vector>,
    ) {
        // for i from 0 to k−1 do
        //     r[i] := CBD{η1}(PRF(r, N))
        //     N := N + 1
        // end for
        // rˆ := NTT(r)
        let mut prf_input: [u8; 33] = into_padded_array(randomness);
        let (r_as_ntt, domain_separator) =
            sample_vector_cbd_then_ntt_out::<K, ETA1, ETA1_RANDOMNESS_SIZE, Vector, Hasher>(
                prf_input, 0,
            );
        hax_lib::fstar!(
            "Lib.Sequence.eq_intro #u8 #32 $randomness (Seq.slice $prf_input 0 32);
        assert (v $domain_separator == v $K)"
        );

        // for i from 0 to k−1 do
        //     e1[i] := CBD_{η2}(PRF(r,N))
        //     N := N + 1
        // end for
        let mut error_1 = from_fn(|_i| PolynomialRingElement::<Vector>::ZERO());
        let domain_separator =
            sample_ring_element_cbd::<K, ETA2_RANDOMNESS_SIZE, ETA2, Vector, Hasher>(
                prf_input,
                domain_separator,
                &mut error_1,
            );

        // e_2 := CBD{η2}(PRF(r, N))
        prf_input[32] = domain_separator;
        hax_lib::fstar!(
        "assert (Seq.equal $prf_input (Seq.append $randomness (Seq.create 1 $domain_separator)));
        assert ($prf_input == Seq.append $randomness (Seq.create 1 $domain_separator))"
    );
        let mut prf_output = [0u8; ETA2_RANDOMNESS_SIZE];
        Hasher::PRF(&prf_input, &mut prf_output);
        let error_2 = sample_from_binomial_distribution::<ETA2, Vector>(&prf_output);

        // u := NTT^{-1}(AˆT ◦ rˆ) + e_1
        let u = compute_vector_u(matrix, &r_as_ntt, &error_1);

        // c_1 := Encode_{du}(Compress_q(u,d_u))
        compress_then_serialize_u::<K, C1_LEN, U_COMPRESSION_FACTOR, BLOCK_LEN, Vector>(
            u, ciphertext,
        );

        (r_as_ntt, error_2)
    }

    #[inline(always)]
    pub(crate) fn encrypt_c2<
        const K: usize,
        const V_COMPRESSION_FACTOR: usize,
        const C2_LEN: usize,
        Vector: Operations,
    >(
        t_as_ntt: &[PolynomialRingElement<Vector>; K],
        r_as_ntt: &[PolynomialRingElement<Vector>; K],
        error_2: &PolynomialRingElement<Vector>,
        message: [u8; SHARED_SECRET_SIZE],
        ciphertext: &mut [u8],
    ) {
        // v := NTT^{−1}(tˆT ◦ rˆ) + e_2 + Decompress_q(Decode_1(m),1)
        let message_as_ring_element = deserialize_then_decompress_message(message);
        let v = compute_ring_element_v(t_as_ntt, r_as_ntt, error_2, &message_as_ring_element);
        hax_lib::fstar!("assert ($C2_LEN = Spec.MLKEM.v_C2_SIZE v_K)");

        // c_2 := Encode_{dv}(Compress_q(v,d_v))
        compress_then_serialize_ring_element_v::<K, V_COMPRESSION_FACTOR, C2_LEN, Vector>(
            v, ciphertext,
        );
    }

    #[allow(non_snake_case)]
    #[hax_lib::fstar::options("--z3rlimit 500 --ext context_pruning")]
    #[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
    $ETA1 = Spec.MLKEM.v_ETA1 $K /\
    $ETA1_RANDOMNESS_SIZE = Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE $K /\
    $ETA2 = Spec.MLKEM.v_ETA2 $K /\
    $BLOCK_LEN == Spec.MLKEM.v_C1_BLOCK_SIZE $K /\
    $ETA2_RANDOMNESS_SIZE = Spec.MLKEM.v_ETA2_RANDOMNESS_SIZE $K /\
    $U_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_U_COMPRESSION_FACTOR $K /\
    $V_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_V_COMPRESSION_FACTOR $K /\
    length $public_key == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K /\
    length $randomness == Spec.MLKEM.v_SHARED_SECRET_SIZE /\
    $CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE $K /\
    $T_AS_NTT_ENCODED_SIZE == Spec.MLKEM.v_T_AS_NTT_ENCODED_SIZE $K /\
    $C1_LEN == Spec.MLKEM.v_C1_SIZE $K /\
    $C2_LEN == Spec.MLKEM.v_C2_SIZE $K"#))]
    #[hax_lib::ensures(|result|
    fstar!(r#"let (expected, valid) = Spec.MLKEM.ind_cpa_encrypt $K $public_key $message $randomness in
            valid ==> $result == expected"#)
)]
    #[inline(always)]
    pub(crate) fn encrypt<
        const K: usize,
        const CIPHERTEXT_SIZE: usize,
        const T_AS_NTT_ENCODED_SIZE: usize,
        const C1_LEN: usize,
        const C2_LEN: usize,
        const U_COMPRESSION_FACTOR: usize,
        const V_COMPRESSION_FACTOR: usize,
        const BLOCK_LEN: usize,
        const ETA1: usize,
        const ETA1_RANDOMNESS_SIZE: usize,
        const ETA2: usize,
        const ETA2_RANDOMNESS_SIZE: usize,
        Vector: Operations,
        Hasher: Hash<K>,
    >(
        public_key: &[u8],
        message: [u8; SHARED_SECRET_SIZE],
        randomness: &[u8],
    ) -> [u8; CIPHERTEXT_SIZE] {
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.MLKEM.ind_cpa_encrypt) Spec.MLKEM.ind_cpa_encrypt"#
        );
        let unpacked_public_key =
            build_unpacked_public_key::<K, T_AS_NTT_ENCODED_SIZE, Vector, Hasher>(public_key);

        // After unpacking the public key we can now call the unpacked decryption.
        encrypt_unpacked::<
            K,
            CIPHERTEXT_SIZE,
            T_AS_NTT_ENCODED_SIZE,
            C1_LEN,
            C2_LEN,
            U_COMPRESSION_FACTOR,
            V_COMPRESSION_FACTOR,
            BLOCK_LEN,
            ETA1,
            ETA1_RANDOMNESS_SIZE,
            ETA2,
            ETA2_RANDOMNESS_SIZE,
            Vector,
            Hasher,
        >(&unpacked_public_key, message, randomness)
    }

    #[inline(always)]
    #[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
    $T_AS_NTT_ENCODED_SIZE == Spec.MLKEM.v_T_AS_NTT_ENCODED_SIZE $K /\
    length $public_key == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K"#))]
    #[hax_lib::ensures(|result| fstar!(r#"
    let (t_as_ntt_bytes, seed_for_A) = split public_key $T_AS_NTT_ENCODED_SIZE in
    let t_as_ntt = Spec.MLKEM.vector_decode_12 #$K t_as_ntt_bytes in 
    let matrix_A_as_ntt, valid = Spec.MLKEM.sample_matrix_A_ntt #$K seed_for_A in
    (Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector ${result.t_as_ntt} == t_as_ntt /\
     valid ==> Libcrux_ml_kem.Polynomial.to_spec_matrix_t #$K #$:Vector ${result.A} == Spec.MLKEM.matrix_transpose matrix_A_as_ntt)"#))]
    fn build_unpacked_public_key<
        const K: usize,
        const T_AS_NTT_ENCODED_SIZE: usize,
        Vector: Operations,
        Hasher: Hash<K>,
    >(
        public_key: &[u8],
    ) -> IndCpaPublicKeyUnpacked<K, Vector> {
        let mut unpacked_public_key = IndCpaPublicKeyUnpacked::<K, Vector>::default();
        build_unpacked_public_key_mut::<K, T_AS_NTT_ENCODED_SIZE, Vector, Hasher>(
            public_key,
            &mut unpacked_public_key,
        );
        unpacked_public_key
    }

    #[inline(always)]
    #[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
    $T_AS_NTT_ENCODED_SIZE == Spec.MLKEM.v_T_AS_NTT_ENCODED_SIZE $K /\
    length $public_key == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K"#))]
    #[hax_lib::ensures(|_| {
    let unpacked_public_key_future = future(unpacked_public_key);
    {fstar!(r#"
    let (t_as_ntt_bytes, seed_for_A) = split public_key $T_AS_NTT_ENCODED_SIZE in
    let t_as_ntt = Spec.MLKEM.vector_decode_12 #$K t_as_ntt_bytes in 
    let matrix_A_as_ntt, valid = Spec.MLKEM.sample_matrix_A_ntt #$K seed_for_A in
    (Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector ${unpacked_public_key_future.t_as_ntt} == t_as_ntt /\
    valid ==> Libcrux_ml_kem.Polynomial.to_spec_matrix_t #$K #$:Vector ${unpacked_public_key_future.A} == Spec.MLKEM.matrix_transpose matrix_A_as_ntt)"#)}})]
    pub(crate) fn build_unpacked_public_key_mut<
        const K: usize,
        const T_AS_NTT_ENCODED_SIZE: usize,
        Vector: Operations,
        Hasher: Hash<K>,
    >(
        public_key: &[u8],
        unpacked_public_key: &mut IndCpaPublicKeyUnpacked<K, Vector>,
    ) {
        // tˆ := Decode_12(pk)
        deserialize_ring_elements_reduced::<K, Vector>(
            &public_key[..T_AS_NTT_ENCODED_SIZE],
            &mut unpacked_public_key.t_as_ntt,
        );

        // ρ := pk + 12·k·n / 8
        // for i from 0 to k−1 do
        //     for j from 0 to k − 1 do
        //         AˆT[i][j] := Parse(XOF(ρ, i, j))
        //     end for
        // end for
        let seed = &public_key[T_AS_NTT_ENCODED_SIZE..];
        hax_lib::fstar!(
            "Lib.Sequence.eq_intro #u8 #32 $seed
      (Seq.slice (Libcrux_ml_kem.Utils.into_padded_array (sz 34) $seed) 0 32)"
        );
        sample_matrix_A::<K, Vector, Hasher>(
            &mut unpacked_public_key.A,
            into_padded_array(seed),
            false,
        );
    }

    /// Call [`deserialize_then_decompress_ring_element_u`] on each ring element
    /// in the `ciphertext`.
    #[inline(always)]
    #[hax_lib::fstar::options("--z3rlimit 800 --ext context_pruning")]
    #[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
    $CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE $K /\
    $U_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_U_COMPRESSION_FACTOR $K"#))]
    #[hax_lib::ensures(|res|
    fstar!(r#"Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector $res ==
        Spec.MLKEM.(vector_ntt (decode_then_decompress_u #$K (Seq.slice $ciphertext 0 (v (Spec.MLKEM.v_C1_SIZE $K)))))"#)
)]
    fn deserialize_then_decompress_u<
        const K: usize,
        const CIPHERTEXT_SIZE: usize,
        const U_COMPRESSION_FACTOR: usize,
        Vector: Operations,
    >(
        ciphertext: &[u8; CIPHERTEXT_SIZE],
    ) -> [PolynomialRingElement<Vector>; K] {
        hax_lib::fstar!(
            "assert (v (($COEFFICIENTS_IN_RING_ELEMENT *! $U_COMPRESSION_FACTOR ) /!
        sz 8) == v (Spec.MLKEM.v_C1_BLOCK_SIZE $K))"
        );
        let mut u_as_ntt = from_fn(|_| PolynomialRingElement::<Vector>::ZERO());
        cloop! {
            for (i, u_bytes) in ciphertext
                .chunks_exact((COEFFICIENTS_IN_RING_ELEMENT * U_COMPRESSION_FACTOR) / 8)
                .enumerate()
            {
                hax_lib::loop_invariant!(|i: usize| { fstar!(r#"forall (j: nat). j < v $i ==>
                  j * v (Spec.MLKEM.v_C1_BLOCK_SIZE $K) + v (Spec.MLKEM.v_C1_BLOCK_SIZE $K) <= v $CIPHERTEXT_SIZE /\
              Libcrux_ml_kem.Polynomial.to_spec_poly_t #$:Vector (Seq.index $u_as_ntt j) ==
                Spec.MLKEM.poly_ntt (Spec.MLKEM.byte_decode_then_decompress (v $U_COMPRESSION_FACTOR)
                  (Seq.slice $ciphertext (j * v (Spec.MLKEM.v_C1_BLOCK_SIZE $K))
                    (j * v (Spec.MLKEM.v_C1_BLOCK_SIZE $K) + v (Spec.MLKEM.v_C1_BLOCK_SIZE $K))))"#) });
                u_as_ntt[i]  = deserialize_then_decompress_ring_element_u::<U_COMPRESSION_FACTOR, Vector>(u_bytes);
                ntt_vector_u::<U_COMPRESSION_FACTOR, Vector>(&mut u_as_ntt[i]);
            }
        }
        hax_lib::fstar!(
            "Lib.Sequence.eq_intro #Spec.MLKEM.polynomial #(v $K)
        (Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector $u_as_ntt)
        (Spec.MLKEM.(vector_ntt (decode_then_decompress_u #$K
        (Seq.slice $ciphertext 0 (v (Spec.MLKEM.v_C1_SIZE $K))))))"
        );
        u_as_ntt
    }

    /// Call [`deserialize_to_uncompressed_ring_element`] for each ring element.
    #[inline(always)]
    #[hax_lib::fstar::options("--z3rlimit 800 --ext context_pruning")]
    #[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
    length $secret_key == Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE $K /\
    v (${secret_key.len()}) / v $BYTES_PER_RING_ELEMENT <= v $K"#))]
    #[hax_lib::ensures(|res|
    fstar!(r#"Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector $res ==
         Spec.MLKEM.vector_decode_12 #$K $secret_key"#)
)]
    pub(crate) fn deserialize_vector<const K: usize, Vector: Operations>(
        secret_key: &[u8],
    ) -> [PolynomialRingElement<Vector>; K] {
        hax_lib::fstar!(r#"assert_norm (Spec.MLKEM.polynomial_d 12 == Spec.MLKEM.polynomial)"#);
        let mut secret_as_ntt = from_fn(|_| PolynomialRingElement::<Vector>::ZERO());
        for i in 0..K {
            hax_lib::loop_invariant!(|i: usize| {
                fstar!(
                    r#"forall (j: nat). j < v $i ==>
                j * v $BYTES_PER_RING_ELEMENT + v $BYTES_PER_RING_ELEMENT <=
                    v (Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE $K) /\
                Libcrux_ml_kem.Polynomial.to_spec_poly_t #$:Vector (Seq.index $secret_as_ntt j) ==
                    Spec.MLKEM.byte_decode 12 (Seq.slice $secret_key
                        (j * v $BYTES_PER_RING_ELEMENT)
                        (j * v $BYTES_PER_RING_ELEMENT + v $BYTES_PER_RING_ELEMENT))"#
                )
            });
            secret_as_ntt[i] = deserialize_to_uncompressed_ring_element(
                &secret_key[i * BYTES_PER_RING_ELEMENT..(i + 1) * BYTES_PER_RING_ELEMENT],
            );
        }
        hax_lib::fstar!(
            "Lib.Sequence.eq_intro #Spec.MLKEM.polynomial #(v $K)
        (Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector $secret_as_ntt)
        (Spec.MLKEM.vector_decode_12 #$K $secret_key)"
        );
        secret_as_ntt
    }

    /// This function implements <strong>Algorithm 14</strong> of the
    /// NIST FIPS 203 specification; this is the Kyber CPA-PKE decryption algorithm.
    ///
    /// Algorithm 14 is reproduced below:
    ///
    /// ```plaintext
    /// Input: decryption key dkₚₖₑ ∈ 𝔹^{384k}.
    /// Input: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.
    /// Output: message m ∈ 𝔹^{32}.
    ///
    /// c₁ ← c[0 : 32dᵤk]
    /// c₂ ← c[32dᵤk : 32(dᵤk + dᵥ)]
    /// u ← Decompress_{dᵤ}(ByteDecode_{dᵤ}(c₁))
    /// v ← Decompress_{dᵥ}(ByteDecode_{dᵥ}(c₂))
    /// ŝ ← ByteDecode₁₂(dkₚₖₑ)
    /// w ← v - NTT-¹(ŝᵀ ◦ NTT(u))
    /// m ← ByteEncode₁(Compress₁(w))
    /// return m
    /// ```
    ///
    /// The NIST FIPS 203 standard can be found at
    /// <https://csrc.nist.gov/pubs/fips/203/ipd>.
    #[allow(non_snake_case)]
    #[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
    $CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE $K /\
    $U_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_U_COMPRESSION_FACTOR $K /\
    $V_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_V_COMPRESSION_FACTOR $K /\
    $VECTOR_U_ENCODED_SIZE == Spec.MLKEM.v_C1_SIZE $K"#))]
    #[hax_lib::ensures(|result|
    fstar!(r#"$result == Spec.MLKEM.ind_cpa_decrypt_unpacked $K $ciphertext
        (Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector ${secret_key}.f_secret_as_ntt)"#)
)]
    #[inline(always)]
    pub(crate) fn decrypt_unpacked<
        const K: usize,
        const CIPHERTEXT_SIZE: usize,
        const VECTOR_U_ENCODED_SIZE: usize,
        const U_COMPRESSION_FACTOR: usize,
        const V_COMPRESSION_FACTOR: usize,
        Vector: Operations,
    >(
        secret_key: &IndCpaPrivateKeyUnpacked<K, Vector>,
        ciphertext: &[u8; CIPHERTEXT_SIZE],
    ) -> [u8; SHARED_SECRET_SIZE] {
        // u := Decompress_q(Decode_{d_u}(c), d_u)
        let u_as_ntt =
            deserialize_then_decompress_u::<K, CIPHERTEXT_SIZE, U_COMPRESSION_FACTOR, Vector>(
                ciphertext,
            );

        // v := Decompress_q(Decode_{d_v}(c + d_u·k·n / 8), d_v)
        let v = deserialize_then_decompress_ring_element_v::<K, V_COMPRESSION_FACTOR, Vector>(
            &ciphertext[VECTOR_U_ENCODED_SIZE..],
        );

        // m := Encode_1(Compress_q(v − NTT^{−1}(sˆT ◦ NTT(u)) , 1))
        let message = compute_message(&v, &secret_key.secret_as_ntt, &u_as_ntt);
        compress_then_serialize_message(message)
    }

    #[allow(non_snake_case)]
    #[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
    length $secret_key == Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE $K /\ 
    $CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE $K /\
    $VECTOR_U_ENCODED_SIZE == Spec.MLKEM.v_C1_SIZE $K /\
    $U_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_U_COMPRESSION_FACTOR $K /\
    $V_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_V_COMPRESSION_FACTOR $K"#))]
    #[hax_lib::ensures(|result|
    fstar!(r#"$result == Spec.MLKEM.ind_cpa_decrypt $K $secret_key $ciphertext"#)
)]
    #[inline(always)]
    pub(crate) fn decrypt<
        const K: usize,
        const CIPHERTEXT_SIZE: usize,
        const VECTOR_U_ENCODED_SIZE: usize,
        const U_COMPRESSION_FACTOR: usize,
        const V_COMPRESSION_FACTOR: usize,
        Vector: Operations,
    >(
        secret_key: &[u8],
        ciphertext: &[u8; CIPHERTEXT_SIZE],
    ) -> [u8; SHARED_SECRET_SIZE] {
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.MLKEM.ind_cpa_decrypt) Spec.MLKEM.ind_cpa_decrypt"#
        );
        // sˆ := Decode_12(sk)
        let secret_as_ntt = deserialize_vector::<K, Vector>(secret_key);
        let secret_key_unpacked = IndCpaPrivateKeyUnpacked { secret_as_ntt };

        decrypt_unpacked::<
            K,
            CIPHERTEXT_SIZE,
            VECTOR_U_ENCODED_SIZE,
            U_COMPRESSION_FACTOR,
            V_COMPRESSION_FACTOR,
            Vector,
        >(&secret_key_unpacked, ciphertext)
    }
}
