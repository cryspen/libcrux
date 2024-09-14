module Libcrux_ml_kem.Ind_cpa
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Hash_functions in
  let open Libcrux_ml_kem.Vector.Traits in
  ()

/// Sample a vector of ring elements from a centered binomial distribution.
val sample_ring_element_cbd
      (v_K v_ETA2_RANDOMNESS_SIZE v_ETA2: usize)
      (#v_Vector #v_Hasher: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i3: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      (prf_input: t_Array u8 (sz 33))
      (domain_separator: u8)
    : Prims.Pure (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K & u8)
      (requires
        Spec.MLKEM.is_rank v_K /\ v_ETA2_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA2_RANDOMNESS_SIZE v_K /\
        v_ETA2 == Spec.MLKEM.v_ETA2 v_K /\ range (v domain_separator + v v_K) u8_inttype)
      (fun _ -> Prims.l_True)

/// Sample a vector of ring elements from a centered binomial distribution and
/// convert them into their NTT representations.
val sample_vector_cbd_then_ntt
      (v_K v_ETA v_ETA_RANDOMNESS_SIZE: usize)
      (#v_Vector #v_Hasher: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i3: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      (prf_input: t_Array u8 (sz 33))
      (domain_separator: u8)
    : Prims.Pure (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K & u8)
      (requires
        Spec.MLKEM.is_rank v_K /\ v_ETA_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE v_K /\
        v_ETA == Spec.MLKEM.v_ETA1 v_K /\ v domain_separator < 2 * v v_K /\
        range (v domain_separator + v v_K) u8_inttype)
      (ensures
        fun temp_0_ ->
          let x, ds:(t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K & u8)
          =
            temp_0_
          in
          v ds == v domain_separator + v v_K /\
          Libcrux_ml_kem.Polynomial.to_spec_vector_t #v_K #v_Vector x ==
          Spec.MLKEM.sample_vector_cbd_then_ntt #v_K
            (Seq.slice prf_input 0 32)
            (sz (v domain_separator)))

/// Call [`compress_then_serialize_ring_element_u`] on each ring element.
val compress_then_serialize_u
      (v_K v_OUT_LEN v_COMPRESSION_FACTOR v_BLOCK_LEN: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (input: t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        Spec.MLKEM.is_rank v_K /\ v_OUT_LEN == Spec.MLKEM.v_C1_SIZE v_K /\
        v_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_U_COMPRESSION_FACTOR v_K /\
        v_BLOCK_LEN == Spec.MLKEM.v_C1_BLOCK_SIZE v_K /\ Core.Slice.impl__len #u8 out == v_OUT_LEN)
      (ensures
        fun out_future ->
          let out_future:t_Slice u8 = out_future in
          out_future ==
          Spec.MLKEM.compress_then_encode_u #v_K
            (Libcrux_ml_kem.Polynomial.to_spec_vector_t #v_K #v_Vector input))

/// Call [`deserialize_then_decompress_ring_element_u`] on each ring element
/// in the `ciphertext`.
val deserialize_then_decompress_u
      (v_K v_CIPHERTEXT_SIZE v_U_COMPRESSION_FACTOR: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (ciphertext: t_Array u8 v_CIPHERTEXT_SIZE)
    : Prims.Pure (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (requires
        Spec.MLKEM.is_rank v_K /\ v_CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE v_K /\
        v_U_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_U_COMPRESSION_FACTOR v_K)
      (ensures
        fun res ->
          let res:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K = res in
          Libcrux_ml_kem.Polynomial.to_spec_vector_t #v_K #v_Vector res ==
          Spec.MLKEM.(vector_ntt (decode_then_decompress_u #v_K
                  (Seq.slice ciphertext 0 (v (Spec.MLKEM.v_C1_SIZE v_K))))))

/// Call [`deserialize_to_uncompressed_ring_element`] for each ring element.
val deserialize_secret_key
      (v_K: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (secret_key: t_Slice u8)
    : Prims.Pure (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (requires
        Spec.MLKEM.is_rank v_K /\ length secret_key == Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE v_K /\
        v (Core.Slice.impl__len #u8 secret_key) /
        v Libcrux_ml_kem.Constants.v_BYTES_PER_RING_ELEMENT <=
        v v_K)
      (ensures
        fun res ->
          let res:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K = res in
          Libcrux_ml_kem.Polynomial.to_spec_vector_t #v_K #v_Vector res ==
          Spec.MLKEM.vector_decode_12 #v_K secret_key)

/// Call [`serialize_uncompressed_ring_element`] for each ring element.
val serialize_secret_key
      (v_K v_OUT_LEN: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (key: t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
    : Prims.Pure (t_Array u8 v_OUT_LEN)
      (requires Spec.MLKEM.is_rank v_K /\ v_OUT_LEN == Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE v_K)
      (ensures
        fun res ->
          let res:t_Array u8 v_OUT_LEN = res in
          res ==
          Spec.MLKEM.vector_encode_12 #v_K
            (Libcrux_ml_kem.Polynomial.to_spec_vector_t #v_K #v_Vector key))

/// Concatenate `t` and `ρ` into the public key.
val serialize_public_key
      (v_K v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (tt_as_ntt: t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (seed_for_a: t_Slice u8)
    : Prims.Pure (t_Array u8 v_PUBLIC_KEY_SIZE)
      (requires
        Spec.MLKEM.is_rank v_K /\
        v_RANKED_BYTES_PER_RING_ELEMENT == Spec.MLKEM.v_RANKED_BYTES_PER_RING_ELEMENT v_K /\
        v_PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE v_K /\ length seed_for_a == sz 32)
      (ensures
        fun res ->
          let res:t_Array u8 v_PUBLIC_KEY_SIZE = res in
          res ==
          Seq.append (Spec.MLKEM.vector_encode_12 #v_K
                (Libcrux_ml_kem.Polynomial.to_spec_vector_t #v_K #v_Vector tt_as_ntt))
            seed_for_a)

/// This function implements <strong>Algorithm 14</strong> of the
/// NIST FIPS 203 specification; this is the Kyber CPA-PKE decryption algorithm.
/// Algorithm 14 is reproduced below:
/// ```plaintext
/// Input: decryption key dkₚₖₑ ∈ 𝔹^{384k}.
/// Input: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.
/// Output: message m ∈ 𝔹^{32}.
/// c₁ ← c[0 : 32dᵤk]
/// c₂ ← c[32dᵤk : 32(dᵤk + dᵥ)]
/// u ← Decompress_{dᵤ}(ByteDecode_{dᵤ}(c₁))
/// v ← Decompress_{dᵥ}(ByteDecode_{dᵥ}(c₂))
/// ŝ ← ByteDecode₁₂(dkₚₖₑ)
/// w ← v - NTT-¹(ŝᵀ ◦ NTT(u))
/// m ← ByteEncode₁(Compress₁(w))
/// return m
/// ```
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
val decrypt_unpacked
      (v_K v_CIPHERTEXT_SIZE v_VECTOR_U_ENCODED_SIZE v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR:
          usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (secret_key: Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector)
      (ciphertext: t_Array u8 v_CIPHERTEXT_SIZE)
    : Prims.Pure (t_Array u8 (sz 32))
      (requires
        Spec.MLKEM.is_rank v_K /\ v_CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE v_K /\
        v_U_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_U_COMPRESSION_FACTOR v_K /\
        v_V_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_V_COMPRESSION_FACTOR v_K /\
        v_VECTOR_U_ENCODED_SIZE == Spec.MLKEM.v_C1_SIZE v_K)
      (fun _ -> Prims.l_True)

val decrypt
      (v_K v_CIPHERTEXT_SIZE v_VECTOR_U_ENCODED_SIZE v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR:
          usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (secret_key: t_Slice u8)
      (ciphertext: t_Array u8 v_CIPHERTEXT_SIZE)
    : Prims.Pure (t_Array u8 (sz 32))
      (requires
        Spec.MLKEM.is_rank v_K /\ length secret_key == Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE v_K /\
        v_CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE v_K /\
        v_VECTOR_U_ENCODED_SIZE == Spec.MLKEM.v_C1_SIZE v_K /\
        v_U_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_U_COMPRESSION_FACTOR v_K /\
        v_V_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_V_COMPRESSION_FACTOR v_K)
      (ensures
        fun result ->
          let result:t_Array u8 (sz 32) = result in
          result == Spec.MLKEM.ind_cpa_decrypt v_K secret_key ciphertext)

/// This function implements <strong>Algorithm 13</strong> of the
/// NIST FIPS 203 specification; this is the Kyber CPA-PKE encryption algorithm.
/// Algorithm 13 is reproduced below:
/// ```plaintext
/// Input: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
/// Input: message m ∈ 𝔹^{32}.
/// Input: encryption randomness r ∈ 𝔹^{32}.
/// Output: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.
/// N ← 0
/// t\u{302} ← ByteDecode₁₂(ekₚₖₑ[0:384k])
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
/// r\u{302} ← NTT(r)
/// u ← NTT-¹(Âᵀ ◦ r\u{302}) + e₁
/// μ ← Decompress₁(ByteDecode₁(m)))
/// v ← NTT-¹(t\u{302}ᵀ ◦ rˆ) + e₂ + μ
/// c₁ ← ByteEncode_{dᵤ}(Compress_{dᵤ}(u))
/// c₂ ← ByteEncode_{dᵥ}(Compress_{dᵥ}(v))
/// return c ← (c₁ ‖ c₂)
/// ```
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
val encrypt_unpacked
      (v_K v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_LEN v_C2_LEN v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR v_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i3: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      (public_key: Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector)
      (message: t_Array u8 (sz 32))
      (randomness: t_Slice u8)
    : Prims.Pure (t_Array u8 v_CIPHERTEXT_SIZE)
      (requires
        Spec.MLKEM.is_rank v_K /\ v_ETA1 == Spec.MLKEM.v_ETA1 v_K /\
        v_ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE v_K /\
        v_ETA2 == Spec.MLKEM.v_ETA2 v_K /\
        v_ETA2_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA2_RANDOMNESS_SIZE v_K /\
        v_C1_LEN == Spec.MLKEM.v_C1_SIZE v_K /\ v_C2_LEN == Spec.MLKEM.v_C2_SIZE v_K /\
        v_U_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_U_COMPRESSION_FACTOR v_K /\
        v_V_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_V_COMPRESSION_FACTOR v_K /\
        v_BLOCK_LEN == Spec.MLKEM.v_C1_BLOCK_SIZE v_K /\
        v_CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE v_K /\
        length randomness == Spec.MLKEM.v_SHARED_SECRET_SIZE)
      (fun _ -> Prims.l_True)

val encrypt
      (v_K v_CIPHERTEXT_SIZE v_T_AS_NTT_ENCODED_SIZE v_C1_LEN v_C2_LEN v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR v_BLOCK_LEN v_ETA1 v_ETA1_RANDOMNESS_SIZE v_ETA2 v_ETA2_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i3: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      (public_key: t_Slice u8)
      (message: t_Array u8 (sz 32))
      (randomness: t_Slice u8)
    : Prims.Pure (t_Array u8 v_CIPHERTEXT_SIZE)
      (requires
        Spec.MLKEM.is_rank v_K /\ v_ETA1 = Spec.MLKEM.v_ETA1 v_K /\
        v_ETA1_RANDOMNESS_SIZE = Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE v_K /\
        v_ETA2 = Spec.MLKEM.v_ETA2 v_K /\ v_BLOCK_LEN == Spec.MLKEM.v_C1_BLOCK_SIZE v_K /\
        v_ETA2_RANDOMNESS_SIZE = Spec.MLKEM.v_ETA2_RANDOMNESS_SIZE v_K /\
        v_U_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_U_COMPRESSION_FACTOR v_K /\
        v_V_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_V_COMPRESSION_FACTOR v_K /\
        length public_key == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE v_K /\
        length randomness == Spec.MLKEM.v_SHARED_SECRET_SIZE /\
        v_CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE v_K /\
        v_T_AS_NTT_ENCODED_SIZE == Spec.MLKEM.v_T_AS_NTT_ENCODED_SIZE v_K /\
        v_C1_LEN == Spec.MLKEM.v_C1_SIZE v_K /\ v_C2_LEN == Spec.MLKEM.v_C2_SIZE v_K)
      (ensures
        fun result ->
          let result:t_Array u8 v_CIPHERTEXT_SIZE = result in
          let expected, valid = Spec.MLKEM.ind_cpa_encrypt v_K public_key message randomness in
          valid ==> result == expected)

/// This function implements most of <strong>Algorithm 12</strong> of the
/// NIST FIPS 203 specification; this is the Kyber CPA-PKE key generation algorithm.
/// We say \"most of\" since Algorithm 12 samples the required randomness within
/// the function itself, whereas this implementation expects it to be provided
/// through the `key_generation_seed` parameter.
/// Algorithm 12 is reproduced below:
/// ```plaintext
/// Output: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
/// Output: decryption key dkₚₖₑ ∈ 𝔹^{384k}.
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
/// t\u{302} ← Â◦ŝ + ê
/// ekₚₖₑ ← ByteEncode₁₂(t\u{302}) ‖ ρ
/// dkₚₖₑ ← ByteEncode₁₂(ŝ)
/// ```
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
val generate_keypair_unpacked
      (v_K v_ETA1 v_ETA1_RANDOMNESS_SIZE: usize)
      (#v_Vector #v_Hasher: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i3: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      (key_generation_seed: t_Slice u8)
    : Prims.Pure
      (Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPrivateKeyUnpacked v_K v_Vector &
        Libcrux_ml_kem.Ind_cpa.Unpacked.t_IndCpaPublicKeyUnpacked v_K v_Vector)
      (requires
        Spec.MLKEM.is_rank v_K /\ v_ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE v_K /\
        v_ETA1 == Spec.MLKEM.v_ETA1 v_K)
      (fun _ -> Prims.l_True)

val generate_keypair
      (v_K v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_RANKED_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i3: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      (key_generation_seed: t_Slice u8)
    : Prims.Pure (t_Array u8 v_PRIVATE_KEY_SIZE & t_Array u8 v_PUBLIC_KEY_SIZE)
      (requires
        Spec.MLKEM.is_rank v_K /\ v_PRIVATE_KEY_SIZE == Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE v_K /\
        v_PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE v_K /\
        v_RANKED_BYTES_PER_RING_ELEMENT == Spec.MLKEM.v_RANKED_BYTES_PER_RING_ELEMENT v_K /\
        v_ETA1 == Spec.MLKEM.v_ETA1 v_K /\
        v_ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE v_K /\
        length key_generation_seed == Spec.MLKEM.v_CPA_KEY_GENERATION_SEED_SIZE)
      (ensures
        fun result ->
          let result:(t_Array u8 v_PRIVATE_KEY_SIZE & t_Array u8 v_PUBLIC_KEY_SIZE) = result in
          let expected, valid = Spec.MLKEM.ind_cpa_generate_keypair v_K key_generation_seed in
          valid ==> result == expected)
