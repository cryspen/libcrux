module Libcrux_ml_kem.Ind_cpa
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Hash_functions in
  let open Libcrux_ml_kem.Variant in
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
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Sample a vector of ring elements from a centered binomial distribution and
/// convert them into their NTT representations.
val sample_vector_cbd_then_ntt
      (v_K v_ETA v_ETA_RANDOMNESS_SIZE: usize)
      (#v_Vector #v_Hasher: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i3: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      (re_as_ntt: t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (prf_input: t_Array u8 (sz 33))
      (domain_separator: u8)
    : Prims.Pure (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K & u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val sample_vector_cbd_then_ntt_out
      (v_K v_ETA v_ETA_RANDOMNESS_SIZE: usize)
      (#v_Vector #v_Hasher: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i3: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      (prf_input: t_Array u8 (sz 33))
      (domain_separator: u8)
    : Prims.Pure (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K & u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Call [`compress_then_serialize_ring_element_u`] on each ring element.
val compress_then_serialize_u
      (v_K v_OUT_LEN v_COMPRESSION_FACTOR v_BLOCK_LEN: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (input: t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (out: t_Slice u8)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

/// Call [`deserialize_then_decompress_ring_element_u`] on each ring element
/// in the `ciphertext`.
val deserialize_then_decompress_u
      (v_K v_CIPHERTEXT_SIZE v_U_COMPRESSION_FACTOR: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (ciphertext: t_Array u8 v_CIPHERTEXT_SIZE)
    : Prims.Pure (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      Prims.l_True
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
    : Prims.Pure (t_Array u8 v_CIPHERTEXT_SIZE) Prims.l_True (fun _ -> Prims.l_True)

/// Call [`deserialize_to_uncompressed_ring_element`] for each ring element.
val deserialize_secret_key
      (v_K: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (secret_key: t_Slice u8)
    : Prims.Pure (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Call [`serialize_uncompressed_ring_element`] for each ring element.
val serialize_secret_key
      (v_K v_OUT_LEN: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (key: t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
    : Prims.Pure (t_Array u8 v_OUT_LEN) Prims.l_True (fun _ -> Prims.l_True)

/// Concatenate `t` and `ρ` into the public key.
val serialize_public_key
      (v_K v_RANKED_BYTES_PER_RING_ELEMENT v_PUBLIC_KEY_SIZE: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (tt_as_ntt: t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (seed_for_a: t_Slice u8)
    : Prims.Pure (t_Array u8 v_PUBLIC_KEY_SIZE) Prims.l_True (fun _ -> Prims.l_True)

val generate_keypair
      (v_K v_PRIVATE_KEY_SIZE v_PUBLIC_KEY_SIZE v_RANKED_BYTES_PER_RING_ELEMENT v_ETA1 v_ETA1_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher #v_Scheme: Type0)
      {| i3: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i4: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      {| i5: Libcrux_ml_kem.Variant.t_Variant v_Scheme |}
      (key_generation_seed: t_Slice u8)
    : Prims.Pure (t_Array u8 v_PRIVATE_KEY_SIZE & t_Array u8 v_PUBLIC_KEY_SIZE)
      Prims.l_True
      (fun _ -> Prims.l_True)

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
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

val decrypt
      (v_K v_CIPHERTEXT_SIZE v_VECTOR_U_ENCODED_SIZE v_U_COMPRESSION_FACTOR v_V_COMPRESSION_FACTOR:
          usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (secret_key: t_Slice u8)
      (ciphertext: t_Array u8 v_CIPHERTEXT_SIZE)
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)
