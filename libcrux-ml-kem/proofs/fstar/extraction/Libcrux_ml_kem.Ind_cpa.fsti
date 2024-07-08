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
      (#v_K #v_ETA2_RANDOMNESS_SIZE #v_ETA2: usize)
      (#v_Vector #v_Hasher: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i3: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      (prf_input: t_Array u8 (sz 33))
      (domain_separator: u8)
    : Prims.Pure (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K & u8)
      (requires
        ((Rust_primitives.Hax.Int.from_machine domain_separator <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine v_K <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine 255l <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True)

/// Sample a vector of ring elements from a centered binomial distribution and
/// convert them into their NTT representations.
val sample_vector_cbd_then_ntt
      (#v_K #v_ETA #v_ETA_RANDOMNESS_SIZE: usize)
      (#v_Vector #v_Hasher: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i3: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      (prf_input: t_Array u8 (sz 33))
      (domain_separator: u8)
    : Prims.Pure (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K & u8)
      (requires
        ((Rust_primitives.Hax.Int.from_machine domain_separator <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine v_K <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine 255l <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True)

/// Call [`compress_then_serialize_ring_element_u`] on each ring element.
val compress_then_serialize_u
      (#v_K #v_OUT_LEN #v_COMPRESSION_FACTOR #v_BLOCK_LEN: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (input: t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (out: t_Slice u8)
    : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

/// Call [`deserialize_then_decompress_ring_element_u`] on each ring element
/// in the `ciphertext`.
val deserialize_then_decompress_u
      (#v_K #v_CIPHERTEXT_SIZE #v_U_COMPRESSION_FACTOR: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (ciphertext: t_Array u8 v_CIPHERTEXT_SIZE)
    : Prims.Pure (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (requires
        ((Rust_primitives.Hax.Int.from_machine Libcrux_ml_kem.Constants.v_COEFFICIENTS_IN_RING_ELEMENT

            <:
            Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine v_U_COMPRESSION_FACTOR <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core.Num.impl__usize__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True)

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
val encrypt
      (#v_K #v_CIPHERTEXT_SIZE #v_T_AS_NTT_ENCODED_SIZE #v_C1_LEN #v_C2_LEN #v_U_COMPRESSION_FACTOR #v_V_COMPRESSION_FACTOR #v_BLOCK_LEN #v_ETA1 #v_ETA1_RANDOMNESS_SIZE #v_ETA2 #v_ETA2_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i3: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      (public_key: t_Slice u8)
      (message: t_Array u8 (sz 32))
      (randomness: t_Slice u8)
    : Prims.Pure (t_Array u8 v_CIPHERTEXT_SIZE)
      (requires
        v_T_AS_NTT_ENCODED_SIZE <. (Core.Slice.impl__len #u8 public_key <: usize) && v_K <=. sz 255 &&
        v_C1_LEN <. v_CIPHERTEXT_SIZE)
      (fun _ -> Prims.l_True)

/// Call [`deserialize_to_uncompressed_ring_element`] for each ring element.
val deserialize_secret_key
      (#v_K: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (secret_key: t_Slice u8)
    : Prims.Pure (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
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
val decrypt
      (#v_K #v_CIPHERTEXT_SIZE #v_VECTOR_U_ENCODED_SIZE #v_U_COMPRESSION_FACTOR #v_V_COMPRESSION_FACTOR:
          usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (secret_key: t_Slice u8)
      (ciphertext: t_Array u8 v_CIPHERTEXT_SIZE)
    : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True (fun _ -> Prims.l_True)

/// Call [`serialize_uncompressed_ring_element`] for each ring element.
val serialize_secret_key
      (#v_K #v_OUT_LEN: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (key: t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
    : Prims.Pure (t_Array u8 v_OUT_LEN) Prims.l_True (fun _ -> Prims.l_True)

/// Concatenate `t` and `ρ` into the public key.
val serialize_public_key
      (#v_K #v_RANKED_BYTES_PER_RING_ELEMENT #v_PUBLIC_KEY_SIZE: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (tt_as_ntt: t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (seed_for_a: t_Slice u8)
    : Prims.Pure (t_Array u8 v_PUBLIC_KEY_SIZE)
      (requires
        v_RANKED_BYTES_PER_RING_ELEMENT <=. v_PUBLIC_KEY_SIZE &&
        (Core.Slice.impl__len #u8 seed_for_a <: usize) =.
        (v_PUBLIC_KEY_SIZE -! v_RANKED_BYTES_PER_RING_ELEMENT <: usize))
      (fun _ -> Prims.l_True)

/// This function implements most of <strong>Algorithm 12</strong> of the
/// NIST FIPS 203 specification; this is the Kyber CPA-PKE key generation algorithm.
/// We say "most of" since Algorithm 12 samples the required randomness within
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
/// t̂ ← Â◦ŝ + ê
/// ekₚₖₑ ← ByteEncode₁₂(t̂) ‖ ρ
/// dkₚₖₑ ← ByteEncode₁₂(ŝ)
/// ```
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
val generate_keypair
      (#v_K #v_PRIVATE_KEY_SIZE #v_PUBLIC_KEY_SIZE #v_RANKED_BYTES_PER_RING_ELEMENT #v_ETA1 #v_ETA1_RANDOMNESS_SIZE:
          usize)
      (#v_Vector #v_Hasher: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i3: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      (key_generation_seed: t_Slice u8)
    : Prims.Pure (t_Array u8 v_PRIVATE_KEY_SIZE & t_Array u8 v_PUBLIC_KEY_SIZE)
      Prims.l_True
      (fun _ -> Prims.l_True)
