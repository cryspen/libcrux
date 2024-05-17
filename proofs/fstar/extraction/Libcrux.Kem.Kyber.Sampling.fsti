module Libcrux.Kem.Kyber.Sampling
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// Given a series of uniformly random bytes in `randomness`, for some number `eta`,
/// the `sample_from_binomial_distribution_{eta}` functions sample
/// a ring element from a binomial distribution centered at 0 that uses two sets
/// of `eta` coin flips. If, for example,
/// `eta = ETA`, each ring coefficient is a value `v` such
/// such that `v ∈ {-ETA, -ETA + 1, ..., 0, ..., ETA + 1, ETA}` and:
/// ```plaintext
/// - If v < 0, Pr[v] = Pr[-v]
/// - If v >= 0, Pr[v] = BINOMIAL_COEFFICIENT(2 * ETA; ETA - v) / 2 ^ (2 * ETA)
/// ```
/// The values `v < 0` are mapped to the appropriate `KyberFieldElement`.
/// The expected value is:
/// ```plaintext
/// E[X] = (-ETA)Pr[-ETA] + (-(ETA - 1))Pr[-(ETA - 1)] + ... + (ETA - 1)Pr[ETA - 1] + (ETA)Pr[ETA]
///      = 0 since Pr[-v] = Pr[v] when v < 0.
/// ```
/// And the variance is:
/// ```plaintext
/// Var(X) = E[(X - E[X])^2]
///        = E[X^2]
///        = sum_(v=-ETA to ETA)v^2 * (BINOMIAL_COEFFICIENT(2 * ETA; ETA - v) / 2^(2 * ETA))
///        = ETA / 2
/// ```
/// This function implements <strong>Algorithm 7</strong> of the NIST FIPS 203 standard, which is
/// reproduced below:
/// ```plaintext
/// Input: byte array B ∈ 𝔹^{64η}.
/// Output: array f ∈ ℤ₂₅₆.
/// b ← BytesToBits(B)
/// for (i ← 0; i < 256; i++)
///     x ← ∑(j=0 to η - 1) b[2iη + j]
///     y ← ∑(j=0 to η - 1) b[2iη + η + j]
///     f[i] ← x−y mod q
/// end for
/// return f
/// ```
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
val sample_from_binomial_distribution_2_ (randomness: t_Slice u8)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      (requires (Core.Slice.impl__len #u8 randomness <: usize) =. (sz 2 *! sz 64 <: usize))
      (ensures
        fun result ->
          let result:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = result in
          Hax_lib.v_forall #usize
            (fun i ->
                let i:usize = i in
                Hax_lib.implies (i <.
                    (Core.Slice.impl__len #i32
                        (Rust_primitives.unsize result.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                          <:
                          t_Slice i32)
                      <:
                      usize)
                    <:
                    bool)
                  (fun temp_0_ ->
                      let _:Prims.unit = temp_0_ in
                      (Core.Num.impl__i32__abs (result.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[
                              i ]
                            <:
                            i32)
                        <:
                        i32) <=.
                      2l
                      <:
                      bool)
                <:
                bool))

val sample_from_binomial_distribution_3_ (randomness: t_Slice u8)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      (requires (Core.Slice.impl__len #u8 randomness <: usize) =. (sz 3 *! sz 64 <: usize))
      (ensures
        fun result ->
          let result:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = result in
          Hax_lib.v_forall #usize
            (fun i ->
                let i:usize = i in
                Hax_lib.implies (i <.
                    (Core.Slice.impl__len #i32
                        (Rust_primitives.unsize result.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                          <:
                          t_Slice i32)
                      <:
                      usize)
                    <:
                    bool)
                  (fun temp_0_ ->
                      let _:Prims.unit = temp_0_ in
                      (Core.Num.impl__i32__abs (result.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[
                              i ]
                            <:
                            i32)
                        <:
                        i32) <=.
                      3l
                      <:
                      bool)
                <:
                bool))

val sample_from_binomial_distribution (v_ETA: usize) (randomness: t_Slice u8)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

/// If `bytes` contains a set of uniformly random bytes, this function
/// uniformly samples a ring element `â` that is treated as being the NTT representation
/// of the corresponding polynomial `a`.
/// Since rejection sampling is used, it is possible the supplied bytes are
/// not enough to sample the element, in which case an `Err` is returned and the
/// caller must try again with a fresh set of bytes.
/// This function <strong>partially</strong> implements <strong>Algorithm 6</strong> of the NIST FIPS 203 standard,
/// We say "partially" because this implementation only accepts a finite set of
/// bytes as input and returns an error if the set is not enough; Algorithm 6 of
/// the FIPS 203 standard on the other hand samples from an infinite stream of bytes
/// until the ring element is filled. Algorithm 6 is reproduced below:
/// ```plaintext
/// Input: byte stream B ∈ 𝔹*.
/// Output: array â ∈ ℤ₂₅₆.
/// i ← 0
/// j ← 0
/// while j < 256 do
///     d₁ ← B[i] + 256·(B[i+1] mod 16)
///     d₂ ← ⌊B[i+1]/16⌋ + 16·B[i+2]
///     if d₁ < q then
///         â[j] ← d₁
///         j ← j + 1
///     end if
///     if d₂ < q and j < 256 then
///         â[j] ← d₂
///         j ← j + 1
///     end if
///     i ← i + 3
/// end while
/// return â
/// ```
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
val sample_from_uniform_distribution_next
      (v_K v_N: usize)
      (randomness: t_Array (t_Array u8 v_N) v_K)
      (sampled_coefficients: t_Array usize v_K)
      (out: t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
    : Prims.Pure
      (t_Array usize v_K & t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K & bool)
      Prims.l_True
      (fun _ -> Prims.l_True)

val sample_from_xof (v_K: usize) (seeds: t_Array (t_Array u8 (sz 34)) v_K)
    : Prims.Pure (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
      Prims.l_True
      (fun _ -> Prims.l_True)
