module Libcrux.Kem.Kyber.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_ZETAS_TIMES_MONTGOMERY_R: t_Array i32 (sz 128) =
  let list =
    [
      (-1044l); (-758l); (-359l); (-1517l); 1493l; 1422l; 287l; 202l; (-171l); 622l; 1577l; 182l;
      962l; (-1202l); (-1474l); 1468l; 573l; (-1325l); 264l; 383l; (-829l); 1458l; (-1602l); (-130l);
      (-681l); 1017l; 732l; 608l; (-1542l); 411l; (-205l); (-1571l); 1223l; 652l; (-552l); 1015l;
      (-1293l); 1491l; (-282l); (-1544l); 516l; (-8l); (-320l); (-666l); (-1618l); (-1162l); 126l;
      1469l; (-853l); (-90l); (-271l); 830l; 107l; (-1421l); (-247l); (-951l); (-398l); 961l;
      (-1508l); (-725l); 448l; (-1065l); 677l; (-1275l); (-1103l); 430l; 555l; 843l; (-1251l); 871l;
      1550l; 105l; 422l; 587l; 177l; (-235l); (-291l); (-460l); 1574l; 1653l; (-246l); 778l; 1159l;
      (-147l); (-777l); 1483l; (-602l); 1119l; (-1590l); 644l; (-872l); 349l; 418l; 329l; (-156l);
      (-75l); 817l; 1097l; 603l; 610l; 1322l; (-1285l); (-1465l); 384l; (-1215l); (-136l); 1218l;
      (-1335l); (-874l); 220l; (-1187l); (-1659l); (-1185l); (-1530l); (-1278l); 794l; (-1510l);
      (-854l); (-870l); 478l; (-108l); (-308l); 996l; 991l; 958l; (-1460l); 1522l; 1628l
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 128);
  Rust_primitives.Hax.array_of_list 128 list

/// Compute the product of two Kyber binomials with respect to the
/// modulus `X² - zeta`.
/// This function almost implements <strong>Algorithm 11</strong> of the
/// NIST FIPS 203 standard, which is reproduced below:
/// ```plaintext
/// Input:  a₀, a₁, b₀, b₁ ∈ ℤq.
/// Input: γ ∈ ℤq.
/// Output: c₀, c₁ ∈ ℤq.
/// c₀ ← a₀·b₀ + a₁·b₁·γ
/// c₁ ← a₀·b₁ + a₁·b₀
/// return c₀, c₁
/// ```
/// We say "almost" because the coefficients output by this function are in
/// the Montgomery domain (unlike in the specification).
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
val ntt_multiply_binomials: (i32 & i32) -> (i32 & i32) -> zeta: i32
  -> Prims.Pure (i32 & i32) Prims.l_True (fun _ -> Prims.l_True)

val invert_ntt_at_layer
      (zeta_i: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
      (layer: usize)
    : Prims.Pure (usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Use the Gentleman-Sande butterfly to invert, in-place, the NTT representation
/// of a `KyberPolynomialRingElement`. The coefficients of the output
/// ring element are in the Montgomery domain.
val invert_ntt_montgomery (v_K: usize) (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Represents an intermediate polynomial splitting step in the NTT. All
/// resulting coefficients are in the normal domain since the zetas have been
/// multiplied by MONTGOMERY_R.
val ntt_at_layer
      (zeta_i: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
      (layer v__initial_coefficient_bound: usize)
    : Prims.Pure (usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// See [`ntt_at_layer`].
val ntt_at_layer_3_
      (zeta_i: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
      (layer: usize)
    : Prims.Pure (usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// See [`ntt_at_layer`].
val ntt_at_layer_3328_
      (zeta_i: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
      (layer: usize)
    : Prims.Pure (usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Use the Cooley–Tukey butterfly to compute an in-place NTT representation
/// of a `KyberPolynomialRingElement`.
/// This function operates only on those which were produced by binomial
/// sampling, and thus those which have small coefficients. The small
/// coefficients let us skip the first round of Montgomery reductions.
val ntt_binomially_sampled_ring_element (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      (requires
        Hax_lib.v_forall #usize
          (fun i ->
              let i:usize = i in
              Hax_lib.implies (i <.
                  (Core.Slice.impl__len #i32
                      (Rust_primitives.unsize re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        <:
                        t_Slice i32)
                    <:
                    usize)
                  <:
                  bool)
                (fun temp_0_ ->
                    let _:Prims.unit = temp_0_ in
                    (Core.Num.impl__i32__abs (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ]
                          <:
                          i32)
                      <:
                      i32) <=.
                    3l
                    <:
                    bool)
              <:
              bool))
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
                        i32) <.
                      Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
                      <:
                      bool)
                <:
                bool))

/// Given two `KyberPolynomialRingElement`s in their NTT representations,
/// compute their product. Given two polynomials in the NTT domain `f^` and `ĵ`,
/// the `iᵗʰ` coefficient of the product `k\u{302}` is determined by the calculation:
/// ```plaintext
/// ĥ[2·i] + ĥ[2·i + 1]X = (f^[2·i] + f^[2·i + 1]X)·(ĝ[2·i] + ĝ[2·i + 1]X) mod (X² - ζ^(2·BitRev₇(i) + 1))
/// ```
/// This function almost implements <strong>Algorithm 10</strong> of the
/// NIST FIPS 203 standard, which is reproduced below:
/// ```plaintext
/// Input: Two arrays fˆ ∈ ℤ₂₅₆ and ĝ ∈ ℤ₂₅₆.
/// Output: An array ĥ ∈ ℤq.
/// for(i ← 0; i < 128; i++)
///     (ĥ[2i], ĥ[2i+1]) ← BaseCaseMultiply(fˆ[2i], fˆ[2i+1], ĝ[2i], ĝ[2i+1], ζ^(2·BitRev₇(i) + 1))
/// end for
/// return ĥ
/// ```
/// We say \"almost\" because the coefficients of the ring element output by
/// this function are in the Montgomery domain.
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
val ntt_multiply (lhs rhs: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      (requires
        Hax_lib.v_forall #usize
          (fun i ->
              let i:usize = i in
              Hax_lib.implies (i <. Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
                  <:
                  bool)
                (fun temp_0_ ->
                    let _:Prims.unit = temp_0_ in
                    ((lhs.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ] <: i32) >=. 0l <: bool) &&
                    ((lhs.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ] <: i32) <. 4096l <: bool
                    ) &&
                    ((Core.Num.impl__i32__abs (rhs.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ]
                            <:
                            i32)
                        <:
                        i32) <=.
                      Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
                      <:
                      bool))
              <:
              bool))
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
                      Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
                      <:
                      bool)
                <:
                bool))

/// Use the Cooley–Tukey butterfly to compute an in-place NTT representation
/// of a `KyberPolynomialRingElement`.
/// This function operates on the ring element that partly constitutes
/// the ciphertext.
val ntt_vector_u
      (v_VECTOR_U_COMPRESSION_FACTOR: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      (requires
        Hax_lib.v_forall #usize
          (fun i ->
              let i:usize = i in
              Hax_lib.implies (i <.
                  (Core.Slice.impl__len #i32
                      (Rust_primitives.unsize re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        <:
                        t_Slice i32)
                    <:
                    usize)
                  <:
                  bool)
                (fun temp_0_ ->
                    let _:Prims.unit = temp_0_ in
                    (Core.Num.impl__i32__abs (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ]
                          <:
                          i32)
                      <:
                      i32) <=.
                    3328l
                    <:
                    bool)
              <:
              bool))
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
                        i32) <.
                      Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
                      <:
                      bool)
                <:
                bool))
