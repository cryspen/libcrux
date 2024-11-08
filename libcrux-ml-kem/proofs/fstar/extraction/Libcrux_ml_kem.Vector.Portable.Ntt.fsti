module Libcrux_ml_kem.Vector.Portable.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

[@@ "opaque_to_smt"]

val inv_ntt_step
      (vec: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta: i16)
      (i j: usize)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires
        v i < 16 /\ v j < 16 /\ v i <> v j /\ Spec.Utils.is_i16b 1664 zeta /\
        Spec.Utils.is_i16b_array (4 * 3328) vec.f_elements)
      (ensures
        fun vec_future ->
          let vec_future:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec_future in
          Spec.Utils.is_i16b_array (4 * 3328) vec_future.f_elements /\
          (forall k.
              (k <> v i /\ k <> v j) ==>
              Seq.index vec_future.f_elements k == Seq.index vec.f_elements k) /\
          Spec.Utils.is_i16b 3328 (Seq.index vec_future.f_elements (v i)) /\
          Spec.Utils.is_i16b 3328 (Seq.index vec_future.f_elements (v j)) /\
          Spec.Utils.inv_ntt_spec vec.f_elements (v zeta) (v i) (v j) vec_future.f_elements)

val inv_ntt_layer_1_step
      (vec: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta0 zeta1 zeta2 zeta3: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires
        Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
        Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
        Spec.Utils.is_i16b_array (4 * 3328) vec.f_elements)
      (ensures
        fun result ->
          let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = result in
          Spec.Utils.is_i16b_array 3328 result.f_elements)

val inv_ntt_layer_2_step
      (vec: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta0 zeta1: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires
        Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
        Spec.Utils.is_i16b_array 3328 vec.f_elements)
      (ensures
        fun result ->
          let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = result in
          Spec.Utils.is_i16b_array 3328 result.f_elements)

val inv_ntt_layer_3_step
      (vec: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires Spec.Utils.is_i16b 1664 zeta /\ Spec.Utils.is_i16b_array 3328 vec.f_elements)
      (ensures
        fun result ->
          let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = result in
          Spec.Utils.is_i16b_array 3328 result.f_elements)

[@@ "opaque_to_smt"]

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
/// We say \"almost\" because the coefficients output by this function are in
/// the Montgomery domain (unlike in the specification).
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
val ntt_multiply_binomials
      (a b: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta: i16)
      (i: usize)
      (out: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires
        v i < 8 /\ Spec.Utils.is_i16b 1664 zeta /\ Spec.Utils.is_i16b_array 3328 a.f_elements /\
        Spec.Utils.is_i16b_array 3328 b.f_elements /\ Spec.Utils.is_i16b_array 3328 out.f_elements)
      (ensures
        fun out_future ->
          let out_future:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = out_future in
          Spec.Utils.is_i16b_array 3328 out_future.f_elements /\
          (forall k.
              (k <> 2 * v i /\ k <> 2 * v i + 1) ==>
              Seq.index out_future.f_elements k == Seq.index out.f_elements k) /\
          (let ai = Seq.index a.f_elements (2 * v i) in
            let aj = Seq.index a.f_elements (2 * v i + 1) in
            let bi = Seq.index b.f_elements (2 * v i) in
            let bj = Seq.index b.f_elements (2 * v i + 1) in
            let oi = Seq.index out_future.f_elements (2 * v i) in
            let oj = Seq.index out_future.f_elements (2 * v i + 1) in
            ((v oi % 3329) == (((v ai * v bi + (v aj * v bj * v zeta * 169)) * 169) % 3329)) /\
            ((v oj % 3329) == (((v ai * v bj + v aj * v bi) * 169) % 3329))))

[@@ "opaque_to_smt"]

val ntt_step
      (vec: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta: i16)
      (i j: usize)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires
        v i < 16 /\ v j < 16 /\ v i <> v j /\ Spec.Utils.is_i16b 1664 zeta /\
        Spec.Utils.is_i16b_array (11207 + 6 * 3328) vec.f_elements /\
        Spec.Utils.is_i16b (11207 + 5 * 3328) vec.f_elements.[ i ] /\
        Spec.Utils.is_i16b (11207 + 5 * 3328) vec.f_elements.[ j ])
      (ensures
        fun vec_future ->
          let vec_future:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = vec_future in
          (forall k.
              (k <> v i /\ k <> v j) ==>
              Seq.index vec_future.f_elements k == Seq.index vec.f_elements k) /\
          (forall b.
              (Spec.Utils.is_i16b b vec.f_elements.[ i ] /\
                Spec.Utils.is_i16b b vec.f_elements.[ j ]) ==>
              (Spec.Utils.is_i16b (b + 3328) vec_future.f_elements.[ i ] /\
                Spec.Utils.is_i16b (b + 3328) vec_future.f_elements.[ j ])) /\
          Spec.Utils.ntt_spec vec.f_elements (v zeta) (v i) (v j) vec_future.f_elements)

val ntt_layer_1_step
      (vec: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta0 zeta1 zeta2 zeta3: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires
        Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
        Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
        Spec.Utils.is_i16b_array (11207 + 5 * 3328) vec.f_elements)
      (ensures
        fun result ->
          let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = result in
          Spec.Utils.is_i16b_array (11207 + 6 * 3328) result.f_elements)

val ntt_layer_2_step
      (vec: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta0 zeta1: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires
        Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
        Spec.Utils.is_i16b_array (11207 + 4 * 3328) vec.f_elements)
      (ensures
        fun result ->
          let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = result in
          Spec.Utils.is_i16b_array (11207 + 5 * 3328) result.f_elements)

val ntt_layer_3_step (vec: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector) (zeta: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires
        Spec.Utils.is_i16b 1664 zeta /\ Spec.Utils.is_i16b_array (11207 + 3 * 3328) vec.f_elements)
      (ensures
        fun result ->
          let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = result in
          Spec.Utils.is_i16b_array (11207 + 4 * 3328) result.f_elements)

val ntt_multiply
      (lhs rhs: Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector)
      (zeta0 zeta1 zeta2 zeta3: i16)
    : Prims.Pure Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
      (requires
        Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
        Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
        Spec.Utils.is_i16b_array 3328 lhs.f_elements /\ Spec.Utils.is_i16b_array 3328 rhs.f_elements
      )
      (ensures
        fun result ->
          let result:Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector = result in
          Spec.Utils.is_i16b_array 3328 result.f_elements /\
          (let zetas =
              Seq.seq_of_list [
                  v zeta0;
                  - v zeta0;
                  v zeta1;
                  - v zeta1;
                  v zeta2;
                  - v zeta2;
                  v zeta3;
                  - v zeta3
                ]
            in
            (forall (i: nat).
                i < 8 ==>
                (let ai = Seq.index lhs.f_elements (2 * i) in
                  let aj = Seq.index lhs.f_elements (2 * i + 1) in
                  let bi = Seq.index rhs.f_elements (2 * i) in
                  let bj = Seq.index rhs.f_elements (2 * i + 1) in
                  let oi = Seq.index result.f_elements (2 * i) in
                  let oj = Seq.index result.f_elements (2 * i + 1) in
                  ((v oi % 3329) ==
                    (((v ai * v bi + (v aj * v bj * (Seq.index zetas i) * 169)) * 169) % 3329)) /\
                  ((v oj % 3329) == (((v ai * v bj + v aj * v bi) * 169) % 3329))))))
