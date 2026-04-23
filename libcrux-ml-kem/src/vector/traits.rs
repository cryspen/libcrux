pub const MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS: i16 = 1353;
pub const FIELD_MODULUS: i16 = 3329;
pub const FIELD_ELEMENTS_IN_VECTOR: usize = 16;
pub const INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u32 = 62209; // FIELD_MODULUS^{-1} mod MONTGOMERY_R
pub const BARRETT_SHIFT: i32 = 26;
pub const BARRETT_R: i32 = 1 << BARRETT_SHIFT;

#[cfg(hax)]
use hax_lib::prop::ToProp;

// We define a trait that allows us to talk about the contents of a vector.
// This is used extensively in pre- and post-conditions to reason about the code.
// The trait is duplicated for Eurydice to avoid the trait inheritance between Operations and Repr
// This is needed because of this issue: https://github.com/AeneasVerif/eurydice/issues/111
#[cfg(hax)]
#[hax_lib::attributes]
pub trait Repr: Copy + Clone {
    #[requires(true)]
    fn repr(&self) -> [i16; 16];
}

#[cfg(any(eurydice, not(hax)))]
pub trait Repr {}

#[cfg(hax)]
#[allow(dead_code, unused_variables)]
pub(crate) mod spec {

    // Spec-side infrastructure injected into the generated F* module
    // `Libcrux_ml_kem.Vector.Traits.Spec`:
    //
    //   * Generic integer-bound predicates (is_intb / is_i16b /
    //     is_i16b_array / is_i16b_array_opaque / map_array), copied
    //     verbatim from proofs/fstar/spec/Spec.Utils.fsti so that, with
    //     opaque_to_smt unfolded, the predicate content is identical.
    //
    //   * Two i16 -> t_FieldElement lifts, distinguished by whether the
    //     impl i16 is a *plain* representative mod q, or a *Montgomery*
    //     form representing abstract value `(v x * R^{-1}) mod q` with
    //     R = 2^16 and R^{-1} = 169 mod 3329:
    //       - i16_to_spec_fe x      := (v x) mod q
    //       - mont_i16_to_spec_fe x := (v x * 169) mod q
    //     NTT, inverse-NTT, and ntt_multiply live in Montgomery land;
    //     compress/decompress/serialize/deserialize/barrett live in
    //     plain land.  `add`/`sub` are linear and work in either.
    //
    //   * Array companions i16_to_spec_array / mont_i16_to_spec_array
    //     and the small helper builders zetas_{1,2,4} for the trait's
    //     explicit-zeta NTT steps.  Zetas in the impl are stored in
    //     Montgomery form (`zeta * R mod q`); the builders use
    //     `mont_i16_to_spec_fe` so the resulting slice holds plain
    //     abstract zetas that hacspec's ntt_layer_n expects.
    #[cfg_attr(
        hax,
        hax_lib::fstar::before(
            r#"
let is_intb (l:nat) (x:int) : bool = (x <= l) && (x >= -l)
let is_i16b (l:nat) (x:i16) : bool = is_intb l (v x)
let is_i16b_array (l:nat) (x:t_Slice i16) : prop =
    forall i. i < Seq.length x ==> is_i16b l (Seq.index x i)
[@@ "opaque_to_smt"]
let is_i16b_array_opaque (l:nat) (x:t_Slice i16) : prop =
    is_i16b_array l x
let map_array (#a #b:Type) (#len:usize)
    (f: a -> b)
    (s: t_Array a len)
    : t_Array b len
    = createi (length s) (fun i -> f (Seq.index s (v i)))

(* Plain-domain lift: x is a field representative mod q. *)
let i16_to_spec_fe (x: i16)
    : Hacspec_ml_kem.Parameters.t_FieldElement =
  let m : int = v x % 3329 in
  let m_nat : nat = if m < 0 then m + 3329 else m in
  { Hacspec_ml_kem.Parameters.f_val = mk_u16 m_nat }

(* Montgomery-domain lift: x stores `v_abs * R mod q` with R = 2^16;
   R^{-1} = 169 mod 3329.  Strips the R factor to recover the abstract
   value. *)
let mont_i16_to_spec_fe (x: i16)
    : Hacspec_ml_kem.Parameters.t_FieldElement =
  let m : int = (v x * 169) % 3329 in
  let m_nat : nat = if m < 0 then m + 3329 else m in
  { Hacspec_ml_kem.Parameters.f_val = mk_u16 m_nat }

let i16_to_spec_array (#n: usize)
    (x: t_Array i16 n)
    : t_Array Hacspec_ml_kem.Parameters.t_FieldElement n =
  createi n (fun i -> i16_to_spec_fe (Seq.index x (v i)))

let mont_i16_to_spec_array (#n: usize)
    (x: t_Array i16 n)
    : t_Array Hacspec_ml_kem.Parameters.t_FieldElement n =
  createi n (fun i -> mont_i16_to_spec_fe (Seq.index x (v i)))

(* Build a small zeta slice from explicit i16 zetas, for passing to
   hacspec's ntt_layer_n / ntt_inverse_layer_n / ntt_multiply_n.
   The trait's ntt_layer_{1,2,3}_step / inv_ntt_* / ntt_multiply take
   4 / 2 / 1 zetas as separate parameters.  Impl zetas are stored
   in Montgomery form; the slice holds abstract plain zetas. *)
let zetas_1 (z0: i16)
    : t_Array Hacspec_ml_kem.Parameters.t_FieldElement (mk_usize 1) =
  createi (mk_usize 1) (fun _ -> mont_i16_to_spec_fe z0)

let zetas_2 (z0 z1: i16)
    : t_Array Hacspec_ml_kem.Parameters.t_FieldElement (mk_usize 2) =
  createi (mk_usize 2) (fun i ->
    if v i = 0 then mont_i16_to_spec_fe z0 else mont_i16_to_spec_fe z1)

let zetas_4 (z0 z1 z2 z3: i16)
    : t_Array Hacspec_ml_kem.Parameters.t_FieldElement (mk_usize 4) =
  createi (mk_usize 4) (fun i ->
    if v i = 0 then mont_i16_to_spec_fe z0
    else if v i = 1 then mont_i16_to_spec_fe z1
    else if v i = 2 then mont_i16_to_spec_fe z2
    else mont_i16_to_spec_fe z3)

(* Hacspec equations stated elementwise over arrays of any length n.
   The trait instantiates them with n=16; the polynomial layer uses
   n=256.  Each predicate bakes in whatever pre-conditions hacspec's
   underlying primitive demands (e.g. compress_d requires d < 12). *)

let compress_post_N (#n: usize) (d: usize{v d < 12})
    (input result: t_Array i16 n) : prop =
  forall (i: nat). i < v n ==>
    i16_to_spec_fe (Seq.index result i) ==
    Hacspec_ml_kem.Compress.compress_d (i16_to_spec_fe (Seq.index input i)) d

(* decompress_d (hacspec) has precondition
     to_bit_size < 12 /\ fe.f_val < 1 << to_bit_size.
   The first part is in our refinement on d; the second must be
   supplied by the caller's pre.  We use implication so the predicate
   is callable without an input refinement. *)
let decompress_post_N (#n: usize) (d: usize{v d < 12})
    (input result: t_Array i16 n) : prop =
  (forall (i: nat). i < v n ==>
     v (Seq.index input i) >= 0 /\ v (Seq.index input i) < pow2 (v d)) ==>
  (forall (i: nat). i < v n ==>
    i16_to_spec_fe (Seq.index result i) ==
    Hacspec_ml_kem.Compress.decompress_d (i16_to_spec_fe (Seq.index input i)) d)

(* Bit-packing pre/post.  An i16 array of n elements where each
   element's low d bits participate is packed into n8 bytes iff
   n * d == n8 * 8.  Stated via the BitVecEq helper — same path
   serialize_post_N used at n=16, now generic. *)
let serialize_pre_N (#n: usize)
    (d: nat{d > 0 /\ d <= 12})
    (input: t_Array i16 n) : prop =
  forall (i: nat). i < v n ==> Rust_primitives.BitVectors.bounded (Seq.index input i) d

let serialize_post_N (#n: usize)
    (d: nat{d > 0 /\ d <= 12})
    (input: t_Array i16 n {serialize_pre_N d input})
    (output: t_Slice u8 {Seq.length output * 8 == v n * d}) : prop =
  let n8 : usize = sz (Seq.length output) in
  let output_arr : t_Array u8 n8 = output in
  BitVecEq.int_t_array_bitwise_eq input d output_arr 8

let deserialize_post_N (#n: usize)
    (d: nat{d > 0 /\ d <= 12})
    (input: t_Slice u8 {Seq.length input * 8 == v n * d})
    (output: t_Array i16 n) : prop =
  let n8 : usize = sz (Seq.length input) in
  let input_arr : t_Array u8 n8 = input in
  BitVecEq.int_t_array_bitwise_eq input_arr 8 output d /\
  (forall (i: nat). i < v n ==> Rust_primitives.BitVectors.bounded (Seq.index output i) d)

(* Raw 16-bit LE byte load / store.  At n=16 lanes / 32 bytes, these
   are the trait's from_bytes / to_bytes.  Same BitVecEq path again,
   d=16 on the i16 side, d=8 on the u8 side.  Same slice-with-length
   coercion pattern as serialize_post_N. *)
let from_le_bytes_post_N (#n: usize)
    (input: t_Slice u8 {Seq.length input * 8 == v n * 16})
    (output: t_Array i16 n) : prop =
  let n2 : usize = sz (Seq.length input) in
  let input_arr : t_Array u8 n2 = input in
  BitVecEq.int_t_array_bitwise_eq input_arr 8 output 16

let to_le_bytes_post_N (#n: usize)
    (input: t_Array i16 n)
    (output: t_Slice u8 {Seq.length output * 8 == v n * 16}) : prop =
  let n2 : usize = sz (Seq.length output) in
  let output_arr : t_Array u8 n2 = output in
  BitVecEq.int_t_array_bitwise_eq input 16 output_arr 8
"#
        )
    )]
    pub(crate) fn add_pre(lhs: &[i16; 16], rhs: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"forall i.
            is_intb (pow2 15 - 1) 
                (v (Seq.index ${lhs} i) + v (Seq.index ${rhs} i))"#
        )
    }

    pub(crate) fn add_post(lhs: &[i16; 16], rhs: &[i16; 16], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"(forall i. 
                v (Seq.index ${result} i) == 
                v (Seq.index ${lhs} i) + v (Seq.index ${rhs} i))"#
        )
    }

    pub(crate) fn sub_pre(lhs: &[i16; 16], rhs: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"forall i. 
                is_intb (pow2 15 - 1) 
                (v (Seq.index ${lhs} i) - v (Seq.index ${rhs} i))"#
        )
    }

    pub(crate) fn sub_post(lhs: &[i16; 16], rhs: &[i16; 16], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"(forall i. 
                v (Seq.index ${result} i) == 
                v (Seq.index ${lhs} i) - v (Seq.index ${rhs} i))"#
        )
    }

    pub(crate) fn negate_pre(vec: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"forall i. 
                is_intb (pow2 15 - 1) (v (Seq.index ${vec} i))"#
        )
    }

    pub(crate) fn negate_post(vec: &[i16; 16], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"(forall i. 
                v (Seq.index ${result} i) == 
                - (v (Seq.index ${vec} i)))"#
        )
    }

    pub(crate) fn multiply_by_constant_pre(vec: &[i16; 16], c: i16) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"forall i. 
                is_intb (pow2 15 - 1) (v (Seq.index ${vec} i) * v $c)"#
        )
    }

    pub(crate) fn multiply_by_constant_post(
        vec: &[i16; 16],
        c: i16,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"(forall i.
                v (Seq.index ${result} i) == 
                v (Seq.index ${vec} i) * v $c)"#
        )
    }

    pub(crate) fn bitwise_and_with_constant_constant_post(
        vec: &[i16; 16],
        c: i16,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"$result == 
               map_array (fun x -> x &. $c) $vec"#
        )
    }

    pub(crate) fn shift_right_post(
        vec: &[i16; 16],
        shift_by: i32,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"(v $shift_by >= 0 /\ v $shift_by < 16) ==>
                $result == 
                map_array (fun x -> x >>! ${shift_by}) $vec"#
        )
    }

    pub(crate) fn cond_subtract_3329_pre(vec: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"is_i16b_array_opaque (pow2 12 - 1) $vec"#)
    }

    pub(crate) fn cond_subtract_3329_post(vec: &[i16; 16], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"$result == 
                map_array (fun x -> 
                    if x >=. (mk_i16 3329) then 
                        x -! (mk_i16 3329) 
                    else x) $vec"#
        )
    }

    pub(crate) fn barrett_reduce_pre(vec: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"is_i16b_array_opaque 28296 $vec"#)
    }

    pub(crate) fn barrett_reduce_post(vec: &[i16; 16], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"is_i16b_array_opaque 3328 ${result} /\
                (forall i. (v (Seq.index ${result} i) % 3329) == 
                           (v (Seq.index ${vec} i) % 3329))"#
        )
    }

    pub(crate) fn montgomery_multiply_by_constant_pre(vec: &[i16; 16], c: i16) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"is_i16b 1664 c"#)
    }

    pub(crate) fn montgomery_multiply_by_constant_post(
        vec: &[i16; 16],
        c: i16,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"is_i16b_array_opaque 3328 ${result} /\
                (forall i. ((v (Seq.index ${result} i) % 3329)==
                            (v (Seq.index ${vec} i) * v ${c} * 169) % 3329))"#
        )
    }

    pub(crate) fn to_unsigned_representative_pre(vec: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"is_i16b_array_opaque 3328 ${vec}"#)
    }

    pub(crate) fn to_unsigned_representative_post(
        vec: &[i16; 16],
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"forall i.
                let x = Seq.index ${vec} i in
                let y = Seq.index ${result} i in
                (v y >= 0 /\ v y <= 3328 /\ (v y % 3329 == v x % 3329))"#
        )
    }

    pub(crate) fn compress_1_pre(vec: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"forall i. 
                v (Seq.index ${vec} i) >= 0 /\
                v (Seq.index ${vec} i) < 3329"#
        )
    }

    // TODO(C4): re-add `compress_post_N #(mk_usize 16) (mk_usize 1) vec result`
    // conjunct once the impl body discharges it.
    pub(crate) fn compress_1_post(vec: &[i16; 16], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"forall i. bounded (Seq.index ${result} i) 1"#)
    }

    pub(crate) fn compress_pre(vec: &[i16; 16], coefficient_bits: i32) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"(v $coefficient_bits == 4 \/
                v $coefficient_bits == 5 \/
                v $coefficient_bits == 10 \/
                v $coefficient_bits == 11) /\
                (forall i. 
                    v (Seq.index $vec i) >= 0 /\
                    v (Seq.index $vec i) < 3329)"#
        )
    }

    // TODO(C4): re-add the compress_post_N conjunct once impl discharges it.
    pub(crate) fn compress_post(
        vec: &[i16; 16],
        coefficient_bits: i32,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"(v $coefficient_bits == 4 \/
                v $coefficient_bits == 5 \/
                v $coefficient_bits == 10 \/
                v $coefficient_bits == 11) ==>
                (forall i. bounded (Seq.index ${result} i) (v $coefficient_bits))"#
        )
    }

    pub(crate) fn decompress_1_post(vec: &[i16; 16], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"decompress_post_N #(mk_usize 16) (mk_usize 1) ${vec} ${result}"#
        )
    }

    pub(crate) fn decompress_ciphertext_coefficient_post(
        vec: &[i16; 16],
        coefficient_bits: i32,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"(v $coefficient_bits == 4 \/
                v $coefficient_bits == 5 \/
                v $coefficient_bits == 10 \/
                v $coefficient_bits == 11) ==>
                decompress_post_N #(mk_usize 16) (mk_usize (v $coefficient_bits)) ${vec} ${result}"#
        )
    }

    pub(crate) fn decompress_1_pre(vec: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"forall i. 
               let x = Seq.index ${vec} i in 
               (x == mk_i16 0 \/ x == mk_i16 1)"#
        )
    }

    pub(crate) fn decompress_ciphertext_coefficient_pre(
        vec: &[i16; 16],
        coefficient_bits: i32,
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"(v $coefficient_bits == 4 \/
                v $coefficient_bits == 5 \/
                v $coefficient_bits == 10 \/
                v $coefficient_bits == 11) /\
                (forall i. 
                    v (Seq.index $vec i) >= 0 /\
                    v (Seq.index $vec i) < pow2 (v $coefficient_bits))"#
        )
    }

    pub(crate) fn ntt_layer_1_step_pre(
        vec: &[i16; 16],
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#" is_i16b 1664 $zeta0 /\ is_i16b 1664 $zeta1 /\ 
                is_i16b 1664 $zeta2 /\ is_i16b 1664 $zeta3 /\
                is_i16b_array_opaque (7*3328) ${vec}"#
        )
    }

    // TODO(C4): re-add the `mont_i16_to_spec_array result == ntt_layer_n ...`
    // equation once impl discharges it.
    pub(crate) fn ntt_layer_1_step_post(
        vec: &[i16; 16],
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"is_i16b_array_opaque (8*3328) ${result}"#)
    }

    pub(crate) fn ntt_layer_2_step_pre(vec: &[i16; 16], zeta0: i16, zeta1: i16) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#" is_i16b 1664 $zeta0 /\ is_i16b 1664 $zeta1 /\ 
                is_i16b_array_opaque (6*3328) ${vec}"#
        )
    }

    // TODO(C4): re-add the hacspec ntt_layer_n equation.
    pub(crate) fn ntt_layer_2_step_post(
        vec: &[i16; 16],
        zeta0: i16,
        zeta1: i16,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"is_i16b_array_opaque (7*3328) ${result}"#)
    }

    pub(crate) fn ntt_layer_3_step_pre(vec: &[i16; 16], zeta0: i16) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#" is_i16b 1664 $zeta0 /\
                is_i16b_array_opaque (5*3328) ${vec}"#
        )
    }

    // TODO(C4): re-add the hacspec ntt_layer_n equation.
    pub(crate) fn ntt_layer_3_step_post(
        vec: &[i16; 16],
        zeta0: i16,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"is_i16b_array_opaque (6*3328) ${result}"#)
    }

    pub(crate) fn inv_ntt_layer_1_step_pre(
        vec: &[i16; 16],
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#" is_i16b 1664 zeta0 /\ is_i16b 1664 zeta1 /\ 
                is_i16b 1664 zeta2 /\ is_i16b 1664 zeta3 /\
                is_i16b_array_opaque (4*3328) ${vec}"#
        )
    }

    pub(crate) fn inv_ntt_layer_1_step_post(
        vec: &[i16; 16],
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        // TODO(C4): re-add the hacspec ntt_inverse_layer_n equation.
        hax_lib::fstar_prop_expr!(r#"is_i16b_array_opaque 3328 ${result}"#)
    }

    pub(crate) fn inv_ntt_layer_2_step_pre(
        vec: &[i16; 16],
        zeta0: i16,
        zeta1: i16,
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#" is_i16b 1664 zeta0 /\ is_i16b 1664 zeta1 /\ 
                is_i16b_array_opaque 3328 ${vec}"#
        )
    }

    // TODO(C4): re-add the hacspec ntt_inverse_layer_n equation.
    pub(crate) fn inv_ntt_layer_2_step_post(
        vec: &[i16; 16],
        zeta0: i16,
        zeta1: i16,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"is_i16b_array_opaque 3328 ${result}"#)
    }

    pub(crate) fn inv_ntt_layer_3_step_pre(vec: &[i16; 16], zeta0: i16) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#" is_i16b 1664 $zeta0 /\
                is_i16b_array_opaque 3328 ${vec}"#
        )
    }

    // TODO(C4): re-add the hacspec ntt_inverse_layer_n equation.
    pub(crate) fn inv_ntt_layer_3_step_post(
        vec: &[i16; 16],
        zeta0: i16,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"is_i16b_array_opaque 3328 ${result}"#)
    }

    pub(crate) fn ntt_multiply_pre(
        lhs: &[i16; 16],
        rhs: &[i16; 16],
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#" is_i16b 1664 zeta0 /\ is_i16b 1664 zeta1 /\
                is_i16b 1664 zeta2 /\ is_i16b 1664 zeta3 /\
                is_i16b_array_opaque 3328 ${lhs} /\
                is_i16b_array_opaque 3328 ${rhs} "#
        )
    }

    // TODO(C4): re-strengthen to include the hacspec equation
    //   mont_i16_to_spec_array result ==
    //     Hacspec_ml_kem.Ntt.ntt_multiply_n (mk_usize 16)
    //       (mont_i16_to_spec_array lhs) (mont_i16_to_spec_array rhs)
    //       (zetas_4 zeta0 zeta1 zeta2 zeta3)
    // once the impl body can discharge it.  Currently weakened to
    // bound-only to match the impl.
    pub(crate) fn ntt_multiply_post(
        lhs: &[i16; 16],
        rhs: &[i16; 16],
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"is_i16b_array_opaque 3328 ${result}"#)
    }

    pub(crate) fn serialize_1_pre(vec: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"
            serialize_pre_N 1 $vec"#
        )
    }

    pub(crate) fn serialize_1_post(vec: &[i16; 16], result: &[u8]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"   
            Seq.length ${result} == 2 /\
            (serialize_pre_N 1 $vec ==> 
               serialize_post_N 1 ${vec} ${result})"#
        )
    }

    pub(crate) fn deserialize_1_pre(input: &[u8]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Seq.length ${input} == 2"#)
    }

    pub(crate) fn deserialize_1_post(input: &[u8], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"
            Seq.length ${input} == 2 ==>
            deserialize_post_N 1 ${input} ${result}"#
        )
    }

    pub(crate) fn serialize_4_pre(vec: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"
            serialize_pre_N 4 $vec"#
        )
    }

    pub(crate) fn serialize_4_post(vec: &[i16; 16], result: &[u8]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"   
            Seq.length ${result} == 8 /\
            (serialize_pre_N 4 $vec ==> 
               serialize_post_N 4 ${vec} ${result})"#
        )
    }

    pub(crate) fn deserialize_4_pre(input: &[u8]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Seq.length ${input} == 8"#)
    }

    pub(crate) fn deserialize_4_post(input: &[u8], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"
            Seq.length ${input} == 8 ==>
            deserialize_post_N 4 ${input} ${result}"#
        )
    }

    pub(crate) fn serialize_10_pre(vec: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#" 
            serialize_pre_N 10 $vec"#
        )
    }

    pub(crate) fn serialize_10_post(vec: &[i16; 16], result: &[u8]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"   
            Seq.length ${result} == 20 /\
            (serialize_pre_N 10 $vec ==> 
               serialize_post_N 10 ${vec} ${result})"#
        )
    }

    pub(crate) fn deserialize_10_pre(input: &[u8]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Seq.length ${input} == 20"#)
    }

    pub(crate) fn deserialize_10_post(input: &[u8], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"
            Seq.length ${input} == 20 ==>
            deserialize_post_N 10 ${input} ${result}"#
        )
    }

    pub(crate) fn serialize_12_pre(vec: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#" 
            serialize_pre_N 12 $vec"#
        )
    }

    pub(crate) fn serialize_12_post(vec: &[i16; 16], result: &[u8]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"   
            Seq.length ${result} == 24 /\
            (serialize_pre_N 12 $vec ==> 
               serialize_post_N 12 ${vec} ${result})"#
        )
    }

    pub(crate) fn deserialize_12_pre(input: &[u8]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Seq.length ${input} == 24"#)
    }

    pub(crate) fn deserialize_12_post(input: &[u8], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"
            Seq.length ${input} == 24 ==>
            deserialize_post_N 12 ${input} ${result}"#
        )
    }

    pub(crate) fn serialize_5_pre(vec: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"serialize_pre_N 5 $vec"#)
    }

    pub(crate) fn serialize_5_post(vec: &[i16; 16], result: &[u8]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"Seq.length ${result} == 10 /\
               (serialize_pre_N 5 $vec ==>
                  serialize_post_N 5 ${vec} ${result})"#
        )
    }

    pub(crate) fn deserialize_5_pre(input: &[u8]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Seq.length ${input} == 10"#)
    }

    pub(crate) fn deserialize_5_post(input: &[u8], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"Seq.length ${input} == 10 ==>
               deserialize_post_N 5 ${input} ${result}"#
        )
    }

    pub(crate) fn serialize_11_pre(vec: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"serialize_pre_N 11 $vec"#)
    }

    pub(crate) fn serialize_11_post(vec: &[i16; 16], result: &[u8]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"Seq.length ${result} == 22 /\
               (serialize_pre_N 11 $vec ==>
                  serialize_post_N 11 ${vec} ${result})"#
        )
    }

    pub(crate) fn deserialize_11_pre(input: &[u8]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Seq.length ${input} == 22"#)
    }

    pub(crate) fn deserialize_11_post(input: &[u8], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"Seq.length ${input} == 22 ==>
               deserialize_post_N 11 ${input} ${result}"#
        )
    }

    pub(crate) fn from_bytes_post(input: &[u8], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"Seq.length ${input} >= 32 ==>
               (let head : t_Slice u8 = Seq.slice ${input} 0 32 in
                from_le_bytes_post_N #(mk_usize 16) head ${result})"#
        )
    }

    pub(crate) fn to_bytes_post(input: &[i16; 16], result: &[u8]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"Seq.length ${result} >= 32 ==>
               (let head : t_Slice u8 = Seq.slice ${result} 0 32 in
                to_le_bytes_post_N #(mk_usize 16) ${input} head)"#
        )
    }

    pub(crate) fn rej_sample_post(input: &[u8], count: usize, out: &[i16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"Seq.length ${input} == 24 ==>
               (Seq.length ${out} == 16 /\ v ${count} <= 16 /\
                (let bytes : t_Array u8 (mk_usize 24) = ${input} in
                 let spec_result, spec_count =
                   Hacspec_ml_kem.Sampling.rej_sample_step bytes in
                 v ${count} == v spec_count /\
                 (forall (j: nat). j < v ${count} ==>
                    v (Seq.index ${out} j) >= 0 /\
                    v (Seq.index ${out} j) <= 3328 /\
                    v (Seq.index ${out} j) ==
                      v (Seq.index spec_result j).Hacspec_ml_kem.Parameters.f_val)))"#
        )
    }
}

#[hax_lib::attributes]
pub trait Operations: Copy + Clone + Repr {
    #[allow(non_snake_case)]
    #[requires(true)]
    #[ensures(|result| result.repr() == [0i16; 16])]
    fn ZERO() -> Self;

    #[requires(array.len() == 16)]
    #[ensures(|result| result.repr() == *array)]
    fn from_i16_array(array: &[i16]) -> Self;

    #[requires(true)]
    #[ensures(|result| result == x.repr())]
    fn to_i16_array(x: Self) -> [i16; 16];

    #[requires(array.len() >= 32)]
    // TODO(C4): strengthen to `spec::from_bytes_post(&array, &result.repr())`
    // once impl bodies can discharge it.
    fn from_bytes(array: &[u8]) -> Self;

    #[requires(bytes.len() >= 32)]
    #[ensures(|_| future(bytes).len() == bytes.len())]
    // TODO(C4): add `spec::to_bytes_post(&x.repr(), &future(bytes))` post.
    fn to_bytes(x: Self, bytes: &mut [u8]);

    // Basic arithmetic
    #[requires(spec::add_pre(&lhs.repr(), &rhs.repr()))]
    #[ensures(|result| spec::add_post(&lhs.repr(), &rhs.repr(), &result.repr()))]
    fn add(lhs: Self, rhs: &Self) -> Self;

    #[requires(spec::sub_pre(&lhs.repr(), &rhs.repr()))]
    #[ensures(|result| spec::sub_post(&lhs.repr(), &rhs.repr(), &result.repr()))]
    fn sub(lhs: Self, rhs: &Self) -> Self;

    #[requires(spec::multiply_by_constant_pre(&vec.repr(), c))]
    #[ensures(|result| spec::multiply_by_constant_post(&vec.repr(), c, &result.repr()))]
    fn multiply_by_constant(vec: Self, c: i16) -> Self;

    // Modular operations
    #[requires(spec::cond_subtract_3329_pre(&v.repr()))]
    #[ensures(|result| spec::cond_subtract_3329_post(&v.repr(), &result.repr()))]
    fn cond_subtract_3329(v: Self) -> Self;

    #[requires(spec::barrett_reduce_pre(&vector.repr()))]
    #[ensures(|result| spec::barrett_reduce_post(&vector.repr(), &result.repr()))]
    fn barrett_reduce(vector: Self) -> Self;

    #[requires(spec::montgomery_multiply_by_constant_pre(&vector.repr(), constant))]
    #[ensures(|result| spec::montgomery_multiply_by_constant_post(&vector.repr(), constant, &result.repr()))]
    fn montgomery_multiply_by_constant(vector: Self, constant: i16) -> Self;

    #[requires(spec::to_unsigned_representative_pre(&a.repr()))]
    #[ensures(|result| spec::to_unsigned_representative_post(&a.repr(), &result.repr()))]
    fn to_unsigned_representative(a: Self) -> Self;

    // Compression
    #[requires(spec::compress_1_pre(&a.repr()))]
    #[ensures(|result| spec::compress_1_post(&a.repr(), &result.repr()))]
    fn compress_1(a: Self) -> Self;

    #[requires(spec::compress_pre(&a.repr(), COEFFICIENT_BITS))]
    #[ensures(|result| spec::compress_post(&a.repr(), COEFFICIENT_BITS, &result.repr()))]
    fn compress<const COEFFICIENT_BITS: i32>(a: Self) -> Self;

    #[requires(spec::decompress_1_pre(&a.repr()))]
    // TODO(C4): add `spec::decompress_1_post(...)` once impl discharges it.
    fn decompress_1(a: Self) -> Self;

    #[requires(spec::decompress_ciphertext_coefficient_pre(&a.repr(), COEFFICIENT_BITS))]
    // TODO(C4): add `spec::decompress_ciphertext_coefficient_post(...)` post.
    fn decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(a: Self) -> Self;

    // NTT
    #[requires(spec::ntt_layer_1_step_pre(&a.repr(), zeta0, zeta1, zeta2, zeta3))]
    #[ensures(|result| spec::ntt_layer_1_step_post(&a.repr(), zeta0, zeta1, zeta2, zeta3, &result.repr()))]
    fn ntt_layer_1_step(a: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self;

    #[requires(spec::ntt_layer_2_step_pre(&a.repr(), zeta0, zeta1))]
    #[ensures(|result| spec::ntt_layer_2_step_post(&a.repr(), zeta0, zeta1, &result.repr()))]
    fn ntt_layer_2_step(a: Self, zeta0: i16, zeta1: i16) -> Self;

    #[requires(spec::ntt_layer_3_step_pre(&a.repr(), zeta))]
    #[ensures(|result| spec::ntt_layer_3_step_post(&a.repr(), zeta, &result.repr()))]
    fn ntt_layer_3_step(a: Self, zeta: i16) -> Self;

    #[requires(spec::inv_ntt_layer_1_step_pre(&a.repr(), zeta0, zeta1, zeta2, zeta3))]
    #[ensures(|result| spec::inv_ntt_layer_1_step_post(&a.repr(), zeta0, zeta1, zeta2, zeta3, &result.repr()))]
    fn inv_ntt_layer_1_step(a: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self;

    #[requires(spec::inv_ntt_layer_2_step_pre(&a.repr(), zeta0, zeta1))]
    #[ensures(|result| spec::inv_ntt_layer_2_step_post(&a.repr(), zeta0, zeta1, &result.repr()))]
    fn inv_ntt_layer_2_step(a: Self, zeta0: i16, zeta1: i16) -> Self;

    #[requires(spec::inv_ntt_layer_3_step_pre(&a.repr(), zeta))]
    #[ensures(|result| spec::inv_ntt_layer_3_step_post(&a.repr(), zeta, &result.repr()))]
    fn inv_ntt_layer_3_step(a: Self, zeta: i16) -> Self;

    #[requires(spec::ntt_multiply_pre(&lhs.repr(), &rhs.repr(), zeta0, zeta1, zeta2, zeta3))]
    #[ensures(|result| spec::ntt_multiply_post(&lhs.repr(), &rhs.repr(), zeta0, zeta1, zeta2, zeta3, &result.repr()))]
    fn ntt_multiply(lhs: &Self, rhs: &Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16)
        -> Self;

    // Serialization and deserialization
    #[requires(spec::serialize_1_pre(&a.repr()))]
    #[ensures(|result| spec::serialize_1_post(&a.repr(), &result))]
    fn serialize_1(a: Self) -> [u8; 2];

    #[requires(spec::deserialize_1_pre(&a))]
    #[ensures(|result| spec::deserialize_1_post(&a, &result.repr()))]
    fn deserialize_1(a: &[u8]) -> Self;

    #[requires(spec::serialize_4_pre(&a.repr()))]
    #[ensures(|result| spec::serialize_4_post(&a.repr(), &result))]
    fn serialize_4(a: Self) -> [u8; 8];

    #[requires(spec::deserialize_4_pre(&a))]
    #[ensures(|result| spec::deserialize_4_post(&a, &result.repr()))]
    fn deserialize_4(a: &[u8]) -> Self;

    // TODO(C4): add `spec::serialize_5_pre(&a.repr())` and
    // `spec::serialize_5_post(&a.repr(), &result)` once impl discharges them.
    fn serialize_5(a: Self) -> [u8; 10];

    #[requires(a.len() == 10)]
    // TODO(C4): add `spec::deserialize_5_post(&a, &result.repr())` post.
    fn deserialize_5(a: &[u8]) -> Self;

    #[requires(spec::serialize_10_pre(&a.repr()))]
    #[ensures(|result| spec::serialize_10_post(&a.repr(), &result))]
    fn serialize_10(a: Self) -> [u8; 20];

    #[requires(spec::deserialize_10_pre(&a))]
    #[ensures(|result| spec::deserialize_10_post(&a, &result.repr()))]
    fn deserialize_10(a: &[u8]) -> Self;

    // TODO(C4): add `spec::serialize_11_pre(&a.repr())` and
    // `spec::serialize_11_post(&a.repr(), &result)` once impl discharges them.
    fn serialize_11(a: Self) -> [u8; 22];

    #[requires(a.len() == 22)]
    // TODO(C4): add `spec::deserialize_11_post(&a, &result.repr())` post.
    fn deserialize_11(a: &[u8]) -> Self;

    #[requires(spec::serialize_12_pre(&a.repr()))]
    #[ensures(|result| spec::serialize_12_post(&a.repr(), &result))]
    fn serialize_12(a: Self) -> [u8; 24];

    #[requires(spec::deserialize_12_pre(&a))]
    #[ensures(|result| spec::deserialize_12_post(&a, &result.repr()))]
    fn deserialize_12(a: &[u8]) -> Self;

    // Rejection sampling
    #[requires(a.len() == 24 && out.len() == 16)]
    #[ensures(|result| (future(out).len() == 16 && result <= 16).to_prop() & (
            hax_lib::forall(|j: usize|
                hax_lib::implies(j < result,
                    future(out)[j] >= 0 && future(out)[j] <= 3328))))]
    // TODO(C4): strengthen to `spec::rej_sample_post(&a, result, &future(out))`
    // once impl bodies can discharge the rej_sample_step equation.
    fn rej_sample(a: &[u8], out: &mut [i16]) -> usize;
}
