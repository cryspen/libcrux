use super::arithmetic::{self, montgomery_multiply_fe_by_fer};
use super::vector_type::Coefficients;
use crate::simd::traits::{COEFFICIENTS_IN_SIMD_UNIT, SIMD_UNITS_IN_RING_ELEMENT};

#[cfg(hax)]
use crate::simd::traits::specs::*;

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 300 --split_queries always")]
#[hax_lib::fstar::before(r#"open Libcrux_ml_dsa.Simd.Portable.Invntt_theory"#)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
    1 <= v $step /\ v $step <= 4 /\ v $index + v $step < 8 /\
    Spec.Utils.is_i32b (simd_layer_factor $step * v $FIELD_MAX)
                    (Seq.index ${simd_unit}.f_values (v $index)) /\
    Spec.Utils.is_i32b (simd_layer_factor $step * v $FIELD_MAX)
                    (Seq.index ${simd_unit}.f_values (v $index + v $step)) /\
    Spec.Utils.is_i32b 4190208 $zeta
"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    Spec.Utils.modifies2_8 ${simd_unit}.f_values ${simd_unit}_future.f_values index (index +! step) /\
    Spec.Utils.is_i32b (2 * (simd_layer_factor $step)  * v $FIELD_MAX)
                    (Seq.index ${simd_unit}_future.f_values (v $index)) /\
    Spec.Utils.is_i32b (2 * (simd_layer_factor $step)  * v $FIELD_MAX)
                    (Seq.index ${simd_unit}_future.f_values (v $index + v $step)) /\
    (let ci = ${simd_unit}.f_values in
     let co = ${simd_unit}_future.f_values in
     v (Seq.index co (v $index)) ==
       v (Seq.index ci (v $index)) + v (Seq.index ci (v $index + v $step)) /\
     (v (Seq.index co (v $index + v $step))) % 8380417 ==
       ((v (Seq.index ci (v $index + v $step)) - v (Seq.index ci (v $index))) * v $zeta * 8265825) % 8380417)
"#) )]
fn simd_unit_inv_ntt_step(simd_unit: &mut Coefficients, zeta: i32, index: usize, step: usize) {
    let a_minus_b = simd_unit.values[index + step] - simd_unit.values[index];
    simd_unit.values[index] = simd_unit.values[index] + simd_unit.values[index + step];
    simd_unit.values[index + step] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);
    hax_lib::fstar!(r#"reveal_opaque (`%Spec.MLDSA.Math.mod_q) (Spec.MLDSA.Math.mod_q)"#);
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 300 --split_queries always")]
#[hax_lib::fstar::before(r#"
    (* ---- INVERSE Layer 0: opaque per-chunk GS-FE atom (4 zetas/chunk, pairs (2p,2p+1)).
       GS butterfly: co[2p] = ci[2p] + ci[2p+1] (plain add); the odd lane co[2p+1] is a
       direct mod-q relation (= mont_mul(ci[2p+1]-ci[2p], zeta), NO separate `t` witness). *)
    [@@ "opaque_to_smt"]
    let unit_fe_post_inv_l0 (ci co: t_Array i32 (sz 8))
                        (zeta0 zeta1 zeta2 zeta3: i32{Spec.Utils.is_i32b 4190208 zeta0 /\ Spec.Utils.is_i32b 4190208 zeta1 /\ Spec.Utils.is_i32b 4190208 zeta2 /\ Spec.Utils.is_i32b 4190208 zeta3}) : Type0 =
      (v (Seq.index co 0) == v (Seq.index ci 0) + v (Seq.index ci 1) /\
       (v (Seq.index co 1)) % 8380417 == ((v (Seq.index ci 1) - v (Seq.index ci 0)) * v zeta0 * 8265825) % 8380417 /\
       v (Seq.index co 2) == v (Seq.index ci 2) + v (Seq.index ci 3) /\
       (v (Seq.index co 3)) % 8380417 == ((v (Seq.index ci 3) - v (Seq.index ci 2)) * v zeta1 * 8265825) % 8380417 /\
       v (Seq.index co 4) == v (Seq.index ci 4) + v (Seq.index ci 5) /\
       (v (Seq.index co 5)) % 8380417 == ((v (Seq.index ci 5) - v (Seq.index ci 4)) * v zeta2 * 8265825) % 8380417 /\
       v (Seq.index co 6) == v (Seq.index ci 6) + v (Seq.index ci 7) /\
       (v (Seq.index co 7)) % 8380417 == ((v (Seq.index ci 7) - v (Seq.index ci 6)) * v zeta3 * 8265825) % 8380417)
"#)]
#[hax_lib::fstar::before(r#"
    #push-options "--fuel 0 --ifuel 1 --z3rlimit 100 --split_queries always"
    let lemma_atom_to_bf_inv_l0 (ci co: t_Array i32 (sz 8))
                            (zf: (p: nat{p < 4}) -> (z: i32{Spec.Utils.is_i32b 4190208 z}))
        : Lemma (requires unit_fe_post_inv_l0 ci co (zf 0) (zf 1) (zf 2) (zf 3))
                (ensures
                  (forall (p: nat{p < 4}).
                     v (Seq.index co (2*p))   == v (Seq.index ci (2*p)) + v (Seq.index ci (2*p+1)) /\
                     (v (Seq.index co (2*p+1))) % 8380417 ==
                       ((v (Seq.index ci (2*p+1)) - v (Seq.index ci (2*p))) * v (zf p) * 8265825) % 8380417))
      = reveal_opaque (`%unit_fe_post_inv_l0) unit_fe_post_inv_l0;
        introduce forall (p: nat{p < 4}).
            (v (Seq.index co (2*p))   == v (Seq.index ci (2*p)) + v (Seq.index ci (2*p+1)) /\
             (v (Seq.index co (2*p+1))) % 8380417 ==
               ((v (Seq.index ci (2*p+1)) - v (Seq.index ci (2*p))) * v (zf p) * 8265825) % 8380417)
        with (match p with | 0 -> () | 1 -> () | 2 -> () | _ -> ())
    #pop-options
"#)]
#[hax_lib::fstar::before(r#"
    #push-options "--fuel 0 --ifuel 1 --z3rlimit 200 --split_queries always"
    let lemma_inv_l0_driver_compose
          (orig fut: t_Array (t_Array i32 (sz 8)) (sz 32))
        : Lemma
            (requires
              Spec.Utils.forall32 (fun b ->
                unit_fe_post_inv_l0 (Seq.index orig b) (Seq.index fut b)
                                (mk_i32 (Spec.MLDSA.NttConstants.zeta_r (255 - (4*b + 0))))
                                (mk_i32 (Spec.MLDSA.NttConstants.zeta_r (255 - (4*b + 1))))
                                (mk_i32 (Spec.MLDSA.NttConstants.zeta_r (255 - (4*b + 2))))
                                (mk_i32 (Spec.MLDSA.NttConstants.zeta_r (255 - (4*b + 3))))))
            (ensures
              (let in_flat = Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array orig in
               let out_flat = Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array fut in
               let spec = Hacspec_ml_dsa.Ntt.intt_layer in_flat (mk_usize 0) in
               forall (i: nat). i < 256 ==>
                 (v (Seq.index out_flat i)) % 8380417 == (v (Seq.index spec i)) % 8380417))
      = let zm (b: nat{b < 32}) (p: nat{p < 4}) : (z: i32{Spec.Utils.is_i32b 4190208 z}) =
          mk_i32 (Spec.MLDSA.NttConstants.zeta_r (255 - (4*b + p))) in
        Libcrux_ml_dsa.Simd.Portable.Ntt.forall32_elim_1d (fun b -> unit_fe_post_inv_l0 (Seq.index orig b) (Seq.index fut b)
                                     (mk_i32 (Spec.MLDSA.NttConstants.zeta_r (255 - (4*b + 0))))
                                     (mk_i32 (Spec.MLDSA.NttConstants.zeta_r (255 - (4*b + 1))))
                                     (mk_i32 (Spec.MLDSA.NttConstants.zeta_r (255 - (4*b + 2))))
                                     (mk_i32 (Spec.MLDSA.NttConstants.zeta_r (255 - (4*b + 3)))));
        (let aux (b: nat{b < 32}) (p: nat{p < 4}) : Lemma
           (let ci = Seq.index orig b in
            let co = Seq.index fut b in
            v (Seq.index co (2*p)) == v (Seq.index ci (2*p)) + v (Seq.index ci (2*p+1)) /\
            (v (Seq.index co (2*p+1))) % 8380417 ==
              ((v (Seq.index ci (2*p+1)) - v (Seq.index ci (2*p))) * v (zm b p) * 8265825) % 8380417 /\
            (v (zm b p)) % 8380417 ==
              (v (Hacspec_ml_dsa.Ntt.v_ZETAS.[ mk_usize (255 - (4*b + p)) ] <: i32) * pow2 32) % 8380417)
          = lemma_atom_to_bf_inv_l0 (Seq.index orig b) (Seq.index fut b) (fun p -> zm b p);
            reveal_opaque (`%Spec.MLDSA.Math.mod_q) (Spec.MLDSA.Math.mod_q);
            let _ = Spec.MLDSA.NttConstants.zeta_r (255 - (4*b + p)) in
            Hacspec_ml_dsa.Commute.Chunk.lemma_v_zetas_eq_zeta (255 - (4*b + p))
         in Classical.forall_intro_2 aux);
        Hacspec_ml_dsa.Commute.Chunk.lemma_intt_layer_0_step_to_hacspec_poly orig fut zm
    #pop-options
"#)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
    Spec.Utils.is_i32b_array (v $FIELD_MAX) ${simd_unit}.f_values /\
    Spec.Utils.is_i32b 4190208 $zeta0 /\
    Spec.Utils.is_i32b 4190208 $zeta1 /\
    Spec.Utils.is_i32b 4190208 $zeta2 /\
    Spec.Utils.is_i32b 4190208 $zeta3
"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    Spec.Utils.is_i32b_array (2 * v $FIELD_MAX) ${simd_unit}_future.f_values /\
    (let ci = ${simd_unit}.f_values in
     let co = ${simd_unit}_future.f_values in
     v (Seq.index co 0) == v (Seq.index ci 0) + v (Seq.index ci 1) /\
     (v (Seq.index co 1)) % 8380417 == ((v (Seq.index ci 1) - v (Seq.index ci 0)) * v $zeta0 * 8265825) % 8380417 /\
     v (Seq.index co 2) == v (Seq.index ci 2) + v (Seq.index ci 3) /\
     (v (Seq.index co 3)) % 8380417 == ((v (Seq.index ci 3) - v (Seq.index ci 2)) * v $zeta1 * 8265825) % 8380417 /\
     v (Seq.index co 4) == v (Seq.index ci 4) + v (Seq.index ci 5) /\
     (v (Seq.index co 5)) % 8380417 == ((v (Seq.index ci 5) - v (Seq.index ci 4)) * v $zeta2 * 8265825) % 8380417 /\
     v (Seq.index co 6) == v (Seq.index ci 6) + v (Seq.index ci 7) /\
     (v (Seq.index co 7)) % 8380417 == ((v (Seq.index ci 7) - v (Seq.index ci 6)) * v $zeta3 * 8265825) % 8380417)
"#) )]
pub fn simd_unit_invert_ntt_at_layer_0(
    simd_unit: &mut Coefficients,
    zeta0: i32,
    zeta1: i32,
    zeta2: i32,
    zeta3: i32,
) {
    simd_unit_inv_ntt_step(simd_unit, zeta0, 0, 1);
    simd_unit_inv_ntt_step(simd_unit, zeta1, 2, 1);
    simd_unit_inv_ntt_step(simd_unit, zeta2, 4, 1);
    simd_unit_inv_ntt_step(simd_unit, zeta3, 6, 1);
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 300 --split_queries always")]
#[hax_lib::fstar::before(r#"
    (* ---- INVERSE Layer 1: opaque per-chunk GS-FE atom (2 zetas/chunk, pairs (4h+j,4h+j+2)). *)
    [@@ "opaque_to_smt"]
    let unit_fe_post_inv_l1 (ci co: t_Array i32 (sz 8))
                        (zeta0 zeta1: i32{Spec.Utils.is_i32b 4190208 zeta0 /\ Spec.Utils.is_i32b 4190208 zeta1}) : Type0 =
      (v (Seq.index co 0) == v (Seq.index ci 0) + v (Seq.index ci 2) /\
       (v (Seq.index co 2)) % 8380417 == ((v (Seq.index ci 2) - v (Seq.index ci 0)) * v zeta0 * 8265825) % 8380417 /\
       v (Seq.index co 1) == v (Seq.index ci 1) + v (Seq.index ci 3) /\
       (v (Seq.index co 3)) % 8380417 == ((v (Seq.index ci 3) - v (Seq.index ci 1)) * v zeta0 * 8265825) % 8380417 /\
       v (Seq.index co 4) == v (Seq.index ci 4) + v (Seq.index ci 6) /\
       (v (Seq.index co 6)) % 8380417 == ((v (Seq.index ci 6) - v (Seq.index ci 4)) * v zeta1 * 8265825) % 8380417 /\
       v (Seq.index co 5) == v (Seq.index ci 5) + v (Seq.index ci 7) /\
       (v (Seq.index co 7)) % 8380417 == ((v (Seq.index ci 7) - v (Seq.index ci 5)) * v zeta1 * 8265825) % 8380417)
"#)]
#[hax_lib::fstar::before(r#"
    #push-options "--fuel 0 --ifuel 1 --z3rlimit 100 --split_queries always"
    let lemma_atom_to_bf_inv_l1 (ci co: t_Array i32 (sz 8))
                            (zf: (h: nat{h < 2}) -> (z: i32{Spec.Utils.is_i32b 4190208 z}))
        : Lemma (requires unit_fe_post_inv_l1 ci co (zf 0) (zf 1))
                (ensures
                  (forall (h: nat{h < 2}) (j: nat{j < 2}).
                     v (Seq.index co (4*h+j))   == v (Seq.index ci (4*h+j)) + v (Seq.index ci (4*h+j+2)) /\
                     (v (Seq.index co (4*h+j+2))) % 8380417 ==
                       ((v (Seq.index ci (4*h+j+2)) - v (Seq.index ci (4*h+j))) * v (zf h) * 8265825) % 8380417))
      = reveal_opaque (`%unit_fe_post_inv_l1) unit_fe_post_inv_l1;
        introduce forall (h: nat{h < 2}) (j: nat{j < 2}).
            (v (Seq.index co (4*h+j))   == v (Seq.index ci (4*h+j)) + v (Seq.index ci (4*h+j+2)) /\
             (v (Seq.index co (4*h+j+2))) % 8380417 ==
               ((v (Seq.index ci (4*h+j+2)) - v (Seq.index ci (4*h+j))) * v (zf h) * 8265825) % 8380417)
        with (match h with | 0 -> (match j with | 0 -> () | _ -> ()) | _ -> (match j with | 0 -> () | _ -> ()))
    #pop-options
"#)]
#[hax_lib::fstar::before(r#"
    #push-options "--fuel 0 --ifuel 1 --z3rlimit 200 --split_queries always"
    let lemma_inv_l1_driver_compose
          (orig fut: t_Array (t_Array i32 (sz 8)) (sz 32))
        : Lemma
            (requires
              Spec.Utils.forall32 (fun b ->
                unit_fe_post_inv_l1 (Seq.index orig b) (Seq.index fut b)
                                (mk_i32 (Spec.MLDSA.NttConstants.zeta_r (127 - (2*b + 0))))
                                (mk_i32 (Spec.MLDSA.NttConstants.zeta_r (127 - (2*b + 1))))))
            (ensures
              (let in_flat = Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array orig in
               let out_flat = Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array fut in
               let spec = Hacspec_ml_dsa.Ntt.intt_layer in_flat (mk_usize 1) in
               forall (i: nat). i < 256 ==>
                 (v (Seq.index out_flat i)) % 8380417 == (v (Seq.index spec i)) % 8380417))
      = let zm (b: nat{b < 32}) (h: nat{h < 2}) : (z: i32{Spec.Utils.is_i32b 4190208 z}) =
          mk_i32 (Spec.MLDSA.NttConstants.zeta_r (127 - (2*b + h))) in
        Libcrux_ml_dsa.Simd.Portable.Ntt.forall32_elim_1d (fun b -> unit_fe_post_inv_l1 (Seq.index orig b) (Seq.index fut b)
                                     (mk_i32 (Spec.MLDSA.NttConstants.zeta_r (127 - (2*b + 0))))
                                     (mk_i32 (Spec.MLDSA.NttConstants.zeta_r (127 - (2*b + 1)))));
        (let aux_bf (b: nat{b < 32}) : Lemma
           (forall (h: nat{h < 2}) (j: nat{j < 2}).
             (let ci = Seq.index orig b in
              let co = Seq.index fut b in
              v (Seq.index co (4*h+j))   == v (Seq.index ci (4*h+j)) + v (Seq.index ci (4*h+j+2)) /\
              (v (Seq.index co (4*h+j+2))) % 8380417 ==
                ((v (Seq.index ci (4*h+j+2)) - v (Seq.index ci (4*h+j))) * v (zm b h) * 8265825) % 8380417))
          = lemma_atom_to_bf_inv_l1 (Seq.index orig b) (Seq.index fut b) (fun h -> zm b h)
         in Classical.forall_intro aux_bf);
        (let aux_z (b: nat{b < 32}) (h: nat{h < 2}) : Lemma
           ((v (zm b h)) % 8380417 ==
            (v (Hacspec_ml_dsa.Ntt.v_ZETAS.[ mk_usize (127 - (2*b + h)) ] <: i32) * pow2 32) % 8380417)
          = reveal_opaque (`%Spec.MLDSA.Math.mod_q) (Spec.MLDSA.Math.mod_q);
            let _ = Spec.MLDSA.NttConstants.zeta_r (127 - (2*b + h)) in
            Hacspec_ml_dsa.Commute.Chunk.lemma_v_zetas_eq_zeta (127 - (2*b + h))
         in Classical.forall_intro_2 aux_z);
        Hacspec_ml_dsa.Commute.Chunk.lemma_intt_layer_1_step_to_hacspec_poly orig fut zm
    #pop-options
"#)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
    Spec.Utils.is_i32b_array (2 * v $FIELD_MAX) ${simd_unit}.f_values /\
    Spec.Utils.is_i32b 4190208 $zeta0 /\
    Spec.Utils.is_i32b 4190208 $zeta1
"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    Spec.Utils.is_i32b_array (4 * v $FIELD_MAX) ${simd_unit}_future.f_values /\
    (let ci = ${simd_unit}.f_values in
     let co = ${simd_unit}_future.f_values in
     v (Seq.index co 0) == v (Seq.index ci 0) + v (Seq.index ci 2) /\
     (v (Seq.index co 2)) % 8380417 == ((v (Seq.index ci 2) - v (Seq.index ci 0)) * v $zeta0 * 8265825) % 8380417 /\
     v (Seq.index co 1) == v (Seq.index ci 1) + v (Seq.index ci 3) /\
     (v (Seq.index co 3)) % 8380417 == ((v (Seq.index ci 3) - v (Seq.index ci 1)) * v $zeta0 * 8265825) % 8380417 /\
     v (Seq.index co 4) == v (Seq.index ci 4) + v (Seq.index ci 6) /\
     (v (Seq.index co 6)) % 8380417 == ((v (Seq.index ci 6) - v (Seq.index ci 4)) * v $zeta1 * 8265825) % 8380417 /\
     v (Seq.index co 5) == v (Seq.index ci 5) + v (Seq.index ci 7) /\
     (v (Seq.index co 7)) % 8380417 == ((v (Seq.index ci 7) - v (Seq.index ci 5)) * v $zeta1 * 8265825) % 8380417)
"#) )]
pub fn simd_unit_invert_ntt_at_layer_1(simd_unit: &mut Coefficients, zeta0: i32, zeta1: i32) {
    simd_unit_inv_ntt_step(simd_unit, zeta0, 0, 2);
    simd_unit_inv_ntt_step(simd_unit, zeta0, 1, 2);
    simd_unit_inv_ntt_step(simd_unit, zeta1, 4, 2);
    simd_unit_inv_ntt_step(simd_unit, zeta1, 5, 2);
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 300 --split_queries always")]
#[hax_lib::fstar::before(r#"
    (* ---- INVERSE Layer 2: opaque per-chunk GS-FE atom (1 zeta/chunk, pairs (p,p+4)). *)
    [@@ "opaque_to_smt"]
    let unit_fe_post_inv_l2 (ci co: t_Array i32 (sz 8))
                        (zeta: i32{Spec.Utils.is_i32b 4190208 zeta}) : Type0 =
      (v (Seq.index co 0) == v (Seq.index ci 0) + v (Seq.index ci 4) /\
       (v (Seq.index co 4)) % 8380417 == ((v (Seq.index ci 4) - v (Seq.index ci 0)) * v zeta * 8265825) % 8380417 /\
       v (Seq.index co 1) == v (Seq.index ci 1) + v (Seq.index ci 5) /\
       (v (Seq.index co 5)) % 8380417 == ((v (Seq.index ci 5) - v (Seq.index ci 1)) * v zeta * 8265825) % 8380417 /\
       v (Seq.index co 2) == v (Seq.index ci 2) + v (Seq.index ci 6) /\
       (v (Seq.index co 6)) % 8380417 == ((v (Seq.index ci 6) - v (Seq.index ci 2)) * v zeta * 8265825) % 8380417 /\
       v (Seq.index co 3) == v (Seq.index ci 3) + v (Seq.index ci 7) /\
       (v (Seq.index co 7)) % 8380417 == ((v (Seq.index ci 7) - v (Seq.index ci 3)) * v zeta * 8265825) % 8380417)
"#)]
#[hax_lib::fstar::before(r#"
    #push-options "--fuel 0 --ifuel 1 --z3rlimit 100 --split_queries always"
    let lemma_atom_to_bf_inv_l2 (ci co: t_Array i32 (sz 8))
                            (zeta: i32{Spec.Utils.is_i32b 4190208 zeta})
        : Lemma (requires unit_fe_post_inv_l2 ci co zeta)
                (ensures
                  (forall (p: nat{p < 4}).
                     v (Seq.index co p)     == v (Seq.index ci p) + v (Seq.index ci (p+4)) /\
                     (v (Seq.index co (p+4))) % 8380417 ==
                       ((v (Seq.index ci (p+4)) - v (Seq.index ci p)) * v zeta * 8265825) % 8380417))
      = reveal_opaque (`%unit_fe_post_inv_l2) unit_fe_post_inv_l2;
        introduce forall (p: nat{p < 4}).
            (v (Seq.index co p)     == v (Seq.index ci p) + v (Seq.index ci (p+4)) /\
             (v (Seq.index co (p+4))) % 8380417 ==
               ((v (Seq.index ci (p+4)) - v (Seq.index ci p)) * v zeta * 8265825) % 8380417)
        with (match p with | 0 -> () | 1 -> () | 2 -> () | _ -> ())
    #pop-options
"#)]
#[hax_lib::fstar::before(r#"
    #push-options "--fuel 0 --ifuel 1 --z3rlimit 200 --split_queries always"
    let lemma_inv_l2_driver_compose
          (orig fut: t_Array (t_Array i32 (sz 8)) (sz 32))
        : Lemma
            (requires
              Spec.Utils.forall32 (fun b ->
                unit_fe_post_inv_l2 (Seq.index orig b) (Seq.index fut b)
                                (mk_i32 (Spec.MLDSA.NttConstants.zeta_r (63 - b)))))
            (ensures
              (let in_flat = Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array orig in
               let out_flat = Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array fut in
               let spec = Hacspec_ml_dsa.Ntt.intt_layer in_flat (mk_usize 2) in
               forall (i: nat). i < 256 ==>
                 (v (Seq.index out_flat i)) % 8380417 == (v (Seq.index spec i)) % 8380417))
      = let zm (b: nat{b < 32}) : (z: i32{Spec.Utils.is_i32b 4190208 z}) =
          mk_i32 (Spec.MLDSA.NttConstants.zeta_r (63 - b)) in
        Libcrux_ml_dsa.Simd.Portable.Ntt.forall32_elim_1d (fun b -> unit_fe_post_inv_l2 (Seq.index orig b) (Seq.index fut b)
                                     (mk_i32 (Spec.MLDSA.NttConstants.zeta_r (63 - b))));
        (let aux_bf (b: nat{b < 32}) : Lemma
           (forall (p: nat{p < 4}).
             (let ci = Seq.index orig b in
              let co = Seq.index fut b in
              v (Seq.index co p)     == v (Seq.index ci p) + v (Seq.index ci (p+4)) /\
              (v (Seq.index co (p+4))) % 8380417 ==
                ((v (Seq.index ci (p+4)) - v (Seq.index ci p)) * v (zm b) * 8265825) % 8380417))
          = lemma_atom_to_bf_inv_l2 (Seq.index orig b) (Seq.index fut b) (zm b)
         in Classical.forall_intro aux_bf);
        (let aux_z (b: nat{b < 32}) : Lemma
           ((v (zm b)) % 8380417 ==
            (v (Hacspec_ml_dsa.Ntt.v_ZETAS.[ mk_usize (63 - b) ] <: i32) * pow2 32) % 8380417)
          = reveal_opaque (`%Spec.MLDSA.Math.mod_q) (Spec.MLDSA.Math.mod_q);
            let _ = Spec.MLDSA.NttConstants.zeta_r (63 - b) in
            Hacspec_ml_dsa.Commute.Chunk.lemma_v_zetas_eq_zeta (63 - b)
         in Classical.forall_intro aux_z);
        Hacspec_ml_dsa.Commute.Chunk.lemma_intt_layer_2_step_to_hacspec_poly orig fut zm
    #pop-options
"#)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
    Spec.Utils.is_i32b_array (4 * v $FIELD_MAX) ${simd_unit}.f_values /\
    Spec.Utils.is_i32b 4190208 $zeta
"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    Spec.Utils.is_i32b_array (8 * v $FIELD_MAX) ${simd_unit}_future.f_values /\
    (let ci = ${simd_unit}.f_values in
     let co = ${simd_unit}_future.f_values in
     v (Seq.index co 0) == v (Seq.index ci 0) + v (Seq.index ci 4) /\
     (v (Seq.index co 4)) % 8380417 == ((v (Seq.index ci 4) - v (Seq.index ci 0)) * v $zeta * 8265825) % 8380417 /\
     v (Seq.index co 1) == v (Seq.index ci 1) + v (Seq.index ci 5) /\
     (v (Seq.index co 5)) % 8380417 == ((v (Seq.index ci 5) - v (Seq.index ci 1)) * v $zeta * 8265825) % 8380417 /\
     v (Seq.index co 2) == v (Seq.index ci 2) + v (Seq.index ci 6) /\
     (v (Seq.index co 6)) % 8380417 == ((v (Seq.index ci 6) - v (Seq.index ci 2)) * v $zeta * 8265825) % 8380417 /\
     v (Seq.index co 3) == v (Seq.index ci 3) + v (Seq.index ci 7) /\
     (v (Seq.index co 7)) % 8380417 == ((v (Seq.index ci 7) - v (Seq.index ci 3)) * v $zeta * 8265825) % 8380417)
"#) )]
pub fn simd_unit_invert_ntt_at_layer_2(simd_unit: &mut Coefficients, zeta: i32) {
    simd_unit_inv_ntt_step(simd_unit, zeta, 0, 4);
    simd_unit_inv_ntt_step(simd_unit, zeta, 1, 4);
    simd_unit_inv_ntt_step(simd_unit, zeta, 2, 4);
    simd_unit_inv_ntt_step(simd_unit, zeta, 3, 4);
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 400 --split_queries always")]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
    Libcrux_ml_dsa.Simd.Portable.Ntt.is_i32b_polynomial (v $FIELD_MAX) ${re}
"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    Libcrux_ml_dsa.Simd.Portable.Ntt.is_i32b_polynomial (2 * v $FIELD_MAX) ${re}_future /\
    (let in_flat = Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${re}) in
     let out_flat = Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${re}_future) in
     let spec = Hacspec_ml_dsa.Ntt.intt_layer in_flat (mk_usize 0) in
     forall (i: nat). i < 256 ==>
       (v (Seq.index out_flat i)) % 8380417 == (v (Seq.index spec i)) % 8380417)
"#) )]
fn invert_ntt_at_layer_0(re: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT]) {
    #[inline(always)]
    #[hax_lib::fstar::options("--z3rlimit 100")]
    #[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
    #[hax_lib::requires(fstar!(r#"
        v index < v $SIMD_UNITS_IN_RING_ELEMENT /\
        Spec.Utils.is_i32b_array_opaque (v $FIELD_MAX) 
            (Seq.index ${re} (v index)).f_values /\
        Spec.Utils.is_i32b 4190208 $zeta0 /\
        Spec.Utils.is_i32b 4190208 $zeta1 /\
        Spec.Utils.is_i32b 4190208 $zeta2 /\
        Spec.Utils.is_i32b 4190208 $zeta3
    "#))]
    #[hax_lib::ensures(|_| fstar!(r#"
        Spec.Utils.modifies1_32 ${re} ${re}_future $index /\
        Spec.Utils.is_i32b_array_opaque (2* v $FIELD_MAX)
            (Seq.index ${re}_future (v index)).f_values /\
        unit_fe_post_inv_l0 (Seq.index ${re} (v $index)).f_values
                        (Seq.index ${re}_future (v $index)).f_values
                        $zeta0 $zeta1 $zeta2 $zeta3
     "#))]
    fn round(
        re: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT],
        index: usize,
        zeta0: i32,
        zeta1: i32,
        zeta2: i32,
        zeta3: i32,
    ) {
        hax_lib::fstar!(
            "reveal_opaque (`%Spec.Utils.is_i32b_array_opaque) (Spec.Utils.is_i32b_array_opaque)"
        );
        simd_unit_invert_ntt_at_layer_0(&mut re[index], zeta0, zeta1, zeta2, zeta3);
        hax_lib::fstar!("reveal_opaque (`%unit_fe_post_inv_l0) unit_fe_post_inv_l0");
    }

    #[cfg(hax)]
    let orig_re = re.clone();

    round(re, 0, 1976782, -846154, 1400424, 3937738);
    round(re, 1, -1362209, -48306, 3919660, -554416);
    round(re, 2, -3545687, 1612842, -976891, 183443);
    round(re, 3, -2286327, -420899, -2235985, -2939036);
    round(re, 4, -3833893, -260646, -1104333, -1667432);
    round(re, 5, 1910376, -1803090, 1723600, -426683);
    round(re, 6, 472078, 1717735, -975884, 2213111);
    round(re, 7, 269760, 3866901, 3523897, -3038916);
    round(re, 8, -1799107, -3694233, 1652634, 810149);
    round(re, 9, 3014001, 1616392, 162844, -3183426);
    round(re, 10, -1207385, 185531, 3369112, 1957272);
    round(re, 11, -164721, 2454455, 2432395, -2013608);
    round(re, 12, -3776993, 594136, -3724270, -2584293);
    round(re, 13, -1846953, -1671176, -2831860, -542412);
    round(re, 14, 3406031, 2235880, 777191, 1500165);
    round(re, 15, -1374803, -2546312, 1917081, -1279661);
    round(re, 16, -1962642, 3306115, 1312455, -451100);
    round(re, 17, -1430225, -3318210, 1237275, -1333058);
    round(re, 18, -1050970, 1903435, 1869119, -2994039);
    round(re, 19, -3548272, 2635921, 1250494, -3767016);
    round(re, 20, 1595974, 2486353, 1247620, 4055324);
    round(re, 21, 1265009, -2590150, 2691481, 2842341);
    round(re, 22, 203044, 1735879, -3342277, 3437287);
    round(re, 23, 4108315, -2437823, 286988, 342297);
    round(re, 24, -3595838, -768622, -525098, -3556995);
    round(re, 25, 3207046, 2031748, -3122442, -655327);
    round(re, 26, -522500, -43260, -1613174, 495491);
    round(re, 27, 819034, 909542, 1859098, 900702);
    round(re, 28, -3193378, -1197226, -3759364, -3520352);
    round(re, 29, 3513181, -1235728, 2434439, 266997);
    round(re, 30, -3562462, -2446433, 2244091, -3342478);
    round(re, 31, 3817976, 2316500, 3407706, 2091667);
    hax_lib::fstar!(
        r#"
assert_norm (Spec.MLDSA.NttConstants.zeta_r 128 == 2091667);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 129 == 3407706);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 130 == 2316500);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 131 == 3817976);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 132 == (-3342478));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 133 == 2244091);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 134 == (-2446433));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 135 == (-3562462));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 136 == 266997);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 137 == 2434439);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 138 == (-1235728));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 139 == 3513181);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 140 == (-3520352));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 141 == (-3759364));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 142 == (-1197226));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 143 == (-3193378));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 144 == 900702);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 145 == 1859098);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 146 == 909542);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 147 == 819034);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 148 == 495491);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 149 == (-1613174));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 150 == (-43260));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 151 == (-522500));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 152 == (-655327));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 153 == (-3122442));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 154 == 2031748);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 155 == 3207046);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 156 == (-3556995));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 157 == (-525098));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 158 == (-768622));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 159 == (-3595838));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 160 == 342297);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 161 == 286988);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 162 == (-2437823));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 163 == 4108315);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 164 == 3437287);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 165 == (-3342277));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 166 == 1735879);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 167 == 203044);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 168 == 2842341);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 169 == 2691481);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 170 == (-2590150));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 171 == 1265009);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 172 == 4055324);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 173 == 1247620);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 174 == 2486353);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 175 == 1595974);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 176 == (-3767016));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 177 == 1250494);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 178 == 2635921);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 179 == (-3548272));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 180 == (-2994039));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 181 == 1869119);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 182 == 1903435);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 183 == (-1050970));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 184 == (-1333058));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 185 == 1237275);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 186 == (-3318210));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 187 == (-1430225));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 188 == (-451100));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 189 == 1312455);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 190 == 3306115);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 191 == (-1962642));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 192 == (-1279661));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 193 == 1917081);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 194 == (-2546312));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 195 == (-1374803));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 196 == 1500165);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 197 == 777191);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 198 == 2235880);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 199 == 3406031);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 200 == (-542412));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 201 == (-2831860));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 202 == (-1671176));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 203 == (-1846953));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 204 == (-2584293));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 205 == (-3724270));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 206 == 594136);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 207 == (-3776993));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 208 == (-2013608));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 209 == 2432395);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 210 == 2454455);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 211 == (-164721));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 212 == 1957272);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 213 == 3369112);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 214 == 185531);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 215 == (-1207385));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 216 == (-3183426));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 217 == 162844);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 218 == 1616392);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 219 == 3014001);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 220 == 810149);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 221 == 1652634);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 222 == (-3694233));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 223 == (-1799107));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 224 == (-3038916));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 225 == 3523897);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 226 == 3866901);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 227 == 269760);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 228 == 2213111);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 229 == (-975884));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 230 == 1717735);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 231 == 472078);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 232 == (-426683));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 233 == 1723600);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 234 == (-1803090));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 235 == 1910376);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 236 == (-1667432));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 237 == (-1104333));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 238 == (-260646));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 239 == (-3833893));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 240 == (-2939036));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 241 == (-2235985));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 242 == (-420899));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 243 == (-2286327));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 244 == 183443);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 245 == (-976891));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 246 == 1612842);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 247 == (-3545687));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 248 == (-554416));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 249 == 3919660);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 250 == (-48306));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 251 == (-1362209));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 252 == 3937738);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 253 == 1400424);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 254 == (-846154));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 255 == 1976782);
lemma_inv_l0_driver_compose (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${orig_re}) (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${re})
"#
    );
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 400 --split_queries always")]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
    Libcrux_ml_dsa.Simd.Portable.Ntt.is_i32b_polynomial (2 * v $FIELD_MAX) ${re}
"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    Libcrux_ml_dsa.Simd.Portable.Ntt.is_i32b_polynomial (4 * v $FIELD_MAX) ${re}_future /\
    (let in_flat = Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${re}) in
     let out_flat = Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${re}_future) in
     let spec = Hacspec_ml_dsa.Ntt.intt_layer in_flat (mk_usize 1) in
     forall (i: nat). i < 256 ==>
       (v (Seq.index out_flat i)) % 8380417 == (v (Seq.index spec i)) % 8380417)
"#) )]
fn invert_ntt_at_layer_1(re: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT]) {
    #[inline(always)]
    #[hax_lib::fstar::options("--z3rlimit 100")]
    #[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
    #[hax_lib::requires(fstar!(r#"
        v index < v $SIMD_UNITS_IN_RING_ELEMENT /\
        Spec.Utils.is_i32b_array_opaque (2 * v $FIELD_MAX) 
            (Seq.index ${re} (v index)).f_values /\
        Spec.Utils.is_i32b 4190208 $zeta_00 /\
        Spec.Utils.is_i32b 4190208 $zeta_01
    "#))]
    #[hax_lib::ensures(|_| fstar!(r#"
        Spec.Utils.modifies1_32 ${re} ${re}_future $index /\
        Spec.Utils.is_i32b_array_opaque (4 * v $FIELD_MAX)
            (Seq.index ${re}_future (v $index)).f_values /\
        unit_fe_post_inv_l1 (Seq.index ${re} (v $index)).f_values
                        (Seq.index ${re}_future (v $index)).f_values $zeta_00 $zeta_01
     "#))]
    fn round(
        re: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT],
        index: usize,
        zeta_00: i32,
        zeta_01: i32,
    ) {
        hax_lib::fstar!(
            "reveal_opaque (`%Spec.Utils.is_i32b_array_opaque) (Spec.Utils.is_i32b_array_opaque)"
        );
        simd_unit_invert_ntt_at_layer_1(&mut re[index], zeta_00, zeta_01);
        hax_lib::fstar!("reveal_opaque (`%unit_fe_post_inv_l1) unit_fe_post_inv_l1");
    }

    #[cfg(hax)]
    let orig_re = re.clone();

    round(re, 0, 3839961, -3628969);
    round(re, 1, -3881060, -3019102);
    round(re, 2, -1439742, -812732);
    round(re, 3, -1584928, 1285669);
    round(re, 4, 1341330, 1315589);
    round(re, 5, -177440, -2409325);
    round(re, 6, -1851402, 3159746);
    round(re, 7, -3553272, 189548);
    round(re, 8, -1316856, 759969);
    round(re, 9, -210977, 2389356);
    round(re, 10, -3249728, 1653064);
    round(re, 11, -8578, -3724342);
    round(re, 12, 3958618, 904516);
    round(re, 13, -1100098, 44288);
    round(re, 14, 3097992, 508951);
    round(re, 15, 264944, -3343383);
    round(re, 16, -1430430, 1852771);
    round(re, 17, 1349076, -381987);
    round(re, 18, -1308169, -22981);
    round(re, 19, -1228525, -671102);
    round(re, 20, -2477047, -411027);
    round(re, 21, -3693493, -2967645);
    round(re, 22, 2715295, 2147896);
    round(re, 23, -983419, 3412210);
    round(re, 24, 126922, -3632928);
    round(re, 25, -3157330, -3190144);
    round(re, 26, -1000202, -4083598);
    round(re, 27, 1939314, -1257611);
    round(re, 28, -1585221, 2176455);
    round(re, 29, 3475950, -1452451);
    round(re, 30, -3041255, -3677745);
    round(re, 31, -1528703, -3930395);
    hax_lib::fstar!(
        r#"
assert_norm (Spec.MLDSA.NttConstants.zeta_r 64 == (-3930395));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 65 == (-1528703));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 66 == (-3677745));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 67 == (-3041255));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 68 == (-1452451));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 69 == 3475950);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 70 == 2176455);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 71 == (-1585221));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 72 == (-1257611));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 73 == 1939314);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 74 == (-4083598));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 75 == (-1000202));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 76 == (-3190144));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 77 == (-3157330));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 78 == (-3632928));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 79 == 126922);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 80 == 3412210);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 81 == (-983419));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 82 == 2147896);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 83 == 2715295);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 84 == (-2967645));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 85 == (-3693493));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 86 == (-411027));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 87 == (-2477047));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 88 == (-671102));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 89 == (-1228525));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 90 == (-22981));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 91 == (-1308169));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 92 == (-381987));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 93 == 1349076);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 94 == 1852771);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 95 == (-1430430));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 96 == (-3343383));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 97 == 264944);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 98 == 508951);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 99 == 3097992);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 100 == 44288);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 101 == (-1100098));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 102 == 904516);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 103 == 3958618);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 104 == (-3724342));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 105 == (-8578));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 106 == 1653064);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 107 == (-3249728));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 108 == 2389356);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 109 == (-210977));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 110 == 759969);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 111 == (-1316856));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 112 == 189548);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 113 == (-3553272));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 114 == 3159746);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 115 == (-1851402));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 116 == (-2409325));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 117 == (-177440));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 118 == 1315589);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 119 == 1341330);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 120 == 1285669);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 121 == (-1584928));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 122 == (-812732));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 123 == (-1439742));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 124 == (-3019102));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 125 == (-3881060));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 126 == (-3628969));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 127 == 3839961);
lemma_inv_l1_driver_compose (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${orig_re}) (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${re})
"#
    );
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 400 --split_queries always")]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
    Libcrux_ml_dsa.Simd.Portable.Ntt.is_i32b_polynomial (4 * v $FIELD_MAX) ${re}
"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    Libcrux_ml_dsa.Simd.Portable.Ntt.is_i32b_polynomial (8 * v $FIELD_MAX) ${re}_future /\
    (let in_flat = Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${re}) in
     let out_flat = Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${re}_future) in
     let spec = Hacspec_ml_dsa.Ntt.intt_layer in_flat (mk_usize 2) in
     forall (i: nat). i < 256 ==>
       (v (Seq.index out_flat i)) % 8380417 == (v (Seq.index spec i)) % 8380417)
"#) )]
fn invert_ntt_at_layer_2(re: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT]) {
    #[inline(always)]
    #[hax_lib::fstar::options("--z3rlimit 100")]
    #[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
    #[hax_lib::requires(fstar!(r#"
        v index < v $SIMD_UNITS_IN_RING_ELEMENT /\
        Spec.Utils.is_i32b_array_opaque (4 * v $FIELD_MAX) 
            (Seq.index ${re} (v index)).f_values /\
        Spec.Utils.is_i32b 4190208 $zeta1
    "#))]
    #[hax_lib::ensures(|_| fstar!(r#"
        Spec.Utils.modifies1_32 ${re} ${re}_future $index /\
        Spec.Utils.is_i32b_array_opaque (8 * v $FIELD_MAX)
            (Seq.index ${re}_future (v $index)).f_values /\
        unit_fe_post_inv_l2 (Seq.index ${re} (v $index)).f_values
                        (Seq.index ${re}_future (v $index)).f_values $zeta1
     "#))]
    fn round(re: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT], index: usize, zeta1: i32) {
        hax_lib::fstar!(
            "reveal_opaque (`%Spec.Utils.is_i32b_array_opaque) (Spec.Utils.is_i32b_array_opaque)"
        );
        simd_unit_invert_ntt_at_layer_2(&mut re[index], zeta1);
        hax_lib::fstar!("reveal_opaque (`%unit_fe_post_inv_l2) unit_fe_post_inv_l2");
    }

    #[cfg(hax)]
    let orig_re = re.clone();

    round(re, 0, -2797779);
    round(re, 1, 2071892);
    round(re, 2, -2556880);
    round(re, 3, 3900724);
    round(re, 4, 3881043);
    round(re, 5, 954230);
    round(re, 6, 531354);
    round(re, 7, 811944);
    round(re, 8, 3699596);
    round(re, 9, -1600420);
    round(re, 10, -2140649);
    round(re, 11, 3507263);
    round(re, 12, -3821735);
    round(re, 13, 3505694);
    round(re, 14, -1643818);
    round(re, 15, -1699267);
    round(re, 16, -539299);
    round(re, 17, 2348700);
    round(re, 18, -300467);
    round(re, 19, 3539968);
    round(re, 20, -2867647);
    round(re, 21, 3574422);
    round(re, 22, -3043716);
    round(re, 23, -3861115);
    round(re, 24, 3915439);
    round(re, 25, -2537516);
    round(re, 26, -3592148);
    round(re, 27, -1661693);
    round(re, 28, 3530437);
    round(re, 29, 3077325);
    round(re, 30, 95776);
    round(re, 31, 2706023);
    hax_lib::fstar!(
        r#"
assert_norm (Spec.MLDSA.NttConstants.zeta_r 32 == 2706023);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 33 == 95776);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 34 == 3077325);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 35 == 3530437);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 36 == (-1661693));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 37 == (-3592148));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 38 == (-2537516));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 39 == 3915439);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 40 == (-3861115));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 41 == (-3043716));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 42 == 3574422);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 43 == (-2867647));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 44 == 3539968);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 45 == (-300467));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 46 == 2348700);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 47 == (-539299));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 48 == (-1699267));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 49 == (-1643818));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 50 == 3505694);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 51 == (-3821735));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 52 == 3507263);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 53 == (-2140649));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 54 == (-1600420));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 55 == 3699596);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 56 == 811944);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 57 == 531354);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 58 == 954230);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 59 == 3881043);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 60 == 3900724);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 61 == (-2556880));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 62 == 2071892);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 63 == (-2797779));
lemma_inv_l2_driver_compose (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${orig_re}) (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${re})
"#
    );
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 600 --split_queries always")]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
    (v $STEP_BY > 0) /\
    (v $OFFSET + v $STEP_BY < v $SIMD_UNITS_IN_RING_ELEMENT) /\
    (v $OFFSET + 2 * v $STEP_BY <= v $SIMD_UNITS_IN_RING_ELEMENT) /\
    (Spec.Utils.forall32 (fun i -> (i >= v $OFFSET /\ i < (v $OFFSET + 2 * v $STEP_BY)) ==>
              Spec.Utils.is_i32b_array_opaque 
                ((layer_bound_factor $STEP_BY) * v $FIELD_MAX)
                (Seq.index ${re} i).f_values)) /\
    Spec.Utils.is_i32b 4190208 $ZETA
"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    Spec.Utils.modifies_range_32 ${re} ${re}_future $OFFSET (${OFFSET + STEP_BY + STEP_BY}) /\
    (Spec.Utils.forall32 (fun i -> (i >= v $OFFSET /\ i < (v $OFFSET + 2 * v $STEP_BY)) ==>
              Spec.Utils.is_i32b_array_opaque
                (2 * (layer_bound_factor $STEP_BY) * v $FIELD_MAX)
                (Seq.index ${re}_future i).f_values)) /\
    (Spec.Utils.forall32 (fun u -> (u >= v $OFFSET /\ u < v $OFFSET + v $STEP_BY) ==>
              unit_fe_post_inv_cross (Seq.index ${re} u).f_values
                                     (Seq.index ${re} (u + v $STEP_BY)).f_values
                                     (Seq.index ${re}_future u).f_values
                                     (Seq.index ${re}_future (u + v $STEP_BY)).f_values
                                     $ZETA))
"#))]
fn outer_3_plus<const OFFSET: usize, const STEP_BY: usize, const ZETA: i32>(
    re: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT],
) {
    #[cfg(hax)]
    let orig_re = re.clone();

    for j in OFFSET..OFFSET + STEP_BY {
        hax_lib::loop_invariant!(|j: usize| fstar!(
            r#"
            (Spec.Utils.modifies_range2_32 $orig_re $re
                $OFFSET $j ($OFFSET +! $STEP_BY) ($j +! $STEP_BY)) /\
            (Spec.Utils.forall32 (fun i -> ((i >= v $OFFSET /\ i < v $j) \/
                        (i >= v $OFFSET + v $STEP_BY /\ i < v $j + v $STEP_BY)) ==>
                Spec.Utils.is_i32b_array_opaque
                    (2 * (layer_bound_factor $STEP_BY) * v $FIELD_MAX)
                    (Seq.index ${re} i).f_values)) /\
            (Spec.Utils.forall32 (fun u -> (u >= v $OFFSET /\ u < v $j) ==>
                unit_fe_post_inv_cross (Seq.index $orig_re u).f_values
                                       (Seq.index $orig_re (u + v $STEP_BY)).f_values
                                       (Seq.index ${re} u).f_values
                                       (Seq.index ${re} (u + v $STEP_BY)).f_values
                                       $ZETA))
        "#
        ));

        let rej = re[j];
        let rejs = re[j + STEP_BY];
        arithmetic::add(&mut re[j], &rejs);
        arithmetic::subtract(&mut re[j + STEP_BY], &rej);
        #[cfg(hax)]
        let tmp = re[j + STEP_BY];
        arithmetic::montgomery_multiply_by_constant(&mut re[j + STEP_BY], ZETA);

        hax_lib::fstar!("Spec.Utils.is_i32b_array_larger
            (v $FIELD_MAX) (2 * (layer_bound_factor $STEP_BY) * v $FIELD_MAX) (Seq.index re (v j + v v_STEP_BY)).f_values");
        // Discharge the cross-unit inverse FE atom via the clean bridge lemma:
        // ci_lo/ci_hi = orig_re[j]/[j+STEP_BY] (== re[j]/[j+STEP_BY] at iter start, frame);
        // co_lo/co_hi = re[j]/[j+STEP_BY]; tmp = re[j+STEP_BY] after subtract (= ci_hi - ci_lo).
        // add post: co_lo = ci_lo + ci_hi; sub post: tmp = ci_hi - ci_lo;
        // mmbc post: co_hi = mont_mul(tmp, ZETA) and the mod-q relation.
        hax_lib::fstar!(
            r#"lemma_round_inv_cross_intro
                 (Seq.index $orig_re (v $j)).f_values
                 (Seq.index $orig_re (v $j + v $STEP_BY)).f_values
                 (Seq.index ${re} (v $j)).f_values
                 (Seq.index ${re} (v $j + v $STEP_BY)).f_values
                 ${tmp}.f_values
                 $ZETA"#
        );
    }
}

#[inline(always)]
#[hax_lib::fstar::options(
    "--z3rlimit 400 --split_queries always --using_facts_from '* -Hacspec_ml_dsa.createi_lemma'"
)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
    Libcrux_ml_dsa.Simd.Portable.Ntt.is_i32b_polynomial (8 * v $FIELD_MAX) ${re}
"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    Libcrux_ml_dsa.Simd.Portable.Ntt.is_i32b_polynomial (16 * v $FIELD_MAX) ${re}_future /\
    (let in_flat = Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${re}) in
     let out_flat = Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${re}_future) in
     let spec = Hacspec_ml_dsa.Ntt.intt_layer in_flat (mk_usize 3) in
     forall (i: nat). i < 256 ==>
       (v (Seq.index out_flat i)) % 8380417 == (v (Seq.index spec i)) % 8380417)
"#) )]
fn invert_ntt_at_layer_3(re: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT]) {
    const STEP: usize = 8; // 1 << LAYER;
    const STEP_BY: usize = 1; // step / COEFFICIENTS_IN_SIMD_UNIT;

    #[cfg(hax)]
    let orig_re = re.clone();

    outer_3_plus::<{ (0 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 280005>(re);
    outer_3_plus::<{ (1 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 4010497>(re);
    outer_3_plus::<{ (2 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -19422>(re);
    outer_3_plus::<{ (3 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 1757237>(re);
    outer_3_plus::<{ (4 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -3277672>(re);
    outer_3_plus::<{ (5 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -1399561>(re);
    outer_3_plus::<{ (6 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -3859737>(re);
    outer_3_plus::<{ (7 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -2118186>(re);
    outer_3_plus::<{ (8 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -2108549>(re);
    outer_3_plus::<{ (9 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 2619752>(re);
    outer_3_plus::<{ (10 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -1119584>(re);
    outer_3_plus::<{ (11 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -549488>(re);
    outer_3_plus::<{ (12 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 3585928>(re);
    outer_3_plus::<{ (13 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -1079900>(re);
    outer_3_plus::<{ (14 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 1024112>(re);
    outer_3_plus::<{ (15 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 2725464>(re);

    hax_lib::fstar!(
        r#"
assert_norm (Spec.MLDSA.NttConstants.zeta_r 16 == 2725464);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 17 == 1024112);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 18 == (-1079900));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 19 == 3585928);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 20 == (-549488));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 21 == (-1119584));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 22 == 2619752);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 23 == (-2108549));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 24 == (-2118186));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 25 == (-3859737));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 26 == (-1399561));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 27 == (-3277672));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 28 == 1757237);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 29 == (-19422));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 30 == 4010497);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 31 == 280005);
// Flat-asserts: discharge each even-u inverse cross atom (orig_re vs final re) in
// ISOLATION (one frame each) so the compose lemma's forall32 precondition is
// assembled from 16 ground facts instead of a forall32-of-forall32 cascade.
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 0).f_values (Seq.index ${orig_re} 1).f_values (Seq.index ${re} 0).f_values (Seq.index ${re} 1).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 31)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 2).f_values (Seq.index ${orig_re} 3).f_values (Seq.index ${re} 2).f_values (Seq.index ${re} 3).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 30)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 4).f_values (Seq.index ${orig_re} 5).f_values (Seq.index ${re} 4).f_values (Seq.index ${re} 5).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 29)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 6).f_values (Seq.index ${orig_re} 7).f_values (Seq.index ${re} 6).f_values (Seq.index ${re} 7).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 28)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 8).f_values (Seq.index ${orig_re} 9).f_values (Seq.index ${re} 8).f_values (Seq.index ${re} 9).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 27)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 10).f_values (Seq.index ${orig_re} 11).f_values (Seq.index ${re} 10).f_values (Seq.index ${re} 11).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 26)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 12).f_values (Seq.index ${orig_re} 13).f_values (Seq.index ${re} 12).f_values (Seq.index ${re} 13).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 25)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 14).f_values (Seq.index ${orig_re} 15).f_values (Seq.index ${re} 14).f_values (Seq.index ${re} 15).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 24)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 16).f_values (Seq.index ${orig_re} 17).f_values (Seq.index ${re} 16).f_values (Seq.index ${re} 17).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 23)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 18).f_values (Seq.index ${orig_re} 19).f_values (Seq.index ${re} 18).f_values (Seq.index ${re} 19).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 22)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 20).f_values (Seq.index ${orig_re} 21).f_values (Seq.index ${re} 20).f_values (Seq.index ${re} 21).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 21)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 22).f_values (Seq.index ${orig_re} 23).f_values (Seq.index ${re} 22).f_values (Seq.index ${re} 23).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 20)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 24).f_values (Seq.index ${orig_re} 25).f_values (Seq.index ${re} 24).f_values (Seq.index ${re} 25).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 19)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 26).f_values (Seq.index ${orig_re} 27).f_values (Seq.index ${re} 26).f_values (Seq.index ${re} 27).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 18)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 28).f_values (Seq.index ${orig_re} 29).f_values (Seq.index ${re} 28).f_values (Seq.index ${re} 29).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 17)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 30).f_values (Seq.index ${orig_re} 31).f_values (Seq.index ${re} 30).f_values (Seq.index ${re} 31).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 16)));
lemma_inv_l3_cross_driver_compose ${orig_re} ${re}
"#
    );
}

#[inline(always)]
#[hax_lib::fstar::options(
    "--z3rlimit 400 --split_queries always --using_facts_from '* -Hacspec_ml_dsa.createi_lemma'"
)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
    Libcrux_ml_dsa.Simd.Portable.Ntt.is_i32b_polynomial (16 * v $FIELD_MAX) ${re}
"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    Libcrux_ml_dsa.Simd.Portable.Ntt.is_i32b_polynomial (32 * v $FIELD_MAX) ${re}_future /\
    (let in_flat = Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${re}) in
     let out_flat = Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${re}_future) in
     let spec = Hacspec_ml_dsa.Ntt.intt_layer in_flat (mk_usize 4) in
     forall (i: nat). i < 256 ==>
       (v (Seq.index out_flat i)) % 8380417 == (v (Seq.index spec i)) % 8380417)
"#) )]
fn invert_ntt_at_layer_4(re: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT]) {
    const STEP: usize = 16; // 1 << LAYER;
    const STEP_BY: usize = 2; // step / COEFFICIENTS_IN_SIMD_UNIT;

    #[cfg(hax)]
    let orig_re = re.clone();

    outer_3_plus::<{ (0 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 2680103>(re);
    outer_3_plus::<{ (1 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 3111497>(re);
    outer_3_plus::<{ (2 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -2884855>(re);
    outer_3_plus::<{ (3 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 3119733>(re);
    outer_3_plus::<{ (4 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -2091905>(re);
    outer_3_plus::<{ (5 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -359251>(re);
    outer_3_plus::<{ (6 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 2353451>(re);
    outer_3_plus::<{ (7 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 1826347>(re);

    hax_lib::fstar!(
        r#"
assert_norm (Spec.MLDSA.NttConstants.zeta_r 8 == 1826347);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 9 == 2353451);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 10 == (-359251));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 11 == (-2091905));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 12 == 3119733);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 13 == (-2884855));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 14 == 3111497);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 15 == 2680103);
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 0).f_values (Seq.index ${orig_re} 2).f_values (Seq.index ${re} 0).f_values (Seq.index ${re} 2).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 15)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 1).f_values (Seq.index ${orig_re} 3).f_values (Seq.index ${re} 1).f_values (Seq.index ${re} 3).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 15)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 4).f_values (Seq.index ${orig_re} 6).f_values (Seq.index ${re} 4).f_values (Seq.index ${re} 6).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 14)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 5).f_values (Seq.index ${orig_re} 7).f_values (Seq.index ${re} 5).f_values (Seq.index ${re} 7).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 14)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 8).f_values (Seq.index ${orig_re} 10).f_values (Seq.index ${re} 8).f_values (Seq.index ${re} 10).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 13)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 9).f_values (Seq.index ${orig_re} 11).f_values (Seq.index ${re} 9).f_values (Seq.index ${re} 11).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 13)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 12).f_values (Seq.index ${orig_re} 14).f_values (Seq.index ${re} 12).f_values (Seq.index ${re} 14).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 12)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 13).f_values (Seq.index ${orig_re} 15).f_values (Seq.index ${re} 13).f_values (Seq.index ${re} 15).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 12)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 16).f_values (Seq.index ${orig_re} 18).f_values (Seq.index ${re} 16).f_values (Seq.index ${re} 18).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 11)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 17).f_values (Seq.index ${orig_re} 19).f_values (Seq.index ${re} 17).f_values (Seq.index ${re} 19).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 11)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 20).f_values (Seq.index ${orig_re} 22).f_values (Seq.index ${re} 20).f_values (Seq.index ${re} 22).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 10)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 21).f_values (Seq.index ${orig_re} 23).f_values (Seq.index ${re} 21).f_values (Seq.index ${re} 23).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 10)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 24).f_values (Seq.index ${orig_re} 26).f_values (Seq.index ${re} 24).f_values (Seq.index ${re} 26).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 9)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 25).f_values (Seq.index ${orig_re} 27).f_values (Seq.index ${re} 25).f_values (Seq.index ${re} 27).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 9)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 28).f_values (Seq.index ${orig_re} 30).f_values (Seq.index ${re} 28).f_values (Seq.index ${re} 30).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 8)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 29).f_values (Seq.index ${orig_re} 31).f_values (Seq.index ${re} 29).f_values (Seq.index ${re} 31).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 8)));
lemma_inv_l4_cross_driver_compose ${orig_re} ${re}
"#
    );
}

#[inline(always)]
#[hax_lib::fstar::options(
    "--z3rlimit 400 --split_queries always --using_facts_from '* -Hacspec_ml_dsa.createi_lemma'"
)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
    Libcrux_ml_dsa.Simd.Portable.Ntt.is_i32b_polynomial (32 * v $FIELD_MAX) ${re}
"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    Libcrux_ml_dsa.Simd.Portable.Ntt.is_i32b_polynomial (64 * v $FIELD_MAX) ${re}_future /\
    (let in_flat = Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${re}) in
     let out_flat = Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${re}_future) in
     let spec = Hacspec_ml_dsa.Ntt.intt_layer in_flat (mk_usize 5) in
     forall (i: nat). i < 256 ==>
       (v (Seq.index out_flat i)) % 8380417 == (v (Seq.index spec i)) % 8380417)
"#) )]
fn invert_ntt_at_layer_5(re: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT]) {
    const STEP: usize = 32; // 1 << LAYER;
    const STEP_BY: usize = 4; // step / COEFFICIENTS_IN_SIMD_UNIT;

    #[cfg(hax)]
    let orig_re = re.clone();

    outer_3_plus::<{ (0 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 466468>(re);
    outer_3_plus::<{ (1 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -876248>(re);
    outer_3_plus::<{ (2 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -777960>(re);
    outer_3_plus::<{ (3 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 237124>(re);

    hax_lib::fstar!(
        r#"
assert_norm (Spec.MLDSA.NttConstants.zeta_r 4 == 237124);
assert_norm (Spec.MLDSA.NttConstants.zeta_r 5 == (-777960));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 6 == (-876248));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 7 == 466468);
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 0).f_values (Seq.index ${orig_re} 4).f_values (Seq.index ${re} 0).f_values (Seq.index ${re} 4).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 7)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 1).f_values (Seq.index ${orig_re} 5).f_values (Seq.index ${re} 1).f_values (Seq.index ${re} 5).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 7)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 2).f_values (Seq.index ${orig_re} 6).f_values (Seq.index ${re} 2).f_values (Seq.index ${re} 6).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 7)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 3).f_values (Seq.index ${orig_re} 7).f_values (Seq.index ${re} 3).f_values (Seq.index ${re} 7).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 7)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 8).f_values (Seq.index ${orig_re} 12).f_values (Seq.index ${re} 8).f_values (Seq.index ${re} 12).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 6)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 9).f_values (Seq.index ${orig_re} 13).f_values (Seq.index ${re} 9).f_values (Seq.index ${re} 13).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 6)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 10).f_values (Seq.index ${orig_re} 14).f_values (Seq.index ${re} 10).f_values (Seq.index ${re} 14).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 6)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 11).f_values (Seq.index ${orig_re} 15).f_values (Seq.index ${re} 11).f_values (Seq.index ${re} 15).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 6)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 16).f_values (Seq.index ${orig_re} 20).f_values (Seq.index ${re} 16).f_values (Seq.index ${re} 20).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 5)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 17).f_values (Seq.index ${orig_re} 21).f_values (Seq.index ${re} 17).f_values (Seq.index ${re} 21).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 5)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 18).f_values (Seq.index ${orig_re} 22).f_values (Seq.index ${re} 18).f_values (Seq.index ${re} 22).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 5)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 19).f_values (Seq.index ${orig_re} 23).f_values (Seq.index ${re} 19).f_values (Seq.index ${re} 23).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 5)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 24).f_values (Seq.index ${orig_re} 28).f_values (Seq.index ${re} 24).f_values (Seq.index ${re} 28).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 4)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 25).f_values (Seq.index ${orig_re} 29).f_values (Seq.index ${re} 25).f_values (Seq.index ${re} 29).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 4)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 26).f_values (Seq.index ${orig_re} 30).f_values (Seq.index ${re} 26).f_values (Seq.index ${re} 30).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 4)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 27).f_values (Seq.index ${orig_re} 31).f_values (Seq.index ${re} 27).f_values (Seq.index ${re} 31).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 4)));
lemma_inv_l5_cross_driver_compose ${orig_re} ${re}
"#
    );
}

#[inline(always)]
#[hax_lib::fstar::options(
    "--z3rlimit 400 --split_queries always --using_facts_from '* -Hacspec_ml_dsa.createi_lemma'"
)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
    Libcrux_ml_dsa.Simd.Portable.Ntt.is_i32b_polynomial (64 * v $FIELD_MAX) ${re}
"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    Libcrux_ml_dsa.Simd.Portable.Ntt.is_i32b_polynomial (128 * v $FIELD_MAX) ${re}_future /\
    (let in_flat = Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${re}) in
     let out_flat = Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${re}_future) in
     let spec = Hacspec_ml_dsa.Ntt.intt_layer in_flat (mk_usize 6) in
     forall (i: nat). i < 256 ==>
       (v (Seq.index out_flat i)) % 8380417 == (v (Seq.index spec i)) % 8380417)
"#) )]
fn invert_ntt_at_layer_6(re: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT]) {
    const STEP: usize = 64; // 1 << LAYER;
    const STEP_BY: usize = 8; // step / COEFFICIENTS_IN_SIMD_UNIT;

    #[cfg(hax)]
    let orig_re = re.clone();

    outer_3_plus::<{ (0 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -518909>(re);
    outer_3_plus::<{ (1 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -2608894>(re);

    hax_lib::fstar!(
        r#"
assert_norm (Spec.MLDSA.NttConstants.zeta_r 2 == (-2608894));
assert_norm (Spec.MLDSA.NttConstants.zeta_r 3 == (-518909));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 0).f_values (Seq.index ${orig_re} 8).f_values (Seq.index ${re} 0).f_values (Seq.index ${re} 8).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 3)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 1).f_values (Seq.index ${orig_re} 9).f_values (Seq.index ${re} 1).f_values (Seq.index ${re} 9).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 3)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 2).f_values (Seq.index ${orig_re} 10).f_values (Seq.index ${re} 2).f_values (Seq.index ${re} 10).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 3)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 3).f_values (Seq.index ${orig_re} 11).f_values (Seq.index ${re} 3).f_values (Seq.index ${re} 11).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 3)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 4).f_values (Seq.index ${orig_re} 12).f_values (Seq.index ${re} 4).f_values (Seq.index ${re} 12).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 3)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 5).f_values (Seq.index ${orig_re} 13).f_values (Seq.index ${re} 5).f_values (Seq.index ${re} 13).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 3)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 6).f_values (Seq.index ${orig_re} 14).f_values (Seq.index ${re} 6).f_values (Seq.index ${re} 14).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 3)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 7).f_values (Seq.index ${orig_re} 15).f_values (Seq.index ${re} 7).f_values (Seq.index ${re} 15).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 3)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 16).f_values (Seq.index ${orig_re} 24).f_values (Seq.index ${re} 16).f_values (Seq.index ${re} 24).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 2)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 17).f_values (Seq.index ${orig_re} 25).f_values (Seq.index ${re} 17).f_values (Seq.index ${re} 25).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 2)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 18).f_values (Seq.index ${orig_re} 26).f_values (Seq.index ${re} 18).f_values (Seq.index ${re} 26).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 2)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 19).f_values (Seq.index ${orig_re} 27).f_values (Seq.index ${re} 19).f_values (Seq.index ${re} 27).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 2)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 20).f_values (Seq.index ${orig_re} 28).f_values (Seq.index ${re} 20).f_values (Seq.index ${re} 28).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 2)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 21).f_values (Seq.index ${orig_re} 29).f_values (Seq.index ${re} 21).f_values (Seq.index ${re} 29).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 2)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 22).f_values (Seq.index ${orig_re} 30).f_values (Seq.index ${re} 22).f_values (Seq.index ${re} 30).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 2)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 23).f_values (Seq.index ${orig_re} 31).f_values (Seq.index ${re} 23).f_values (Seq.index ${re} 31).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 2)));
lemma_inv_l6_cross_driver_compose ${orig_re} ${re}
"#
    );
}

#[inline(always)]
#[hax_lib::fstar::options(
    "--z3rlimit 400 --split_queries always --using_facts_from '* -Hacspec_ml_dsa.createi_lemma'"
)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
    Libcrux_ml_dsa.Simd.Portable.Ntt.is_i32b_polynomial (128 * v $FIELD_MAX) ${re}
"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    Libcrux_ml_dsa.Simd.Portable.Ntt.is_i32b_polynomial (256 * v $FIELD_MAX) ${re}_future /\
    (let in_flat = Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${re}) in
     let out_flat = Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${re}_future) in
     let spec = Hacspec_ml_dsa.Ntt.intt_layer in_flat (mk_usize 7) in
     forall (i: nat). i < 256 ==>
       (v (Seq.index out_flat i)) % 8380417 == (v (Seq.index spec i)) % 8380417)
"#) )]
fn invert_ntt_at_layer_7(re: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT]) {
    const STEP: usize = 128; // 1 << LAYER;
    const STEP_BY: usize = 16; // step / COEFFICIENTS_IN_SIMD_UNIT;

    #[cfg(hax)]
    let orig_re = re.clone();

    outer_3_plus::<{ (0 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 25847>(re);

    hax_lib::fstar!(
        r#"
assert_norm (Spec.MLDSA.NttConstants.zeta_r 1 == 25847);
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 0).f_values (Seq.index ${orig_re} 16).f_values (Seq.index ${re} 0).f_values (Seq.index ${re} 16).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 1)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 1).f_values (Seq.index ${orig_re} 17).f_values (Seq.index ${re} 1).f_values (Seq.index ${re} 17).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 1)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 2).f_values (Seq.index ${orig_re} 18).f_values (Seq.index ${re} 2).f_values (Seq.index ${re} 18).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 1)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 3).f_values (Seq.index ${orig_re} 19).f_values (Seq.index ${re} 3).f_values (Seq.index ${re} 19).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 1)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 4).f_values (Seq.index ${orig_re} 20).f_values (Seq.index ${re} 4).f_values (Seq.index ${re} 20).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 1)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 5).f_values (Seq.index ${orig_re} 21).f_values (Seq.index ${re} 5).f_values (Seq.index ${re} 21).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 1)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 6).f_values (Seq.index ${orig_re} 22).f_values (Seq.index ${re} 6).f_values (Seq.index ${re} 22).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 1)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 7).f_values (Seq.index ${orig_re} 23).f_values (Seq.index ${re} 7).f_values (Seq.index ${re} 23).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 1)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 8).f_values (Seq.index ${orig_re} 24).f_values (Seq.index ${re} 8).f_values (Seq.index ${re} 24).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 1)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 9).f_values (Seq.index ${orig_re} 25).f_values (Seq.index ${re} 9).f_values (Seq.index ${re} 25).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 1)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 10).f_values (Seq.index ${orig_re} 26).f_values (Seq.index ${re} 10).f_values (Seq.index ${re} 26).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 1)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 11).f_values (Seq.index ${orig_re} 27).f_values (Seq.index ${re} 11).f_values (Seq.index ${re} 27).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 1)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 12).f_values (Seq.index ${orig_re} 28).f_values (Seq.index ${re} 12).f_values (Seq.index ${re} 28).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 1)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 13).f_values (Seq.index ${orig_re} 29).f_values (Seq.index ${re} 13).f_values (Seq.index ${re} 29).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 1)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 14).f_values (Seq.index ${orig_re} 30).f_values (Seq.index ${re} 14).f_values (Seq.index ${re} 30).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 1)));
assert (unit_fe_post_inv_cross (Seq.index ${orig_re} 15).f_values (Seq.index ${orig_re} 31).f_values (Seq.index ${re} 15).f_values (Seq.index ${re} 31).f_values (mk_i32 (Spec.MLDSA.NttConstants.zeta_r 1)));
lemma_inv_l7_cross_driver_compose ${orig_re} ${re}
"#
    );
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 400 --split_queries always")]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
    Libcrux_ml_dsa.Simd.Portable.Ntt.is_i32b_polynomial (256 * v $FIELD_MAX) ${re}
"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    Libcrux_ml_dsa.Simd.Portable.Ntt.is_i32b_polynomial 4211177 ${re}_future /\
    (let in_flat = Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${re}) in
     let out_flat = Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${re}_future) in
     forall (j:nat). j < 256 ==>
       (v (Seq.index out_flat j)) % 8380417 == (16382 * v (Seq.index in_flat j)) % 8380417)
"#) )]
fn scale_montgomery(re: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT]) {
    #[cfg(hax)]
    let orig = re.clone();
    hax_lib::fstar!(
        r#"reveal_opaque (`%Libcrux_ml_dsa.Simd.Portable.Ntt.is_i32b_polynomial) (Libcrux_ml_dsa.Simd.Portable.Ntt.is_i32b_polynomial (256 * v $FIELD_MAX) ${re})"#
    );
    for i in 0..re.len() {
        hax_lib::loop_invariant!(|i: usize| fstar!(
            r#"
            (forall (k:nat).
              k < v $i ==>
              Spec.Utils.is_i32b_array_opaque 4211177
                (Seq.index $re k).f_values /\
              chunk_scaled (Seq.index ${orig} k).f_values (Seq.index $re k).f_values) /\
            (forall (k:nat).
              (k >= v $i /\ k < 32) ==>
              Spec.Utils.is_i32b_array_opaque (256 * v $FIELD_MAX)
                (Seq.index $re k).f_values /\
              (Seq.index $re k) == (Seq.index ${orig} k)))
        "#
        ));
        // After invert_ntt_at_layer, elements are of the form a * MONTGOMERY_R^{-1}
        // we multiply by (MONTGOMERY_R^2) * (1/2^8) mod Q = 41,978 to both:
        //
        // - Divide the elements by 256 and
        // - Convert the elements form montgomery domain to the standard domain.
        arithmetic::montgomery_multiply_by_constant(&mut re[i], 41_978);
        // Tight 4211177 output bound: the input chunk orig[i] is bounded by
        // 256*FIELD_MAX (k>=i invariant clause) and montgomery's per-lane post
        // gives re[i] = mont_mul(orig[i], 41978); the tight-bound lemma reduces
        // 256*FIELD_MAX to the centered 4211177.
        hax_lib::fstar!(
            r#"lemma_scale_chunk_tight_bound (Seq.index ${orig} (v $i)).f_values (Seq.index $re (v $i)).f_values"#
        );
        // montgomery's per-lane (Spec.MLDSA.Math.mod_q ...) post -> the opaque
        // chunk_scaled atom (input chunk is orig[i] by the k>=i clause).
        hax_lib::fstar!(
            r#"lemma_establish_chunk_scaled (Seq.index ${orig} (v $i)).f_values (Seq.index $re (v $i)).f_values"#
        );
    }
    hax_lib::fstar!(
        r#"reveal_opaque (`%Libcrux_ml_dsa.Simd.Portable.Ntt.is_i32b_polynomial) (Libcrux_ml_dsa.Simd.Portable.Ntt.is_i32b_polynomial 4211177 ${re})"#
    );
    // Lift the per-chunk 16382-scaling (loop post) to the flat-poly view.
    hax_lib::fstar!(r#"lemma_scale_driver ${orig} ${re}"#);
}

#[inline(always)]
#[hax_lib::fstar::options("--z3rlimit 400 --split_queries always")]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
#[hax_lib::requires(fstar!(r#"
    Libcrux_ml_dsa.Simd.Portable.Ntt.is_i32b_polynomial (v $FIELD_MAX) ${re}
"#))]
#[hax_lib::ensures(|_| fstar!(r#"
    Libcrux_ml_dsa.Simd.Portable.Ntt.is_i32b_polynomial 4211177 ${re}_future /\
    (let in_flat = Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${re}) in
     let out_flat = Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${re}_future) in
     forall (i: nat). i < 256 ==>
       (v (Seq.index out_flat i)) % 8380417 ==
       (v (Seq.index (to_mont (Hacspec_ml_dsa.Ntt.intt in_flat)) i)) % 8380417)
"#) )]
pub(crate) fn invert_ntt_montgomery(re: &mut [Coefficients; SIMD_UNITS_IN_RING_ELEMENT]) {
    #[cfg(hax)]
    let s0 = re.clone();
    invert_ntt_at_layer_0(re);
    #[cfg(hax)]
    let s1 = re.clone();
    invert_ntt_at_layer_1(re);
    #[cfg(hax)]
    let s2 = re.clone();
    invert_ntt_at_layer_2(re);
    #[cfg(hax)]
    let s3 = re.clone();
    invert_ntt_at_layer_3(re);
    #[cfg(hax)]
    let s4 = re.clone();
    invert_ntt_at_layer_4(re);
    #[cfg(hax)]
    let s5 = re.clone();
    invert_ntt_at_layer_5(re);
    #[cfg(hax)]
    let s6 = re.clone();
    invert_ntt_at_layer_6(re);
    #[cfg(hax)]
    let s7 = re.clone();
    invert_ntt_at_layer_7(re);
    #[cfg(hax)]
    let s8 = re.clone();
    hax_lib::fstar!(
        r#"
lemma_intt_compose_8
  (Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${s0}))
  (Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${s1}))
  (Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${s2}))
  (Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${s3}))
  (Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${s4}))
  (Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${s5}))
  (Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${s6}))
  (Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${s7}))
  (Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${s8}))
"#
    );
    scale_montgomery(re);
    // out ≡ 16382·s8 (scale_montgomery) and s8 ≡ intt_unscaled(s0) (compose)
    // ⟹ out ≡ to_mont(intt s0) (mod q).
    hax_lib::fstar!(
        r#"
lemma_invert_top
  (Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${s0}))
  (Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${s8}))
  (Hacspec_ml_dsa.Commute.Chunk.simd_units_to_array (Libcrux_ml_dsa.Simd.Portable.Ntt.chunks_of_re ${re}))
"#
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ntt::reduce, polynomial::PolynomialRingElement, simd::traits::FIELD_MODULUS};

    #[test]
    fn inv_ntt_unreduced_max() {
        let mut re = PolynomialRingElement::<crate::simd::portable::PortableSIMDUnit>::zero();
        for simd_unit in re.simd_units.iter_mut() {
            for i in 0..8 {
                simd_unit.values[i] = FIELD_MODULUS + (FIELD_MODULUS / 1024) + 6;
            }
        }
        let _ = core::hint::black_box(invert_ntt_montgomery(&mut re.simd_units));
    }

    #[test]
    #[should_panic]
    fn inv_ntt_unreduced_panic() {
        let mut re1 = PolynomialRingElement::<crate::simd::portable::PortableSIMDUnit>::zero();
        for simd_unit in re1.simd_units.iter_mut() {
            for i in 0..8 {
                simd_unit.values[i] = FIELD_MODULUS + (FIELD_MODULUS / 1024) + 7;
            }
        }
        core::hint::black_box(invert_ntt_montgomery(&mut re1.simd_units)); // In debug mode this will panic since the intermediate values overflow.

        let mut re2 = PolynomialRingElement::<crate::simd::portable::PortableSIMDUnit>::zero();
        for simd_unit in re2.simd_units.iter_mut() {
            for i in 0..8 {
                simd_unit.values[i] = FIELD_MODULUS + (FIELD_MODULUS / 1024) + 7;
            }
        }
        reduce(&mut re2);
        core::hint::black_box(invert_ntt_montgomery(&mut re2.simd_units));

        // In release mode, one of the checks below will panic, since
        // the intermediate values silently overflowed, producing an
        // incorrect result.
        for (i, simd_unit) in re2.simd_units.iter().enumerate() {
            for (j, reference_coeff) in simd_unit.values.iter().enumerate() {
                assert_eq!(*reference_coeff, re1.simd_units[i].values[j])
            }
        }
    }

    #[test]
    fn inv_ntt_reduced() {
        let mut re = PolynomialRingElement::<crate::simd::portable::PortableSIMDUnit>::zero();
        for simd_unit in re.simd_units.iter_mut() {
            for i in 0..8 {
                simd_unit.values[i] = FIELD_MODULUS + (FIELD_MODULUS / 1024) + 7;
            }
        }
        reduce(&mut re);
        let _ = core::hint::black_box(invert_ntt_montgomery(&mut re.simd_units));
    }

    #[test]
    fn inv_ntt_reduced_large() {
        let mut re = PolynomialRingElement::<crate::simd::portable::PortableSIMDUnit>::zero();
        for simd_unit in re.simd_units.iter_mut() {
            for i in 0..8 {
                simd_unit.values[i] = FIELD_MODULUS * 8;
            }
        }
        reduce(&mut re);
        let _ = core::hint::black_box(invert_ntt_montgomery(&mut re.simd_units));
    }
}
