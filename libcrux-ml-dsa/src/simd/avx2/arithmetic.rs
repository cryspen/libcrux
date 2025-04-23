use crate::{
    constants::{BITS_IN_LOWER_PART_OF_T, GAMMA2_V261_888, GAMMA2_V95_232},
    simd::traits::{FIELD_MODULUS, INVERSE_OF_MODULUS_MOD_MONTGOMERY_R},
};

use libcrux_intrinsics::avx2::*;

use super::Gamma2;

#[inline(always)]
fn to_unsigned_representatives_ret(t: &Vec256) -> Vec256 {
    let signs = mm256_srai_epi32::<31>(*t);
    let conditional_add_field_modulus = mm256_and_si256(signs, mm256_set1_epi32(FIELD_MODULUS));

    mm256_add_epi32(*t, conditional_add_field_modulus)
}

#[inline(always)]
fn to_unsigned_representatives(t: &mut Vec256) {
    *t = to_unsigned_representatives_ret(t);
}

#[inline(always)]
pub(super) fn add(lhs: &mut Vec256, rhs: &Vec256) {
    *lhs = mm256_add_epi32(*lhs, *rhs)
}

#[inline(always)]
pub(super) fn subtract(lhs: &mut Vec256, rhs: &Vec256) {
    *lhs = mm256_sub_epi32(*lhs, *rhs)
}

#[inline(always)]
pub(super) fn montgomery_multiply_by_constant(lhs: Vec256, constant: i32) -> Vec256 {
    let rhs = mm256_set1_epi32(constant);
    let field_modulus = mm256_set1_epi32(FIELD_MODULUS);
    let inverse_of_modulus_mod_montgomery_r =
        mm256_set1_epi32(INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i32);

    let prod02 = mm256_mul_epi32(lhs, rhs);
    let prod13 = mm256_mul_epi32(
        mm256_shuffle_epi32::<0b11_11_01_01>(lhs),
        mm256_shuffle_epi32::<0b11_11_01_01>(rhs),
    );

    let k02 = mm256_mul_epi32(prod02, inverse_of_modulus_mod_montgomery_r);
    let k13 = mm256_mul_epi32(prod13, inverse_of_modulus_mod_montgomery_r);

    let c02 = mm256_mul_epi32(k02, field_modulus);
    let c13 = mm256_mul_epi32(k13, field_modulus);

    let res02 = mm256_sub_epi32(prod02, c02);
    let res13 = mm256_sub_epi32(prod13, c13);
    let res02_shifted = mm256_shuffle_epi32::<0b11_11_01_01>(res02);
    let res = mm256_blend_epi32::<0b10101010>(res02_shifted, res13);
    res
}

#[cfg(hax)]
use minicore::abstractions::bitvec::int_vec_interp::{i64x4, SIMPLIFICATION_LEMMA};
#[cfg(hax)]
use minicore::abstractions::funarr::FunArray;
#[cfg(hax)]
use minicore::arch::x86::interpretations::int_vec::LIFT_LEMMA;

#[hax_lib::fstar::before(
    r#"
open FStar.Tactics
let mark_to_normalize_here t (x: t): t = x
let pw8 #t (x: Minicore.Abstractions.Funarr.t_FunArray _ t): Lemma (x == mark_to_normalize_here _ (${FunArray::<8, ()>::pointwise} x)) = admit ()
let pw4 #t (x: Minicore.Abstractions.Funarr.t_FunArray _ t): Lemma (x == mark_to_normalize_here _ (${FunArray::<4, ()>::pointwise} x)) = admit ()

/// A record that holds debugging methods.
/// This is useful for doing conditional debugging with context.
noeq type dbg = {
    print: (message:string) -> Tac unit;
    dump: (message:string) -> Tac unit;
    fail: (message:string) -> Tac unit;
    raw_sub: (subheader:string) -> Tac dbg;
    sub: (subheader:string) -> #t:Type -> (dbg -> Tac t) -> Tac t;
}

/// Make a no-op debugger
let rec mk_noop_dbg (): Tac dbg = {
    print = (fun _ -> ());
    dump = (fun _ -> ());
    fail = (fun _ -> ());
    raw_sub = (fun _ -> mk_noop_dbg ());
    sub = (fun _ f -> f (mk_noop_dbg ()));
}

/// Helper that creates a effectful active debugger.
let rec mk_dbg_with (header: string): Tac dbg =
  let format msg = "[" ^ header ^ "] " ^ msg in
  let raw_sub subheader = mk_dbg_with (if header = "" then subheader else header ^ ":" ^ subheader) in
  {
    print = (fun msg -> print (format msg));
    dump = (fun msg -> dump (format msg));
    fail = (fun msg -> fail (format msg));
    raw_sub;
    sub = (fun subheader f -> 
      let time0 = curms () in
      let d = raw_sub subheader in
      d.print "> enter";
      let result = f d in
      let time = curms () - time0 in
      d.print ("< exit ("^string_of_int (time / 1000) ^ "." ^ string_of_int ((time/100)%10) ^ "s"^")");
      result
    )
  }

/// Make a debugger if `--ext debug_circuit_norm` is set 
/// (e.g. with `OTHERFLAGS="--ext debug_circuit_norm"`)
let mk_dbg (header: string): Tac dbg
    = let ext_key = "debug_circuit_norm" in
      let debug_mode = FStar.Stubs.Tactics.V2.Builtins.ext_enabled ext_key in
      if debug_mode || true then (mk_dbg_with ext_key).raw_sub header else mk_noop_dbg ()

let run_dbg (header: string) #t (f: dbg -> Tac t): Tac t = f (mk_dbg "")

let discharge_smt_goals_now () = iterAllSMT smt_sync

/// Expects `phi` to be of the shape `squash (lhs == rhs)`, returns `(<lhs>, <rhs>)`.
let expect_eq (phi: formula): Tac (term & term) =
  match phi with
  | FStar.Reflection.V1.Formula.Comp (FStar.Reflection.V1.Formula.Eq _) lhs rhs -> (lhs, rhs)
  | _ -> fail ("Expected [_ == _], got ["^formula_to_string phi^"]")

/// Running `rewrite_subterm_in_goal subterm tactic` on a goal where `subterm`
/// appears will call once `tactic` with a goal `squash (subterm == ?u)`.
/// `tactic` needs to fill the unification variable `?u` (e.g. using a `trefl`).
let rewrite_subterm_in_goal (subterm: term) (tactic: dbg -> Tac unit) (d: dbg): Tac unit
  = d.sub "rewrite_subterm_in_goal" (fun d ->
        ctrl_rewrite TopDown (fun t ->
            // Go top down until we reach `subterm`, and stop.
            if term_eq t subterm then (true, Abort) else (false, Continue)
        ) (fun _ -> d.sub "tactic" (fun d -> d.dump "rewrite this subterm"; tactic d))
    )

/// Normalize fully (zeta_full) match scrutinees, effectively getting rid of (visible) control flow.
/// Note that this is likely to crash if scrutinees are not closed terms.
let full_norm_scrutinees (d: dbg) =
    d.sub "full_norm_scrutinees" (fun d ->
        let norm_scrutinee_in_goal () =
            let goal = cur_goal () in
            let goal_phi = term_as_formula goal in
            let (lhs, _) = expect_eq goal_phi in
            (match inspect lhs with
            | Tv_Match scrut ret brs ->
                rewrite_subterm_in_goal scrut (fun d -> 
                    norm [primops; iota; delta; zeta_full];
                    d.dump "`match` rewritten";
                    trefl ()
                ) d;
                discharge_smt_goals_now ()
            | _ -> ());
            trefl ()
        in
        let one_round (): Tac unit =
            ctrl_rewrite TopDown (fun t ->
                let is_match = (match inspect t with | Tv_Match _ _ _ -> true | _ -> false) in
                (is_match, Continue)
            ) norm_scrutinee_in_goal
        in
        d.print "round 1";
        one_round ();
        d.print "round 2";
        one_round ()
    )

/// Returns the list ``[`f1; ...; `fN]`` of all reachable top-levels `f1` ... `fN` tagged with attribute `attr`.
let top_levels_of_attr (attr: term): list term = 
    FStar.List.Tot.map
        (fun f -> pack_ln (Tv_FVar f)) 
        (lookup_attr attr (top_env ()))

/// Rewrite the goal, lifting _source functions_ that operates on _source types_ `Si` to a set of equivalent _destination functions_ operating on _destination types_ `Di`.
/// ## Definition
///
/// The _source types_ are denoted `S` or `Si`.
/// The _destination types_ are denoted `D` or `Dj`.
/// The _source functions_ are denoted `fS` or `fSi`.
/// The _destination functions_ are denoted `fD` or `fDi`.
/// `i` and `j` are used to range over sets of functions or types.
///
/// When a source type `S` can be transformed into a destination type `D`, we require:
///  - two _transformation functions_ `S_to_D: S -> D` and `S_to_D: S -> D` and,
///  - two lemma showing the two _transformations functions_ are inverse:
///     -  `S_D_lemma:  x:S -> (x == D_to_S (S_to_D x))` and
///     -  `D_S_lemma: x:D -> (x == S_to_D (D_to_S x))`.
///
/// For each source function `fS` of type `Si -> Sj` we require:
///   - a destination function `fD` of type `Di -> Dj`
///   - a lemma `fS_lemma: x:S -> (fS x == D_to_S (fD (S_to_D x)))`.
///
/// Additionally, direct transformations of destination types `Di_to_Dj: Di -> Dj` can be provided.
/// For each `Di_to_Dj` we require a lemma `Di_to_Dj_lemma: x:Di -> (S_to_Dj (Di_to_S x) == Di_to_Dj x)`, that is, the following diagram commutes:
/// ```mermaid
/// graph LR;
/// 	`Di`-->|`Di_to_S`|`S`;
/// 	`S`-->|`S_to_Dj`|`Dj`;
/// 	`Di`-->|`Di_to_Dj`|`Dj`;
/// ```
///
/// ## Example
/// Let a source type `S` and two destination type `D1` and `D2`.
/// Let two source functions: `fS: S -> S` and `gS: S -> S`.
/// Let two destination functions:
///  - `fD: D1 -> D2`
///  - `gD: D1 -> D1`
/// Let `D2_to_D1` a direct transformation from `D2` to `D1`.
///
/// Let's assume all the requirement from above are met.
/// Given `x:S`, the tactic will rewrite the goal `gS (gS (fS x))` into:
/// ```
/// D1_to_S (gD (S_to_D1 (
///     D1_to_S (gD (S_to_D1 (
///          D2_to_S (fD (S_to_D1 x))
///        )))
/// )))
/// ```
/// And then into:
/// ```
/// D1_to_S (gD (gD (D2_to_D1 (fD (S_to_D1 x)))))
/// ```
let rewrite_with_lifts (lift_lemmas: list term) (simpl_lemmas: list term) (d: dbg): Tac unit =
    d.sub "rewrite_with_lifts" (fun d -> 
        l_to_r (Minicore.Abstractions.Bitvec.fvars_of_attr ( `$LIFT_LEMMA ));
        d.dump "lift lemmas applied";
        
        l_to_r (Minicore.Abstractions.Bitvec.fvars_of_attr ( `$SIMPLIFICATION_LEMMA ));
        d.dump "simpl_lemmas lemmas applied";
    )

/// Test if the term `t` is of the shape `f arg1 ... arg<arity>`. 
/// If `arity` is not given, it is computed automatically.
let is_application_of (f: string) (#[(
        let f = pack_fv (explode_qn f) in
        let f_term = pack_ln (FStar.Stubs.Reflection.V1.Data.Tv_FVar f) in
        let list, _ = collect_arr (tc (top_env ()) f_term) in
        let arity = List.Tot.length list in
        exact (`(`@arity))
    )]arity: int) (t: term): Tac bool =
    let f = pack_fv (explode_qn f) in
    let hd, args = collect_app t in
    if List.Tot.length args <> arity 
    then false
    else match inspect hd with
    | Tv_UInst fv _ | Tv_FVar fv -> inspect_fv fv = inspect_fv f
    | _ -> false

let postprocess_tactic (lift_lemmas: list term) (simpl_lemmas: list term) (direct_transformation_lemmas: list term) =
    let d = mk_dbg "" in
    d.sub "postprocess_tactic" (fun d -> 
        norm [primops; iota; delta_namespace ["Libcrux_intrinsics"]; zeta_full];
        d.dump "definitions unfolded";

        rewrite_with_lifts lift_lemmas simpl_lemmas d;

        // rewrite_with_lifts (top_levels_of_attr (` $LIFT_LEMMA ))
        //                    (top_levels_of_attr (` $INTERPRETATION_LEMMA ))
        //                    d;
        // direct tr. lemmas : `%${i64x4::into_i32x8}

        l_to_r [`pw8; `pw4 ];
        d.dump "pointwise lemmas applied";

        let round _: Tac unit =
            let normalize_routine () =
                norm [primops; iota; delta_namespace (List.Tot.append 
                    [
                        "Minicore";
                        "FStar.FunctionalExtensionality";
                        `%Rust_primitives.cast_tc; `%Rust_primitives.unsize_tc; 
                        "Core.Ops"; `%(.[]); `%mark_to_normalize_here;
                    ]
                    direct_transformation_lemmas); zeta_full]
            in
            normalize_routine ();
            d.dump "normalize the scrutinees in the following expression";
            full_norm_scrutinees d;
            normalize_routine ();
            d.dump "after normalization of scrutinees";
            trefl ()
        in

        ctrl_rewrite BottomUp (fun t ->
            (is_application_of (`%mark_to_normalize_here) t, Continue)
        ) round;


        d.dump "after full normalization";
        trefl ()
    )

[@@FStar.Tactics.postprocess_with (fun _ -> 
    with_compat_pre_core 0 postprocess_tactic
)]
"#)]
#[inline(always)]
pub(super) fn montgomery_multiply(lhs: &mut Vec256, rhs: &Vec256) {
    let field_modulus = mm256_set1_epi32(FIELD_MODULUS);
    let inverse_of_modulus_mod_montgomery_r =
        mm256_set1_epi32(INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i32);

    let prod02 = mm256_mul_epi32(*lhs, *rhs);
    let prod13 = mm256_mul_epi32(
        mm256_shuffle_epi32::<0b11_11_01_01>(*lhs),
        mm256_shuffle_epi32::<0b11_11_01_01>(*rhs),
    );
    let k02 = mm256_mul_epi32(prod02, inverse_of_modulus_mod_montgomery_r);
    let k13 = mm256_mul_epi32(prod13, inverse_of_modulus_mod_montgomery_r);

    let c02 = mm256_mul_epi32(k02, field_modulus);
    let c13 = mm256_mul_epi32(k13, field_modulus);

    let res02 = mm256_sub_epi32(prod02, c02);
    let res13 = mm256_sub_epi32(prod13, c13);
    let res02_shifted = mm256_shuffle_epi32::<0b11_11_01_01>(res02);
    *lhs = mm256_blend_epi32::<0b10101010>(res02_shifted, res13);
}

#[inline(always)]
pub(super) fn shift_left_then_reduce<const SHIFT_BY: i32>(simd_unit: &mut Vec256) {
    let shifted = mm256_slli_epi32::<SHIFT_BY>(*simd_unit);

    let quotient = mm256_add_epi32(shifted, mm256_set1_epi32(1 << 22));
    let quotient = mm256_srai_epi32::<23>(quotient);

    let quotient_times_field_modulus =
        mm256_mullo_epi32(quotient, mm256_set1_epi32(FIELD_MODULUS as i32));

    *simd_unit = mm256_sub_epi32(shifted, quotient_times_field_modulus);
}

// TODO: Revisit this function when doing the range analysis and testing
// additional KATs.
#[inline(always)]
pub(super) fn infinity_norm_exceeds(simd_unit: &Vec256, bound: i32) -> bool {
    let absolute_values = mm256_abs_epi32(*simd_unit);

    // We will test if |simd_unit| > bound - 1, because if this is the case then
    // it follows that |simd_unit| >= bound
    let bound = mm256_set1_epi32(bound - 1);

    let compare_with_bound = mm256_cmpgt_epi32(absolute_values, bound);

    // If every lane of |result| is 0, all coefficients are <= bound - 1
    let result = mm256_testz_si256(compare_with_bound, compare_with_bound);

    result != 1
}

#[inline(always)]
pub(super) fn power2round(r0: &mut Vec256, r1: &mut Vec256) {
    to_unsigned_representatives(r0);

    *r1 = mm256_add_epi32(
        *r0,
        mm256_set1_epi32((1 << (BITS_IN_LOWER_PART_OF_T - 1)) - 1),
    );
    *r1 = mm256_srai_epi32::<{ BITS_IN_LOWER_PART_OF_T as i32 }>(*r1);

    let tmp = mm256_slli_epi32::<{ BITS_IN_LOWER_PART_OF_T as i32 }>(*r1);
    *r0 = mm256_sub_epi32(*r0, tmp);
}

#[inline(always)]
pub(super) fn decompose(gamma2: Gamma2, r: &Vec256, r0: &mut Vec256, r1: &mut Vec256) {
    let r = to_unsigned_representatives_ret(r);

    let ceil_of_r_by_128 = mm256_add_epi32(r, mm256_set1_epi32(127));
    let ceil_of_r_by_128 = mm256_srai_epi32::<7>(ceil_of_r_by_128);

    match gamma2 {
        GAMMA2_V95_232 => {
            // We approximate 1 / 1488 as:
            // ⌊2²⁴ / 1488⌋ / 2²⁴ = 11,275 / 2²⁴
            let result = mm256_mullo_epi32(ceil_of_r_by_128, mm256_set1_epi32(11_275));
            let result = mm256_add_epi32(result, mm256_set1_epi32(1 << 23));
            let result = mm256_srai_epi32::<24>(result);

            // For the corner-case a₁ = (q-1)/α = 44, we have to set a₁=0.
            let mask = mm256_sub_epi32(mm256_set1_epi32(43), result);
            let mask = mm256_srai_epi32::<31>(mask);

            let not_result = mm256_xor_si256(result, mask);

            *r1 = mm256_and_si256(result, not_result);
        }

        GAMMA2_V261_888 => {
            // We approximate 1 / 4092 as:
            // ⌊2²² / 4092⌋ / 2²² = 1025 / 2²²
            let result = mm256_mullo_epi32(ceil_of_r_by_128, mm256_set1_epi32(1025));
            let result = mm256_add_epi32(result, mm256_set1_epi32(1 << 21));
            let result = mm256_srai_epi32::<22>(result);

            // For the corner-case a₁ = (q-1)/α = 16, we have to set a₁=0.
            *r1 = mm256_and_si256(result, mm256_set1_epi32(15));
        }

        _ => unreachable!(),
    }

    // In the corner-case, when we set a₁=0, we will incorrectly
    // have a₀ > (q-1)/2 and we'll need to subtract q.  As we
    // return a₀ + q, that comes down to adding q if a₀ < (q-1)/2.

    let alpha = gamma2 * 2;
    let r0_tmp = mm256_mullo_epi32(*r1, mm256_set1_epi32(alpha));
    let r0_tmp = mm256_sub_epi32(r, r0_tmp);

    let field_modulus_halved = mm256_set1_epi32((FIELD_MODULUS - 1) / 2);
    let mask = mm256_sub_epi32(field_modulus_halved, r0_tmp);
    let mask = mm256_srai_epi32::<31>(mask);

    let field_modulus_and_mask = mm256_and_si256(mask, mm256_set1_epi32(FIELD_MODULUS));

    *r0 = mm256_sub_epi32(r0_tmp, field_modulus_and_mask);
}

#[inline(always)]
pub(super) fn compute_hint(low: &Vec256, high: &Vec256, gamma2: i32, hint: &mut Vec256) -> usize {
    let minus_gamma2 = mm256_set1_epi32(-gamma2);
    let gamma2 = mm256_set1_epi32(gamma2);

    let low_within_bound = mm256_cmpgt_epi32(mm256_abs_epi32(*low), gamma2);
    let low_equals_minus_gamma2 = mm256_cmpeq_epi32(*low, minus_gamma2);

    // If a lane in |high| is 0, the corresponding output will be 0; the output
    // will have its most significant bit set to 1 otherwise.
    let low_equals_minus_gamma2_and_high_is_nonzero =
        mm256_sign_epi32(low_equals_minus_gamma2, *high);

    *hint = mm256_or_si256(
        low_within_bound,
        low_equals_minus_gamma2_and_high_is_nonzero,
    );

    let hints_mask = mm256_movemask_ps(mm256_castsi256_ps(*hint));
    *hint = mm256_and_si256(*hint, mm256_set1_epi32(0x1));

    hints_mask.count_ones() as usize
}

#[inline(always)]
pub(super) fn use_hint(gamma2: Gamma2, r: &Vec256, hint: &mut Vec256) {
    let (mut r0, mut r1) = (mm256_setzero_si256(), mm256_setzero_si256());
    decompose(gamma2, r, &mut r0, &mut r1);

    let all_zeros = mm256_setzero_si256();

    // If r0 is negative, we have to subtract the hint, whereas if it is positive,
    // we have to add the hint. We thus add signs to the hint vector accordingly:
    //
    // With this step, |negate_hints| will match |hint| in only those lanes in
    // which the corresponding r0 value is negative, and will be 0 elsewhere.
    let negate_hints = vec256_blendv_epi32(all_zeros, *hint, r0);

    // If a lane in |negate_hints| is 1, it means the corresponding hint was 1,
    // and the lane value will be doubled. It will remain 0 otherwise.
    let negate_hints = mm256_slli_epi32::<1>(negate_hints);

    // Suppose |hints[0]| = 1, and |r0[0]| = 1, then this will set |hints[0]| = -1.
    // (we're indexing into an AVX2 vector, as it were).
    let hints = mm256_sub_epi32(*hint, negate_hints);

    // Now add the hints to r1
    let mut r1_plus_hints = mm256_add_epi32(r1, hints);

    match gamma2 {
        GAMMA2_V95_232 => {
            let max = mm256_set1_epi32(43);

            // If |r1_plus_hints[i]| is negative, it must be that |r1[i]| is
            // 0, in this case, we'd want to return |max|.
            r1_plus_hints = vec256_blendv_epi32(r1_plus_hints, max, r1_plus_hints);

            let greater_than_or_equal_to_max = mm256_cmpgt_epi32(r1_plus_hints, max);

            // If r1 is greater than equal to 43, we need to set the result to 0.
            *hint = vec256_blendv_epi32(r1_plus_hints, all_zeros, greater_than_or_equal_to_max);
        }
        GAMMA2_V261_888 => {
            *hint = mm256_and_si256(r1_plus_hints, mm256_set1_epi32(15));
        }

        _ => unreachable!(),
    }
}
