module Libcrux_ml_dsa.Simd.Avx2.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80 --compat_pre_core 1"
open Core
open FStar.Mul

let to_unsigned_representatives_ret (t: Minicore.Core_arch.X86.t_e_ee_m256i)
    : Minicore.Core_arch.X86.t_e_ee_m256i =
  let signs:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_srai_epi32 (mk_i32 31) t
  in
  let conditional_add_field_modulus:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_and_si256 signs
      (Libcrux_intrinsics.Avx2.mm256_set1_epi32 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i)
  in
  Libcrux_intrinsics.Avx2.mm256_add_epi32 t conditional_add_field_modulus

let to_unsigned_representatives (t: Minicore.Core_arch.X86.t_e_ee_m256i)
    : Minicore.Core_arch.X86.t_e_ee_m256i =
  let t:Minicore.Core_arch.X86.t_e_ee_m256i = to_unsigned_representatives_ret t in
  t

let add (lhs rhs: Minicore.Core_arch.X86.t_e_ee_m256i) : Minicore.Core_arch.X86.t_e_ee_m256i =
  let lhs:Minicore.Core_arch.X86.t_e_ee_m256i = Libcrux_intrinsics.Avx2.mm256_add_epi32 lhs rhs in
  lhs

let subtract (lhs rhs: Minicore.Core_arch.X86.t_e_ee_m256i) : Minicore.Core_arch.X86.t_e_ee_m256i =
  let lhs:Minicore.Core_arch.X86.t_e_ee_m256i = Libcrux_intrinsics.Avx2.mm256_sub_epi32 lhs rhs in
  lhs

let montgomery_multiply_by_constant (lhs: Minicore.Core_arch.X86.t_e_ee_m256i) (constant: i32)
    : Minicore.Core_arch.X86.t_e_ee_m256i =
  let rhs:Minicore.Core_arch.X86.t_e_ee_m256i = Libcrux_intrinsics.Avx2.mm256_set1_epi32 constant in
  let field_modulus:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_set1_epi32 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
  in
  let inverse_of_modulus_mod_montgomery_r:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_set1_epi32 (cast (Libcrux_ml_dsa.Simd.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
            <:
            u64)
        <:
        i32)
  in
  let prod02:Minicore.Core_arch.X86.t_e_ee_m256i = Libcrux_intrinsics.Avx2.mm256_mul_epi32 lhs rhs in
  let prod13:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_mul_epi32 (Libcrux_intrinsics.Avx2.mm256_shuffle_epi32 (mk_i32 245
          )
          lhs
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i)
      (Libcrux_intrinsics.Avx2.mm256_shuffle_epi32 (mk_i32 245) rhs
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i)
  in
  let k02:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_mul_epi32 prod02 inverse_of_modulus_mod_montgomery_r
  in
  let k13:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_mul_epi32 prod13 inverse_of_modulus_mod_montgomery_r
  in
  let c02:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_mul_epi32 k02 field_modulus
  in
  let c13:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_mul_epi32 k13 field_modulus
  in
  let res02:Minicore.Core_arch.X86.t_e_ee_m256i = Libcrux_intrinsics.Avx2.mm256_sub_epi32 prod02 c02 in
  let res13:Minicore.Core_arch.X86.t_e_ee_m256i = Libcrux_intrinsics.Avx2.mm256_sub_epi32 prod13 c13 in
  let res02_shifted:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_shuffle_epi32 (mk_i32 245) res02
  in
  Libcrux_intrinsics.Avx2.mm256_blend_epi32 (mk_i32 170) res02_shifted res13

open FStar.Tactics
let pw8 #t (x: Minicore.Abstractions.Funarr.t_FunArray _ t): Lemma (x == Minicore.Abstractions.Funarr.impl_7__pointwise x) = admit ()
let pw4 #t (x: Minicore.Abstractions.Funarr.t_FunArray _ t): Lemma (x == Minicore.Abstractions.Funarr.impl_6__pointwise x) = admit ()

[@@FStar.Tactics.postprocess_with (fun _ -> 
    l_to_r [
        `Libcrux_ml_dsa.Simd.Avx2.Arithmetic.Computable_specs.eq_mm256_set1_epi32;
        `Libcrux_ml_dsa.Simd.Avx2.Arithmetic.Computable_specs.eq_mm256_mul_epi32;
        `Libcrux_ml_dsa.Simd.Avx2.Arithmetic.Computable_specs.eq_mm256_shuffle_epi32;
        `Libcrux_ml_dsa.Simd.Avx2.Arithmetic.Computable_specs.eq_mm256_sub_epi32;
        `Libcrux_ml_dsa.Simd.Avx2.Arithmetic.Computable_specs.eq_mm256_blend_epi32
    ];
    l_to_r [
        `Libcrux_ml_dsa.Simd.Avx2.Arithmetic.Computable_specs.identity_vec_8_i32_inv;
        `Libcrux_ml_dsa.Simd.Avx2.Arithmetic.Computable_specs.identity_vec_4_i64_inv;
        `Libcrux_ml_dsa.Simd.Avx2.Arithmetic.Computable_specs.identity_vec_8_i32;
        `Libcrux_ml_dsa.Simd.Avx2.Arithmetic.Computable_specs.identity_vec_4_i64
    ];
    l_to_r [`pw8; `pw4];
    dump "AAA";
    // norm [primops; iota; delta_namespace ["Core"; "Minicore"; "Libcrux_intrinsics"; "FStar.FunctionalExtensionality"; "Rust_primitives"; "Libcrux_ml_dsa.Simd.Avx2.Arithmetic.Computable_specs"]; zeta_full];
    // dump "AAABBB1";
    norm [primops; iota; delta; zeta_full];
    dump "AAABBB2";
    l_to_r [`Libcrux_ml_dsa.Simd.Avx2.Arithmetic.Computable_specs.manual_norm_lemma];
    dump "AAABBB3";
    norm [primops; iota; delta_namespace ["Libcrux_ml_dsa.Simd.Avx2.Arithmetic.Computable_specs"]; zeta_full];
    dump "AAABBB4";
    trefl ();

    // ctrl_rewrite TopDown (fun t ->
    //     dump ("LOOKING AT" ^ term_to_string t);
    //     let env = cur_env () in
    //     match FStar.InteractiveHelpers.ExploreTerm.free_in t with
    //     | [] -> (true, Skip)
    //     | _ -> (false, Continue)
    // ) (fun () ->
    //     norm [primops; iota; delta; zeta_full]
    // );
    // Minicore.Abstractions.Bitvec.bitvec_postprocess_norm ();
    ()
    // norm [primops; iota; delta_namespace ["Core"; "Minicore"; "Libcrux_intrinsics"; "FStar.FunctionalExtensionality"; "Rust_primitives"; "Libcrux_ml_dsa.Simd.Avx2.Arithmetic.Computable_specs"]; zeta];
    // fail "HEY"
)]

let montgomery_multiply (lhs rhs: Minicore.Core_arch.X86.t_e_ee_m256i) : Minicore.Core_arch.X86.t_e_ee_m256i =
  let field_modulus:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_set1_epi32 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
  in
  let inverse_of_modulus_mod_montgomery_r:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_set1_epi32 (cast (Libcrux_ml_dsa.Simd.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R
            <:
            u64)
        <:
        i32)
  in
  let prod02:Minicore.Core_arch.X86.t_e_ee_m256i = Libcrux_intrinsics.Avx2.mm256_mul_epi32 lhs rhs in
  let prod13:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_mul_epi32 (Libcrux_intrinsics.Avx2.mm256_shuffle_epi32 (mk_i32 245
          )
          lhs
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i)
      (Libcrux_intrinsics.Avx2.mm256_shuffle_epi32 (mk_i32 245) rhs
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i)
  in
  let k02:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_mul_epi32 prod02 inverse_of_modulus_mod_montgomery_r
  in
  let k13:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_mul_epi32 prod13 inverse_of_modulus_mod_montgomery_r
  in
  let c02:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_mul_epi32 k02 field_modulus
  in
  let c13:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_mul_epi32 k13 field_modulus
  in
  let res02:Minicore.Core_arch.X86.t_e_ee_m256i = Libcrux_intrinsics.Avx2.mm256_sub_epi32 prod02 c02 in
  let res13:Minicore.Core_arch.X86.t_e_ee_m256i = Libcrux_intrinsics.Avx2.mm256_sub_epi32 prod13 c13 in
  let res02_shifted:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_shuffle_epi32 (mk_i32 245) res02
  in
  let lhs:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_blend_epi32 (mk_i32 170) res02_shifted res13
  in
  lhs

let f (x y: i32) : i32 =
  cast ((cast (cast (((cast (x <: i32) <: i64) *! (cast (y <: i32) <: i64) <: i64) >>! mk_i32 32
                <:
                i64)
            <:
            i32)
        <:
        i64) -!
      (cast (cast (((cast (cast ((cast (cast ((cast (x <: i32) <: i64) *! (cast (y <: i32) <: i64)
                                      <:
                                      i64)
                                  <:
                                  i32)
                              <:
                              i64) *!
                            (cast (mk_i32 58728449 <: i32) <: i64)
                            <:
                            i64)
                        <:
                        i32)
                    <:
                    i64) *!
                  (cast (mk_i32 8380417 <: i32) <: i64)
                  <:
                  i64) >>!
                mk_i32 32
                <:
                i64)
            <:
            i32)
        <:
        i64)
      <:
      i64)
  <:
  i32

let spec__low_32_ (x: i64) : i32 = cast (x <: i64) <: i32

let spec__high_32_ (x: i64) : i32 = cast (x >>! mk_i32 32 <: i64) <: i32

let spec__mul_64_ (x y: i64) : i64 =
  (cast (spec__low_32_ x <: i32) <: i64) *! (cast (spec__low_32_ y <: i32) <: i64)

let spec (x y: i32) : i32 =
  let prod:i64 = spec__mul_64_ (cast (x <: i32) <: i64) (cast (y <: i32) <: i64) in
  let k:i64 =
    spec__mul_64_ prod
      (cast (Libcrux_ml_dsa.Simd.Traits.v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R <: u64) <: i64)
  in
  let c:i64 = spec__mul_64_ k (cast (Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS <: i32) <: i64) in
  let res:i64 =
    (cast (spec__high_32_ prod <: i32) <: i64) -! (cast (spec__high_32_ c <: i32) <: i64)
  in
  cast (res <: i64) <: i32

let montgomery_multiply_lemma (lhs rhs: Minicore.Core_arch.X86.t_e_ee_m256i)
    : Lemma
    (ensures
      (let out:Minicore.Core_arch.X86.t_e_ee_m256i =
          Core.Clone.f_clone #Minicore.Core_arch.X86.t_e_ee_m256i #FStar.Tactics.Typeclasses.solve lhs
        in
        let out:Minicore.Core_arch.X86.t_e_ee_m256i = montgomery_multiply out rhs in
        let lhs:Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
          Libcrux_ml_dsa.Simd.Avx2.Arithmetic.Computable_specs.vec_8_i32_of_bv lhs
        in
        let rhs:Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
          Libcrux_ml_dsa.Simd.Avx2.Arithmetic.Computable_specs.vec_8_i32_of_bv rhs
        in
        let out:Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
          Libcrux_ml_dsa.Simd.Avx2.Arithmetic.Computable_specs.vec_8_i32_of_bv out
        in
        (f (lhs.[ mk_u64 7 ] <: i32) (rhs.[ mk_u64 7 ] <: i32) <: i32) == (out.[ mk_u64 7 ] <: i32))
    ) = 
        let out:Minicore.Core_arch.X86.t_e_ee_m256i =
          Core.Clone.f_clone #Minicore.Core_arch.X86.t_e_ee_m256i #FStar.Tactics.Typeclasses.solve lhs
        in
        let out:Minicore.Core_arch.X86.t_e_ee_m256i = montgomery_multiply out rhs in
        let lhs:Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
          Libcrux_ml_dsa.Simd.Avx2.Arithmetic.Computable_specs.vec_8_i32_of_bv lhs
        in
        let rhs:Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
          Libcrux_ml_dsa.Simd.Avx2.Arithmetic.Computable_specs.vec_8_i32_of_bv rhs
        in
        let out:Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32 =
          Libcrux_ml_dsa.Simd.Avx2.Arithmetic.Computable_specs.vec_8_i32_of_bv out
        in
        assert ((f (lhs.[ mk_u64 7 ] <: i32) (rhs.[ mk_u64 7 ] <: i32) <: i32) == (out.[ mk_u64 7 ] <: i32))
        by (
          let open FStar.Tactics in

          dump "START HERE";
          l_to_r [
            `Libcrux_ml_dsa.Simd.Avx2.Arithmetic.Computable_specs.identity_vec_8_i32_inv;
            `Libcrux_ml_dsa.Simd.Avx2.Arithmetic.Computable_specs.identity_vec_4_i64_inv;
            `Libcrux_ml_dsa.Simd.Avx2.Arithmetic.Computable_specs.identity_vec_8_i32;
            `Libcrux_ml_dsa.Simd.Avx2.Arithmetic.Computable_specs.identity_vec_4_i64
          ];
          dump "beofre zeta_full";
          norm [primops; iota; delta_namespace [`%montgomery_multiply; `%f; "Minicore.Abstractions.Funarr"; "Core.Clone"; "Core.Ops"; "FStar.FunctionalExtensionality"; "Rust_primitives.Integers.mk_u64"; "Rust_primitives.Integers.mk_int"]; zeta_full];
          dump "after core";
          norm [primops; iota; delta_namespace [`%montgomery_multiply; `%f]];
          dump "before FunctionalExtensionality";
          norm [primops; iota; delta_namespace [`%montgomery_multiply; `%f; "FStar.FunctionalExtensionality"]; zeta_full];
          // let _ = repeat (fun _ -> let _ = clear_top () in ()) in
          dump "after identity lemmas";
          smt_sync ()
          // norm [primops; iota; delta_namespace [`%montgomery_multiply; `%f]; zeta_full];
          // dump "iull norm"
        )

let shift_left_then_reduce (v_SHIFT_BY: i32) (simd_unit: Minicore.Core_arch.X86.t_e_ee_m256i)
    : Minicore.Core_arch.X86.t_e_ee_m256i =
  let shifted:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_slli_epi32 v_SHIFT_BY simd_unit
  in
  let quotient:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_add_epi32 shifted
      (Libcrux_intrinsics.Avx2.mm256_set1_epi32 (mk_i32 1 <<! mk_i32 22 <: i32)
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i)
  in
  let quotient:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_srai_epi32 (mk_i32 23) quotient
  in
  let quotient_times_field_modulus:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_mullo_epi32 quotient
      (Libcrux_intrinsics.Avx2.mm256_set1_epi32 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i)
  in
  let simd_unit:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_sub_epi32 shifted quotient_times_field_modulus
  in
  simd_unit

let infinity_norm_exceeds (simd_unit: Minicore.Core_arch.X86.t_e_ee_m256i) (bound: i32) : bool =
  let absolute_values:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_abs_epi32 simd_unit
  in
  let bound:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_set1_epi32 (bound -! mk_i32 1 <: i32)
  in
  let compare_with_bound:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_cmpgt_epi32 absolute_values bound
  in
  let result:i32 =
    Libcrux_intrinsics.Avx2.mm256_testz_si256 compare_with_bound compare_with_bound
  in
  result <>. mk_i32 1

let power2round (r0 r1: Minicore.Core_arch.X86.t_e_ee_m256i)
    : (Minicore.Core_arch.X86.t_e_ee_m256i & Minicore.Core_arch.X86.t_e_ee_m256i) =
  let r0:Minicore.Core_arch.X86.t_e_ee_m256i = to_unsigned_representatives r0 in
  let r1:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_add_epi32 r0
      (Libcrux_intrinsics.Avx2.mm256_set1_epi32 ((mk_i32 1 <<!
              (Libcrux_ml_dsa.Constants.v_BITS_IN_LOWER_PART_OF_T -! mk_usize 1 <: usize)
              <:
              i32) -!
            mk_i32 1
            <:
            i32)
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i)
  in
  let r1:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_srai_epi32 (mk_i32 13) r1
  in
  let tmp:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_slli_epi32 (mk_i32 13) r1
  in
  let r0:Minicore.Core_arch.X86.t_e_ee_m256i = Libcrux_intrinsics.Avx2.mm256_sub_epi32 r0 tmp in
  r0, r1 <: (Minicore.Core_arch.X86.t_e_ee_m256i & Minicore.Core_arch.X86.t_e_ee_m256i)

let decompose (gamma2: i32) (r r0 r1: Minicore.Core_arch.X86.t_e_ee_m256i)
    : (Minicore.Core_arch.X86.t_e_ee_m256i & Minicore.Core_arch.X86.t_e_ee_m256i) =
  let r:Minicore.Core_arch.X86.t_e_ee_m256i = to_unsigned_representatives_ret r in
  let ceil_of_r_by_128_:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_add_epi32 r
      (Libcrux_intrinsics.Avx2.mm256_set1_epi32 (mk_i32 127) <: Minicore.Core_arch.X86.t_e_ee_m256i)
  in
  let ceil_of_r_by_128_:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_srai_epi32 (mk_i32 7) ceil_of_r_by_128_
  in
  let r1:Minicore.Core_arch.X86.t_e_ee_m256i =
    match gamma2 <: i32 with
    | Rust_primitives.Integers.MkInt 95232 ->
      let result:Minicore.Core_arch.X86.t_e_ee_m256i =
        Libcrux_intrinsics.Avx2.mm256_mullo_epi32 ceil_of_r_by_128_
          (Libcrux_intrinsics.Avx2.mm256_set1_epi32 (mk_i32 11275)
            <:
            Minicore.Core_arch.X86.t_e_ee_m256i)
      in
      let result:Minicore.Core_arch.X86.t_e_ee_m256i =
        Libcrux_intrinsics.Avx2.mm256_add_epi32 result
          (Libcrux_intrinsics.Avx2.mm256_set1_epi32 (mk_i32 1 <<! mk_i32 23 <: i32)
            <:
            Minicore.Core_arch.X86.t_e_ee_m256i)
      in
      let result:Minicore.Core_arch.X86.t_e_ee_m256i =
        Libcrux_intrinsics.Avx2.mm256_srai_epi32 (mk_i32 24) result
      in
      let mask:Minicore.Core_arch.X86.t_e_ee_m256i =
        Libcrux_intrinsics.Avx2.mm256_sub_epi32 (Libcrux_intrinsics.Avx2.mm256_set1_epi32 (mk_i32 43
              )
            <:
            Minicore.Core_arch.X86.t_e_ee_m256i)
          result
      in
      let mask:Minicore.Core_arch.X86.t_e_ee_m256i =
        Libcrux_intrinsics.Avx2.mm256_srai_epi32 (mk_i32 31) mask
      in
      let not_result:Minicore.Core_arch.X86.t_e_ee_m256i =
        Libcrux_intrinsics.Avx2.mm256_xor_si256 result mask
      in
      let r1:Minicore.Core_arch.X86.t_e_ee_m256i =
        Libcrux_intrinsics.Avx2.mm256_and_si256 result not_result
      in
      r1
    | Rust_primitives.Integers.MkInt 261888 ->
      let result:Minicore.Core_arch.X86.t_e_ee_m256i =
        Libcrux_intrinsics.Avx2.mm256_mullo_epi32 ceil_of_r_by_128_
          (Libcrux_intrinsics.Avx2.mm256_set1_epi32 (mk_i32 1025) <: Minicore.Core_arch.X86.t_e_ee_m256i
          )
      in
      let result:Minicore.Core_arch.X86.t_e_ee_m256i =
        Libcrux_intrinsics.Avx2.mm256_add_epi32 result
          (Libcrux_intrinsics.Avx2.mm256_set1_epi32 (mk_i32 1 <<! mk_i32 21 <: i32)
            <:
            Minicore.Core_arch.X86.t_e_ee_m256i)
      in
      let result:Minicore.Core_arch.X86.t_e_ee_m256i =
        Libcrux_intrinsics.Avx2.mm256_srai_epi32 (mk_i32 22) result
      in
      let r1:Minicore.Core_arch.X86.t_e_ee_m256i =
        Libcrux_intrinsics.Avx2.mm256_and_si256 result
          (Libcrux_intrinsics.Avx2.mm256_set1_epi32 (mk_i32 15) <: Minicore.Core_arch.X86.t_e_ee_m256i)
      in
      r1
    | _ -> r1
  in
  let alpha:i32 = gamma2 *! mk_i32 2 in
  let r0_tmp:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_mullo_epi32 r1
      (Libcrux_intrinsics.Avx2.mm256_set1_epi32 alpha <: Minicore.Core_arch.X86.t_e_ee_m256i)
  in
  let r0_tmp:Minicore.Core_arch.X86.t_e_ee_m256i = Libcrux_intrinsics.Avx2.mm256_sub_epi32 r r0_tmp in
  let field_modulus_halved:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_set1_epi32 ((Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS -!
          mk_i32 1
          <:
          i32) /!
        mk_i32 2
        <:
        i32)
  in
  let mask:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_sub_epi32 field_modulus_halved r0_tmp
  in
  let mask:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_srai_epi32 (mk_i32 31) mask
  in
  let field_modulus_and_mask:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_and_si256 mask
      (Libcrux_intrinsics.Avx2.mm256_set1_epi32 Libcrux_ml_dsa.Simd.Traits.v_FIELD_MODULUS
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i)
  in
  let r0:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_sub_epi32 r0_tmp field_modulus_and_mask
  in
  r0, r1 <: (Minicore.Core_arch.X86.t_e_ee_m256i & Minicore.Core_arch.X86.t_e_ee_m256i)

let compute_hint
      (low high: Minicore.Core_arch.X86.t_e_ee_m256i)
      (gamma2: i32)
      (hint: Minicore.Core_arch.X86.t_e_ee_m256i)
    : (Minicore.Core_arch.X86.t_e_ee_m256i & usize) =
  let minus_gamma2:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_set1_epi32 (Core.Ops.Arith.f_neg gamma2 <: i32)
  in
  let gamma2:Minicore.Core_arch.X86.t_e_ee_m256i = Libcrux_intrinsics.Avx2.mm256_set1_epi32 gamma2 in
  let low_within_bound:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_cmpgt_epi32 (Libcrux_intrinsics.Avx2.mm256_abs_epi32 low
        <:
        Minicore.Core_arch.X86.t_e_ee_m256i)
      gamma2
  in
  let low_equals_minus_gamma2:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_cmpeq_epi32 low minus_gamma2
  in
  let low_equals_minus_gamma2_and_high_is_nonzero:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_sign_epi32 low_equals_minus_gamma2 high
  in
  let hint:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_or_si256 low_within_bound
      low_equals_minus_gamma2_and_high_is_nonzero
  in
  let hints_mask:i32 =
    Libcrux_intrinsics.Avx2.mm256_movemask_ps (Libcrux_intrinsics.Avx2.mm256_castsi256_ps hint
        <:
        Minicore.Core_arch.X86.t_e_ee_m256)
  in
  let hint:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_and_si256 hint
      (Libcrux_intrinsics.Avx2.mm256_set1_epi32 (mk_i32 1) <: Minicore.Core_arch.X86.t_e_ee_m256i)
  in
  let hax_temp_output:usize = cast (Core.Num.impl_i32__count_ones hints_mask <: u32) <: usize in
  hint, hax_temp_output <: (Minicore.Core_arch.X86.t_e_ee_m256i & usize)

let uuse_hint (gamma2: i32) (r hint: Minicore.Core_arch.X86.t_e_ee_m256i)
    : Minicore.Core_arch.X86.t_e_ee_m256i =
  let r0, r1:(Minicore.Core_arch.X86.t_e_ee_m256i & Minicore.Core_arch.X86.t_e_ee_m256i) =
    Libcrux_intrinsics.Avx2.mm256_setzero_si256 (), Libcrux_intrinsics.Avx2.mm256_setzero_si256 ()
    <:
    (Minicore.Core_arch.X86.t_e_ee_m256i & Minicore.Core_arch.X86.t_e_ee_m256i)
  in
  let tmp0, tmp1:(Minicore.Core_arch.X86.t_e_ee_m256i & Minicore.Core_arch.X86.t_e_ee_m256i) =
    decompose gamma2 r r0 r1
  in
  let r0:Minicore.Core_arch.X86.t_e_ee_m256i = tmp0 in
  let r1:Minicore.Core_arch.X86.t_e_ee_m256i = tmp1 in
  let _:Prims.unit = () in
  let all_zeros:Minicore.Core_arch.X86.t_e_ee_m256i = Libcrux_intrinsics.Avx2.mm256_setzero_si256 () in
  let negate_hints:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.vec256_blendv_epi32 all_zeros hint r0
  in
  let negate_hints:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_slli_epi32 (mk_i32 1) negate_hints
  in
  let hints:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_sub_epi32 hint negate_hints
  in
  let r1_plus_hints:Minicore.Core_arch.X86.t_e_ee_m256i =
    Libcrux_intrinsics.Avx2.mm256_add_epi32 r1 hints
  in
  let hint, r1_plus_hints:(Minicore.Core_arch.X86.t_e_ee_m256i & Minicore.Core_arch.X86.t_e_ee_m256i) =
    match gamma2 <: i32 with
    | Rust_primitives.Integers.MkInt 95232 ->
      let max:Minicore.Core_arch.X86.t_e_ee_m256i =
        Libcrux_intrinsics.Avx2.mm256_set1_epi32 (mk_i32 43)
      in
      let r1_plus_hints:Minicore.Core_arch.X86.t_e_ee_m256i =
        Libcrux_intrinsics.Avx2.vec256_blendv_epi32 r1_plus_hints max r1_plus_hints
      in
      let greater_than_or_equal_to_max:Minicore.Core_arch.X86.t_e_ee_m256i =
        Libcrux_intrinsics.Avx2.mm256_cmpgt_epi32 r1_plus_hints max
      in
      let hint:Minicore.Core_arch.X86.t_e_ee_m256i =
        Libcrux_intrinsics.Avx2.vec256_blendv_epi32 r1_plus_hints
          all_zeros
          greater_than_or_equal_to_max
      in
      hint, r1_plus_hints <: (Minicore.Core_arch.X86.t_e_ee_m256i & Minicore.Core_arch.X86.t_e_ee_m256i)
    | Rust_primitives.Integers.MkInt 261888 ->
      let hint:Minicore.Core_arch.X86.t_e_ee_m256i =
        Libcrux_intrinsics.Avx2.mm256_and_si256 r1_plus_hints
          (Libcrux_intrinsics.Avx2.mm256_set1_epi32 (mk_i32 15) <: Minicore.Core_arch.X86.t_e_ee_m256i)
      in
      hint, r1_plus_hints <: (Minicore.Core_arch.X86.t_e_ee_m256i & Minicore.Core_arch.X86.t_e_ee_m256i)
    | _ ->
      hint, r1_plus_hints <: (Minicore.Core_arch.X86.t_e_ee_m256i & Minicore.Core_arch.X86.t_e_ee_m256i)
  in
  hint
