module Minicore.Core_arch.X86.Interpretations.Int_vec.Lift_lemmas
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

irreducible

/// An F* attribute that marks an item as being an lifting lemma.
let v_LIFT_LEMMA: Prims.unit = () <: Prims.unit

/// Make sure there is a dependency to int_vec_interp in F*
let e_: Prims.unit = Minicore.Abstractions.Bitvec.Int_vec_interp.v_SIMPLIFICATION_LEMMA

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_set1_epi32': x: i32
  -> Lemma
    (ensures
      (Minicore.Core_arch.X86.Avx.e_mm256_set1_epi32 x
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core.Convert.f_from #(Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
          #(Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
          #FStar.Tactics.Typeclasses.solve
          (Minicore.Core_arch.X86.Interpretations.Int_vec.e_mm256_set1_epi32 x
            <:
            Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

let e_mm256_set1_epi32 = e_mm256_set1_epi32'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_mul_epi32':
    x: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    y: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Minicore.Core_arch.X86.Avx2.e_mm256_mul_epi32 x y
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core.Convert.f_from #(Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
          #(Minicore.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
          #FStar.Tactics.Typeclasses.solve
          (Minicore.Core_arch.X86.Interpretations.Int_vec.e_mm256_mul_epi32 (Core.Convert.f_from #(Minicore.Abstractions.Funarr.t_FunArray
                      (mk_u64 8) i32)
                  #(Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
                  #FStar.Tactics.Typeclasses.solve
                  x
                <:
                Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
              (Core.Convert.f_from #(Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
                  #(Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
                  #FStar.Tactics.Typeclasses.solve
                  y
                <:
                Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
            <:
            Minicore.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

let e_mm256_mul_epi32 = e_mm256_mul_epi32'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_sub_epi32':
    x: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    y: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Minicore.Core_arch.X86.Avx2.e_mm256_sub_epi32 x y
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core.Convert.f_from #(Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
          #(Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
          #FStar.Tactics.Typeclasses.solve
          (Minicore.Core_arch.X86.Interpretations.Int_vec.e_mm256_sub_epi32 (Core.Convert.f_from #(Minicore.Abstractions.Funarr.t_FunArray
                      (mk_u64 8) i32)
                  #(Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
                  #FStar.Tactics.Typeclasses.solve
                  x
                <:
                Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
              (Core.Convert.f_from #(Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
                  #(Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
                  #FStar.Tactics.Typeclasses.solve
                  y
                <:
                Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
            <:
            Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

let e_mm256_sub_epi32 = e_mm256_sub_epi32'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_shuffle_epi32': v_CONTROL: i32 -> x: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Minicore.Core_arch.X86.Avx2.e_mm256_shuffle_epi32 v_CONTROL x
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core.Convert.f_from #(Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
          #(Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
          #FStar.Tactics.Typeclasses.solve
          (Minicore.Core_arch.X86.Interpretations.Int_vec.e_mm256_shuffle_epi32 v_CONTROL
              (Core.Convert.f_from #(Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
                  #(Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
                  #FStar.Tactics.Typeclasses.solve
                  x
                <:
                Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
            <:
            Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

let e_mm256_shuffle_epi32 (v_CONTROL: i32) = e_mm256_shuffle_epi32' v_CONTROL

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_blend_epi32':
    v_CONTROL: i32 ->
    x: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    y: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Minicore.Core_arch.X86.Avx2.e_mm256_blend_epi32 v_CONTROL x y
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core.Convert.f_from #(Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
          #(Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
          #FStar.Tactics.Typeclasses.solve
          (Minicore.Core_arch.X86.Interpretations.Int_vec.e_mm256_blend_epi32 v_CONTROL
              (Core.Convert.f_from #(Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
                  #(Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
                  #FStar.Tactics.Typeclasses.solve
                  x
                <:
                Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
              (Core.Convert.f_from #(Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
                  #(Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256))
                  #FStar.Tactics.Typeclasses.solve
                  y
                <:
                Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
            <:
            Minicore.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

let e_mm256_blend_epi32 (v_CONTROL: i32) = e_mm256_blend_epi32' v_CONTROL
