module Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

irreducible

/// An F* attribute that marks an item as being an lifting lemma.
let v_ETA_MATCH_EXPAND: Prims.unit = () <: Prims.unit

[@@ v_ETA_MATCH_EXPAND ]

assume
val pointwise_i32x8': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32
  -> Lemma
    (ensures
      x ==
      (Core_models.Abstractions.Funarr.impl_7__pointwise #i32 x
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32))

unfold
let pointwise_i32x8 = pointwise_i32x8'

[@@ v_ETA_MATCH_EXPAND ]

assume
val pointwise_i64x4': x: Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64
  -> Lemma
    (ensures
      x ==
      (Core_models.Abstractions.Funarr.impl_6__pointwise #i64 x
        <:
        Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64))

unfold
let pointwise_i64x4 = pointwise_i64x4'

irreducible

/// An F* attribute that marks an item as being an lifting lemma.
let v_LIFT_LEMMA: Prims.unit = () <: Prims.unit

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_set1_epi32': x: i32
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx.e_mm256_set1_epi32 x
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core.Convert.f_from #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
          #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
          #FStar.Tactics.Typeclasses.solve
          (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_set1_epi32 x
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_set1_epi32 = e_mm256_set1_epi32'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_mul_epi32':
    x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    y: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_mul_epi32 x y
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core.Convert.f_from #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
          #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
          #FStar.Tactics.Typeclasses.solve
          (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_mul_epi32 (Core.Convert.f_from #(
                    Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
                  #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
                  #FStar.Tactics.Typeclasses.solve
                  x
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
              (Core.Convert.f_from #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
                  #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
                  #FStar.Tactics.Typeclasses.solve
                  y
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 4) i64)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_mul_epi32 = e_mm256_mul_epi32'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_sub_epi32':
    x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    y: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_sub_epi32 x y
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core.Convert.f_from #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
          #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
          #FStar.Tactics.Typeclasses.solve
          (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_sub_epi32 (Core.Convert.f_from #(
                    Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
                  #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
                  #FStar.Tactics.Typeclasses.solve
                  x
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
              (Core.Convert.f_from #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
                  #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
                  #FStar.Tactics.Typeclasses.solve
                  y
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_sub_epi32 = e_mm256_sub_epi32'

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_shuffle_epi32':
    v_CONTROL: i32 ->
    x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_shuffle_epi32 v_CONTROL x
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core.Convert.f_from #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
          #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
          #FStar.Tactics.Typeclasses.solve
          (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_shuffle_epi32 v_CONTROL
              (Core.Convert.f_from #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
                  #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
                  #FStar.Tactics.Typeclasses.solve
                  x
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_shuffle_epi32 (v_CONTROL: i32) = e_mm256_shuffle_epi32' v_CONTROL

[@@ v_LIFT_LEMMA ]

assume
val e_mm256_blend_epi32':
    v_CONTROL: i32 ->
    x: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256) ->
    y: Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)
  -> Lemma
    (ensures
      (Core_models.Core_arch.X86.Avx2.e_mm256_blend_epi32 v_CONTROL x y
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)) ==
      (Core.Convert.f_from #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
          #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
          #FStar.Tactics.Typeclasses.solve
          (Core_models.Core_arch.X86.Interpretations.Int_vec.e_mm256_blend_epi32 v_CONTROL
              (Core.Convert.f_from #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
                  #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
                  #FStar.Tactics.Typeclasses.solve
                  x
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
              (Core.Convert.f_from #(Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
                  #(Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
                  #FStar.Tactics.Typeclasses.solve
                  y
                <:
                Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
            <:
            Core_models.Abstractions.Funarr.t_FunArray (mk_u64 8) i32)
        <:
        Core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256)))

unfold
let e_mm256_blend_epi32 (v_CONTROL: i32) = e_mm256_blend_epi32' v_CONTROL

let flatten_circuit (): FStar.Tactics.Tac unit =
            let open Tactics.Circuits in
            flatten_circuit
                [
                    "Core_models";
                    "FStar.FunctionalExtensionality";
                    `%Rust_primitives.cast_tc; `%Rust_primitives.unsize_tc;
                    "Core.Ops"; `%(.[]);
                ]
                (top_levels_of_attr (` v_LIFT_LEMMA ))
                (top_levels_of_attr (` Core_models.Abstractions.Bitvec.Int_vec_interp.v_SIMPLIFICATION_LEMMA ))
                (top_levels_of_attr (` v_ETA_MATCH_EXPAND ))
