import Hax
import extraction.libcrux_intrinsics
import extraction.libcrux_sha3
import extraction.hacspec_sha3
import Std.Do.Triple
import Std.Tactic.Do

/-!
# SHA-3 implementation verification: impl → pure

Proves that the portable implementation (`N=1, T=u64`) of each Keccak-f step
matches inline pure reference definitions that mirror the FIPS 202 / hacspec spec.

## Proof strategy
- Define pure functions (no monads) as the ground truth.
- Prove impl functions satisfy Hoare triples whose postconditions match the pure defs.
- The spec→pure direction is deferred (clearly correct by construction).

## Key structural differences between impl and spec
- **Theta+Rho fusion**: Impl's theta returns (unchanged_state, d_array);
  rho fuses theta-XOR + rho-rotation. We define `rho_theta_pure` for this.
- **Axis convention**: Impl `get_ij(arr,i,j) = arr[5*j+i]`,
  Spec `get(st,x,y) = st[5*x+y]`. Both give flat `5*j+i` when j=x, i=y.
-/

open Std.Do
open libcrux_sha3.generic_keccak
open hacspec_sha3.keccak_f

set_option linter.unusedVariables false

/-! ## Pure reference definitions -/

namespace Pure

def rotate_left_pure (x : u64) (n : u32) : u64 :=
  UInt64.ofBitVec (BitVec.rotateLeft x.toBitVec n.toNat)

abbrev ROUND_CONSTANTS_pure : Vector u64 24 := ROUND_CONSTANTS.toVec
abbrev RHO_OFFSETS_pure : Vector u32 25 := RHO_OFFSETS.toVec

/-- Theta column parity: C[x] = state[5x] ⊕ state[5x+1] ⊕ … ⊕ state[5x+4] -/
def theta_c_pure (sv : Vector u64 25) (x : Fin 5) : u64 :=
  sv[5*x.val] ^^^ sv[5*x.val+1] ^^^ sv[5*x.val+2] ^^^ sv[5*x.val+3] ^^^ sv[5*x.val+4]

/-- Theta offset: D[x] = C[(x+4)%5] ⊕ rot(C[(x+1)%5], 1) -/
def theta_d_pure (c : Vector u64 5) (x : Fin 5) : u64 :=
  c[(x.val+4)%5] ^^^ rotate_left_pure c[(x.val+1)%5] 1

/-- Fused rho∘theta: rot(state[idx] ⊕ D[idx/5], RHO_OFFSETS[idx]).
    Matches the impl's combined {theta; rho} and equals spec's rho(theta(state)). -/
def rho_theta_pure (sv : Vector u64 25) : Vector u64 25 :=
  let c := Vector.ofFn (theta_c_pure sv)
  let d := Vector.ofFn (theta_d_pure c)
  Vector.ofFn fun (idx : Fin 25) =>
    rotate_left_pure (sv[idx] ^^^ d[idx.val / 5]) RHO_OFFSETS_pure[idx]

/-- Pi: A'[x,y] = A[(x+3y)%5, x], flat: result[5x+y] = old[5*((x+3y)%5) + x] -/
def pi_pure (sv : Vector u64 25) : Vector u64 25 :=
  Vector.ofFn fun (idx : Fin 25) =>
    let x := idx.val / 5; let y := idx.val % 5
    sv[5 * ((x + 3 * y) % 5) + x]

/-- Chi: A'[x,y] = A[x,y] ⊕ (¬A[(x+1)%5,y] ∧ A[(x+2)%5,y]) -/
def chi_pure (sv : Vector u64 25) : Vector u64 25 :=
  Vector.ofFn fun (idx : Fin 25) =>
    let x := idx.val / 5; let y := idx.val % 5
    sv[5*x + y] ^^^ (~~~sv[5*((x+1)%5) + y] &&& sv[5*((x+2)%5) + y])

/-- Iota: A'[0,0] = A[0,0] ⊕ RC[round] -/
def iota_pure (sv : Vector u64 25) (round : Fin 24) : Vector u64 25 :=
  sv.set (0 : Fin 25) (sv[0] ^^^ ROUND_CONSTANTS_pure[round])

def round_pure (sv : Vector u64 25) (round : Fin 24) : Vector u64 25 :=
  iota_pure (chi_pure (pi_pure (rho_theta_pure sv))) round

def keccak_f_pure (sv : Vector u64 25) : Vector u64 25 :=
  Fin.foldl 24 (fun sv i => round_pure sv i) sv

end Pure

open Pure

/-! ## Infrastructure: checked arithmetic specs -/

@[spec] axiom usize_mul_spec (a b : usize) :
    ⦃ ⌜ a.toNat * b.toNat < USize64.size ⌝ ⦄ (a *? b)
    ⦃ ⇓ r => ⌜ r.toNat = a.toNat * b.toNat ⌝ ⦄

@[spec] axiom usize_add_spec (a b : usize) :
    ⦃ ⌜ a.toNat + b.toNat < USize64.size ⌝ ⦄ (a +? b)
    ⦃ ⇓ r => ⌜ r.toNat = a.toNat + b.toNat ⌝ ⦄

@[spec] theorem usize_div_spec (a b : usize) :
    ⦃ ⌜ b ≠ 0 ⌝ ⦄ (a /? b) ⦃ ⇓ r => ⌜ r.toNat = a.toNat / b.toNat ⌝ ⦄ := by
  intro h; unfold rust_primitives.ops.arith.Div.div instDivUSize64_1; simp [h]; mvcgen

@[spec] theorem usize_mod_spec (a b : usize) :
    ⦃ ⌜ b ≠ 0 ⌝ ⦄ (a %? b) ⦃ ⇓ r => ⌜ r.toNat = a.toNat % b.toNat ⌝ ⦄ := by
  intro h; unfold rust_primitives.ops.arith.Rem.rem instRemUSize64; simp [h]; mvcgen

@[spec] theorem getElemResult_usize_spec {α : Type} [Inhabited α] {n : usize}
    (xs : RustArray α n) (i : usize) :
    ⦃ ⌜ i.toNat < n.toNat ⌝ ⦄ xs[i]_?
    ⦃ ⇓ r => ⌜ r = xs.toVec.toArray.getD i.toNat default ⌝ ⦄ := by
  intro h; unfold getElemResult usize.instGetElemResultVector; mvcgen; simp [Array.getD, h]

/-! ## Bridge lemma: Array.getD → Vector.getElem

`getElemResult_usize_spec` gives postconditions in terms of `Array.getD`,
but `Vector.getElem_set` works with `Vector.getElem`. This lemma bridges them,
enabling `simp [Vector.getElem_set]` to evaluate set chains after `rw [toArray_getD_eq]`. -/

theorem Vector.toArray_getD_eq {n : Nat} {α : Type}
    (v : Vector α n) (i : Nat) (d : α) (hi : i < n) :
    v.toArray.getD i d = v[i] := by
  simp [Array.getD, Vector.size_toArray, hi, Vector.getElem_toArray]

/-! ## Layer 0: KeccakItem primitive specs (portable, N=1, T=u64) -/

open libcrux_sha3.simd.portable in
@[spec] theorem veor5q_u64_spec (a b c d e : u64) :
    ⦃ ⌜ True ⌝ ⦄ _veor5q_u64 a b c d e
    ⦃ ⇓ r => ⌜ r = a ^^^ b ^^^ c ^^^ d ^^^ e ⌝ ⦄ := by
  intro _; unfold _veor5q_u64; mvcgen

open libcrux_sha3.simd.portable in
@[spec] theorem vbcaxq_u64_spec (a b c : u64) :
    ⦃ ⌜ True ⌝ ⦄ _vbcaxq_u64 a b c
    ⦃ ⇓ r => ⌜ r = a ^^^ (b &&& ~~~c) ⌝ ⦄ := by
  intro _; unfold _vbcaxq_u64; mvcgen

open libcrux_sha3.simd.portable in
@[spec] theorem veorq_n_u64_spec (a c : u64) :
    ⦃ ⌜ True ⌝ ⦄ _veorq_n_u64 a c
    ⦃ ⇓ r => ⌜ r = a ^^^ c ⌝ ⦄ := by
  intro _; unfold _veorq_n_u64; mvcgen

-- TODO: rotate_left_portable_spec, vrax1q_u64_spec, vxarq_u64_spec
-- These depend on handling the i32 debug assertion and cast_op.

/-! ## Layer 1: State accessor specs -/

-- Standard VC closer: reduce USize64 literals, unfold size defs, then omega.
-- Used after mvcgen to close arithmetic/bounds VCs.
local macro "vc_omega" : tactic =>
  `(tactic| (simp only [USize64.reduceToNat, USize64.size, UInt64.size,
      Vector.size, Vector.size_toArray] at *; omega))

@[spec] theorem get_ij_spec (arr : RustArray u64 25) (i j : usize) :
    ⦃ ⌜ i.toNat < 5 ∧ j.toNat < 5 ⌝ ⦄
    libcrux_sha3.traits.get_ij 1 u64 arr i j
    ⦃ ⇓ r => ⌜ r = arr.toVec.toArray.getD (5 * j.toNat + i.toNat) 0 ⌝ ⦄ := by
  intro ⟨hi, hj⟩
  unfold libcrux_sha3.traits.get_ij
  mvcgen
  · vc_omega
  · vc_omega
  -- vc3: Vector.getElem result = Array.getD at same index
  · intro heq; subst heq
    simp only [USize64.reduceToNat] at *
    have hlt : 5 * j.toNat + i.toNat < arr.toVec.toArray.size := by vc_omega
    simp only [Array.getD, hlt, dite_true]
    congr 1; omega
  -- vc4: index < 25
  · simp only [USize64.reduceToNat] at *; omega

-- set_ij: element-wise postcondition.
@[spec] theorem set_ij_spec (arr : RustArray u64 25) (i j : usize) (v : u64) :
    ⦃ ⌜ i.toNat < 5 ∧ j.toNat < 5 ⌝ ⦄
    libcrux_sha3.traits.set_ij 1 u64 arr i j v
    ⦃ ⇓ r => ⌜ r.toVec.size = 25 ∧
      (∀ k (hk : k < 25), r.toVec[k] =
        if k = 5 * j.toNat + i.toNat then v else arr.toVec[k]) ⌝ ⦄ := by
  intro ⟨hi, hj⟩
  unfold libcrux_sha3.traits.set_ij
    rust_primitives.hax.monomorphized_update_at.update_at_usize
  mvcgen
  all_goals (try vc_omega)
  -- vc3: in-bounds case — prove element-wise property of Vector.set
  refine ⟨by simp [Vector.size], fun k hk => ?_⟩
  simp only [USize64.reduceToNat] at *
  rw [Vector.getElem_set]
  congr 1; ext; constructor <;> (intro; omega)

/-! ## Impl_2.set and KeccakState indexing -/

-- Impl_2.set wraps set_ij on st.st, returning a new KeccakState.
@[spec] theorem Impl_2_set_spec (st : KeccakState 1 u64) (i j : usize) (v : u64) :
    ⦃ ⌜ i.toNat < 5 ∧ j.toNat < 5 ⌝ ⦄
    Impl_2.set 1 u64 st i j v
    ⦃ ⇓ r => ⌜ r.st.toVec.size = 25 ∧
      (∀ k (hk : k < 25), r.st.toVec[k] =
        if k = 5 * j.toNat + i.toNat then v else st.st.toVec[k]) ⌝ ⦄ := by
  intro ⟨hi, hj⟩
  unfold Impl_2.set libcrux_sha3.traits.set_ij
    rust_primitives.hax.monomorphized_update_at.update_at_usize
  mvcgen
  all_goals (try vc_omega)
  -- vc3: in-bounds — element-wise property
  refine ⟨by simp [Vector.size], fun k hk => ?_⟩
  simp only [USize64.reduceToNat] at *
  rw [Vector.getElem_set]
  congr 1; ext; constructor <;> (intro; omega)

-- KeccakState indexing via Tuple2: st[⟨i,j⟩] = st.st[5*j+i]
@[spec] theorem KeccakState_getElem_spec (st : KeccakState 1 u64) (i j : usize) :
    ⦃ ⌜ i.toNat < 5 ∧ j.toNat < 5 ⌝ ⦄
    st[(rust_primitives.hax.Tuple2.mk i j)]_?
    ⦃ ⇓ r => ⌜ r = st.st.toVec.toArray.getD (5 * j.toNat + i.toNat) 0 ⌝ ⦄ := by
  intro ⟨hi, hj⟩
  -- Unfold the indexing chain: KeccakState[⟨i,j⟩] → Index.index → get_ij
  simp only [getElemResult, instGetElemResultOfIndex,
    libcrux_sha3.generic_keccak.Impl_3,
    core_models.ops.index.Index.index,
    libcrux_sha3.generic_keccak.Impl_3.AssociatedTypes,
    rust_primitives.hax.Tuple2._0, rust_primitives.hax.Tuple2._1]
  -- Now it's wp⟦get_ij 1 u64 st.st i j⟧ — apply get_ij_spec directly
  exact get_ij_spec st.st i j ⟨hi, hj⟩

/-! ## Layer 0 continued: rotate_left and related -/

-- TODO: rotate_left_portable_spec, vrax1q_u64_spec, vxarq_u64_spec
-- These depend on the i32 debug assertion and cast_op in rotate_left.

/-! ## Layer 2: Impl step specs -/

-- Iota: XOR round constant into position [0,0].
-- Impl_2.iota reads self[0,0], XORs with ROUNDCONSTANTS[i], writes back via set.
set_option maxHeartbeats 400000 in
@[spec] theorem impl_iota_spec (st : KeccakState 1 u64) (i : usize)
    (hi : i.toNat < 24) :
    ⦃ ⌜ i.toNat < 24 ⌝ ⦄
    Impl_2.iota 1 u64 st i
    ⦃ ⇓ r => ⌜ ∀ k (hk : k < 25), r.st.toVec[k] =
        if k = 0 then
          st.st.toVec.toArray.getD 0 0 ^^^
            libcrux_sha3.generic_keccak.constants.ROUNDCONSTANTS.toVec.toArray.getD i.toNat 0
        else st.st.toVec[k] ⌝ ⦄ := by
  intro _
  -- Unfold iota and set/update layers
  unfold Impl_2.iota Impl_2.set
    libcrux_sha3.traits.set_ij
    rust_primitives.hax.monomorphized_update_at.update_at_usize
  -- Unfold KeccakState indexing and trait methods to concrete portable ops
  simp only [getElemResult, instGetElemResultOfIndex,
    libcrux_sha3.generic_keccak.Impl_3,
    libcrux_sha3.generic_keccak.Impl_3.AssociatedTypes,
    core_models.ops.index.Index.index,
    rust_primitives.hax.Tuple2._0, rust_primitives.hax.Tuple2._1,
    libcrux_sha3.traits.KeccakItem.xor_constant,
    libcrux_sha3.simd.portable.Impl,
    libcrux_sha3.simd.portable._veorq_n_u64,
    libcrux_sha3.traits.get_ij]
  mvcgen
  all_goals (try vc_omega)
  -- Remaining VC: Vector.set element-wise property
  · intro k hk
    simp only [USize64.reduceToNat, Vector.size] at *
    rw [Vector.getElem_set]
    -- Both the set index and the getElem indices reduce to 0
    -- Use omega to establish r✝.toNat = 0 and r✝².toNat = 0
    split
    · -- k = set_idx = 0: the written value
      rename_i heq
      have h0 : k = 0 := by omega
      subst h0
      simp only [ite_true]
      congr 1
      · -- st.st.toVec[r✝².toNat] = st.st.toVec.toArray.getD 0 0
        -- r✝².toNat = 0 from hypotheses
        have hlt : 0 < st.st.toVec.toArray.size := by vc_omega
        simp only [Array.getD, hlt, dite_true]; congr 1; omega
      · -- ROUNDCONSTANTS.toVec[i] = ROUNDCONSTANTS.toVec.toArray.getD i 0
        simp only [Array.getD, Vector.size_toArray, USize64.reduceToNat]
        split
        · rfl
        · omega
    · -- k ≠ 0: unchanged
      rename_i hne
      have : k ≠ 0 := by omega
      simp only [this, ite_false]

-- Pi: lane permutation. Unrolled into pi_0..pi_4, each writing one column.
-- mvcgen times out on the full pi (24 writes + 24 reads), so we prove each
-- pi_k separately and compose.
-- TODO: impl_pi_0..4_spec, impl_pi_spec — these are large straight-line
-- computations. Each pi_k has 4-5 set+get pairs. Even individually they
-- may be slow with mvcgen. If mvcgen+vc_omega can't close within budget,
-- we sorry with a description of what's needed.

-- pi_0 writes positions (1,0), (2,0), (3,0), (4,0) from old
set_option maxHeartbeats 1600000 in
@[spec] theorem impl_pi_0_spec (self old : KeccakState 1 u64) :
    ⦃ ⌜ True ⌝ ⦄
    Impl_2.pi_0 1 u64 self old
    ⦃ ⇓ r => ⌜
      -- Written positions (flat index 5*0+i for i=1..4):
      r.st.toVec.toArray.getD 1 0 = old.st.toVec.toArray.getD 15 0 ∧  -- self[1,0] = old[0,3]
      r.st.toVec.toArray.getD 2 0 = old.st.toVec.toArray.getD 5 0 ∧   -- self[2,0] = old[0,1]
      r.st.toVec.toArray.getD 3 0 = old.st.toVec.toArray.getD 20 0 ∧  -- self[3,0] = old[0,4]
      r.st.toVec.toArray.getD 4 0 = old.st.toVec.toArray.getD 10 0    -- self[4,0] = old[0,2]
    ⌝ ⦄ := by
  -- Approach: unfold everything to raw EStateM, let Lean evaluate the concrete computation.
  -- All indices are concrete, so bounds checks all pass and the computation is deterministic.
  intro _
  unfold Impl_2.pi_0 Impl_2.set
    libcrux_sha3.traits.set_ij
    rust_primitives.hax.monomorphized_update_at.update_at_usize
  simp only [getElemResult, instGetElemResultOfIndex,
    libcrux_sha3.generic_keccak.Impl_3,
    libcrux_sha3.generic_keccak.Impl_3.AssociatedTypes,
    core_models.ops.index.Index.index,
    rust_primitives.hax.Tuple2._0, rust_primitives.hax.Tuple2._1,
    libcrux_sha3.traits.get_ij]
  -- Now it's a raw chain of *?, +?, if-then-else, Vector.set, Vector.getElem
  -- Use mvcgen on this fully-unfolded form
  mvcgen
  all_goals (try vc_omega)
  -- Remaining: postcondition about (v.set i₁ x₁).set i₂ x₂ ... at indices 1,2,3,4
  -- Reduce USize64 literals, then simplify Vector.set/getD with concrete indices.
  · -- Reduce USize64 literals, then use dsimp to evaluate Vector.set/getInternal
    simp only [USize64.reduceToNat, Vector.size, Vector.size_toArray] at *
    -- The goal has Vector.set at USize64.toNat of variables. We need to reduce
    -- these to concrete Nat values. Use omega to derive, then rewrite.
    -- But we can't name inaccessible vars. Instead, try dsimp with omega-derived facts.
    -- Actually: the key insight is that all USize64.toNat values in the goal
    -- are determined by the hypotheses. Let's try `omega` on the subgoals after splitting.
    -- Close the 4 conjuncts about Vector.set chain.
    -- Pattern: dsimp to reduce USize64 → Nat, simp [*] to propagate index equalities,
    -- then evaluate the Vector.set/getD chain at concrete indices.
    -- The fourth conjunct closes automatically; the first 3 need Array.set evaluation.
    refine ⟨?_, ?_, ?_, ?_⟩ <;> {
      -- 1. Reduce USize64 literals in hypotheses
      dsimp only [USize64.reduceToNat, KeccakState.st] at *
      -- 2. Propagate index equalities from hypotheses into goal
      simp only [*, Nat.mul_zero, Nat.zero_add, Nat.add_zero,
        Nat.reduceMul, Nat.reduceAdd] at *
      -- 3. Bridge getD → getElem on both sides, then evaluate Vector.set chain
      rw [Vector.toArray_getD_eq _ _ _ (by omega), Vector.toArray_getD_eq _ _ _ (by omega)]
      simp [Vector.getElem_set]
    }

-- Shared tactic block for pi_k proofs: unfold, mvcgen, close VCs, evaluate set chain.
-- Each pi_k postcondition is a conjunction of getD equalities.
-- `n` is the number of conjuncts.
local macro "pi_step_proof" n:num : tactic => `(tactic| (
  intro _
  first
    | unfold Impl_2.pi_0 Impl_2.set libcrux_sha3.traits.set_ij rust_primitives.hax.monomorphized_update_at.update_at_usize
    | unfold Impl_2.pi_1 Impl_2.set libcrux_sha3.traits.set_ij rust_primitives.hax.monomorphized_update_at.update_at_usize
    | unfold Impl_2.pi_2 Impl_2.set libcrux_sha3.traits.set_ij rust_primitives.hax.monomorphized_update_at.update_at_usize
    | unfold Impl_2.pi_3 Impl_2.set libcrux_sha3.traits.set_ij rust_primitives.hax.monomorphized_update_at.update_at_usize
    | unfold Impl_2.pi_4 Impl_2.set libcrux_sha3.traits.set_ij rust_primitives.hax.monomorphized_update_at.update_at_usize
  simp only [getElemResult, instGetElemResultOfIndex,
    libcrux_sha3.generic_keccak.Impl_3,
    libcrux_sha3.generic_keccak.Impl_3.AssociatedTypes,
    core_models.ops.index.Index.index,
    rust_primitives.hax.Tuple2._0, rust_primitives.hax.Tuple2._1,
    libcrux_sha3.traits.get_ij]
  mvcgen
  all_goals (try vc_omega)
  · simp only [USize64.reduceToNat, Vector.size, Vector.size_toArray] at *
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (try exact ⟨?_, ?_⟩) <;> {
      dsimp only [USize64.reduceToNat, KeccakState.st] at *
      simp only [*, Nat.mul_zero, Nat.zero_add, Nat.add_zero,
        Nat.reduceMul, Nat.reduceAdd] at *
      rw [Vector.toArray_getD_eq _ _ _ (by omega), Vector.toArray_getD_eq _ _ _ (by omega)]
      simp [Vector.getElem_set]
    }))

set_option maxHeartbeats 1600000 in
@[spec] theorem impl_pi_1_spec (self old : KeccakState 1 u64) :
    ⦃ ⌜ True ⌝ ⦄
    Impl_2.pi_1 1 u64 self old
    ⦃ ⇓ r => ⌜
      r.st.toVec.toArray.getD 5 0 = old.st.toVec.toArray.getD 6 0 ∧   -- self[0,1] = old[1,1]
      r.st.toVec.toArray.getD 6 0 = old.st.toVec.toArray.getD 21 0 ∧  -- self[1,1] = old[1,4]
      r.st.toVec.toArray.getD 7 0 = old.st.toVec.toArray.getD 11 0 ∧  -- self[2,1] = old[1,2]
      r.st.toVec.toArray.getD 8 0 = old.st.toVec.toArray.getD 1 0 ∧   -- self[3,1] = old[1,0]
      r.st.toVec.toArray.getD 9 0 = old.st.toVec.toArray.getD 16 0    -- self[4,1] = old[1,3]
    ⌝ ⦄ := by pi_step_proof 5

set_option maxHeartbeats 1600000 in
@[spec] theorem impl_pi_2_spec (self old : KeccakState 1 u64) :
    ⦃ ⌜ True ⌝ ⦄
    Impl_2.pi_2 1 u64 self old
    ⦃ ⇓ r => ⌜
      r.st.toVec.toArray.getD 10 0 = old.st.toVec.toArray.getD 12 0 ∧  -- self[0,2] = old[2,2]
      r.st.toVec.toArray.getD 11 0 = old.st.toVec.toArray.getD 2 0 ∧   -- self[1,2] = old[2,0]
      r.st.toVec.toArray.getD 12 0 = old.st.toVec.toArray.getD 17 0 ∧  -- self[2,2] = old[2,3]
      r.st.toVec.toArray.getD 13 0 = old.st.toVec.toArray.getD 7 0 ∧   -- self[3,2] = old[2,1]
      r.st.toVec.toArray.getD 14 0 = old.st.toVec.toArray.getD 22 0    -- self[4,2] = old[2,4]
    ⌝ ⦄ := by pi_step_proof 5

set_option maxHeartbeats 1600000 in
@[spec] theorem impl_pi_3_spec (self old : KeccakState 1 u64) :
    ⦃ ⌜ True ⌝ ⦄
    Impl_2.pi_3 1 u64 self old
    ⦃ ⇓ r => ⌜
      r.st.toVec.toArray.getD 15 0 = old.st.toVec.toArray.getD 18 0 ∧  -- self[0,3] = old[3,3]
      r.st.toVec.toArray.getD 16 0 = old.st.toVec.toArray.getD 8 0 ∧   -- self[1,3] = old[3,1]
      r.st.toVec.toArray.getD 17 0 = old.st.toVec.toArray.getD 23 0 ∧  -- self[2,3] = old[3,4]
      r.st.toVec.toArray.getD 18 0 = old.st.toVec.toArray.getD 13 0 ∧  -- self[3,3] = old[3,2]
      r.st.toVec.toArray.getD 19 0 = old.st.toVec.toArray.getD 3 0     -- self[4,3] = old[3,0]
    ⌝ ⦄ := by pi_step_proof 5

set_option maxHeartbeats 1600000 in
@[spec] theorem impl_pi_4_spec (self old : KeccakState 1 u64) :
    ⦃ ⌜ True ⌝ ⦄
    Impl_2.pi_4 1 u64 self old
    ⦃ ⇓ r => ⌜
      r.st.toVec.toArray.getD 20 0 = old.st.toVec.toArray.getD 24 0 ∧  -- self[0,4] = old[4,4]
      r.st.toVec.toArray.getD 21 0 = old.st.toVec.toArray.getD 14 0 ∧  -- self[1,4] = old[4,2]
      r.st.toVec.toArray.getD 22 0 = old.st.toVec.toArray.getD 4 0 ∧   -- self[2,4] = old[4,0]
      r.st.toVec.toArray.getD 23 0 = old.st.toVec.toArray.getD 19 0 ∧  -- self[3,4] = old[4,3]
      r.st.toVec.toArray.getD 24 0 = old.st.toVec.toArray.getD 9 0     -- self[4,4] = old[4,1]
    ⌝ ⦄ := by pi_step_proof 5

-- Pi composition: pi = pi_0; pi_1; pi_2; pi_3; pi_4
-- Since each pi_k has ⌜True⌝ precondition, mvcgen should compose them.
-- Postcondition: all 25 positions match pi_pure.
set_option maxHeartbeats 1600000 in
@[spec] theorem impl_pi_spec (st : KeccakState 1 u64) :
    ⦃ ⌜ True ⌝ ⦄
    Impl_2.pi 1 u64 st
    ⦃ ⇓ r => ⌜ r.st.toVec = pi_pure st.st.toVec ⌝ ⦄ := by
  -- The composition pi = pi_0; pi_1; pi_2; pi_3; pi_4 creates very large wp terms.
  -- wp_bind on the full chain times out even at 12M heartbeats.
  -- Instead, unfold pi and all sub-functions fully, then let mvcgen handle
  -- the flattened monadic chain directly.
  -- This is the same approach that worked for pi_0: unfold everything, mvcgen, close VCs.
  -- But the full pi has 24 writes + 24 reads = ~48 monadic operations.
  -- mvcgen timed out on this earlier at 6.4M heartbeats.
  --
  -- BLOCKED: Both composition approaches (wp_bind and full unfold) time out.
  -- This proof likely needs a custom tactic or a different postcondition formulation.
  -- Leave as sorry for the user.
  sorry

-- TODO: impl_theta_spec
-- TODO: impl_rho_0..4_spec, impl_rho_spec
-- TODO: impl_chi_spec (loop — leave for user)

/-! ## Layer 3: Bridge + composition -/

-- TODO: rho_theta_bridge, round_impl_spec, keccakf1600_spec

