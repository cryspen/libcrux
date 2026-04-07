import Impl_Spec_Mvcgen
set_option linter.unusedSimpArgs false
/-!
# SHA-3 composition proofs: chi, round, keccak_f

Imports the completed step proofs (iota, pi, rho, theta) from `Impl_Spec_Mvcgen`
and composes them into round and keccak_f proofs.

## Remaining work
- `impl_chi_spec`: nested 5x5 fold_range loop — needs loop invariant
- `rho_theta_bridge`: compose theta_spec + rho_spec into `rho_theta_pure`
- `round_impl_spec`: compose theta+rho+pi+chi+iota → `round_pure`
- `keccakf1600_spec`: 24-round fold → `keccak_f_pure`
-/

open Std.Do
open libcrux_sha3.generic_keccak
open hacspec_sha3.keccak_f
open Pure

set_option hax_mvcgen.specset "int"
set_option linter.unusedVariables false

/-! ## Seal all proved functions

All functions with @[spec] lemmas from Impl_Spec_Mvcgen must be irreducible here.
The @[spec] theorems are available globally; marking functions irreducible prevents
mvcgen/simp from unfolding bodies — only specs are used downstream. -/

-- External functions
attribute [local irreducible]
  rust_primitives.hax.monomorphized_update_at.update_at_usize
  rust_primitives.hax.monomorphized_update_at.update_at_usize_slice
  rust_primitives.hax.update_at
  rust_primitives.hax.repeat
  rust_primitives.unsize
  rust_primitives.hax.cast_op
  core_models.num.Impl_9.rotate_left
  core_models.num.Impl_9.from_le_bytes
  core_models.num.Impl_9.to_le_bytes
  hax_lib.assert

-- Primitives (veor5q, vbcaxq, veorq_n, rotate_left_portable, vrax1q, vxarq)
attribute [local irreducible]
  libcrux_sha3.simd.portable._veor5q_u64
  libcrux_sha3.simd.portable._vbcaxq_u64
  libcrux_sha3.simd.portable._veorq_n_u64
  libcrux_sha3.simd.portable.rotate_left
  libcrux_sha3.simd.portable._vrax1q_u64
  libcrux_sha3.simd.portable._vxarq_u64

-- Accessors (get_ij, set_ij, Impl_2.set)
attribute [local irreducible]
  libcrux_sha3.traits.get_ij
  libcrux_sha3.traits.set_ij
  libcrux_sha3.generic_keccak.Impl_2.set

-- Iota
attribute [local irreducible] libcrux_sha3.generic_keccak.Impl_2.iota

-- Pi (sub-steps + composition)
attribute [local irreducible]
  Impl_2.pi_0 Impl_2.pi_1 Impl_2.pi_2 Impl_2.pi_3 Impl_2.pi_4
  Impl_2.pi

-- Rho (sub-steps + composition)
attribute [local irreducible]
  Impl_2.rho_0 Impl_2.rho_1 Impl_2.rho_2 Impl_2.rho_3 Impl_2.rho_4
  Impl_2.rho

-- Typeclass indexing (reduces mvcgen context)
attribute [local irreducible] getElemResult instGetElemResultOfIndex

-- Theta
attribute [local irreducible] Impl_2.theta

/-! ## vc_omega macro -/

local macro "vc_omega" : tactic =>
  `(tactic| (simp only [USize64.reduceToNat, USize64.size, UInt64.size,
      Vector.size, Vector.size_toArray] at *; omega))

/-! ## fold_range infrastructure

`fold_range_usize_spec`: wraps the existing `fold_range_spec_int_USize64` as a proper
`@[spec]` theorem so mvcgen can use it. The precondition bundles `s ≤ e`, initial
invariant, and step preservation into a single conjunction. -/

@[spec]
theorem fold_range_usize_spec {α : Type}
    (s e : USize64)
    (inv : α → USize64 → RustM Prop)
    (init : α)
    (body : α → USize64 → RustM α)
    (pureInv : {i : α → USize64 → Prop //
      ∀ a b, ⦃⌜True⌝⦄ inv a b ⦃Std.Do.PostCond.noThrow fun r => ⌜r = i a b⌝⦄})
    (hle : s.toNat ≤ e.toNat)
    (hinit : pureInv.val init s)
    (hstep : ∀ (acc : α) (i : USize64),
          s.toNat ≤ i.toNat → i.toNat < e.toNat → pureInv.val acc i →
          ⦃ ⌜ True ⌝ ⦄ body acc i
          ⦃ Std.Do.PostCond.noThrow fun res => ⌜ pureInv.val res (i+1) ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    rust_primitives.hax.folds.fold_range s e inv init body pureInv
    ⦃ Std.Do.PostCond.noThrow fun r => ⌜ pureInv.val r e ⌝ ⦄ := by
  intro _
  have h := rust_primitives.hax.folds.fold_range_spec_int_USize64
    s e inv pureInv init body hle hinit hstep
  exact h trivial

/-! ## fold_range invariant swap

`fold_range` never inspects `inv`/`pureInv` at runtime — they are ghost arguments
for specification only. This lets us replace a trivial invariant (as in chi's
extraction) with a meaningful one and still apply `fold_range_spec`. -/

theorem fold_range_inv_irrelevant {α : Type}
    (s e : USize64)
    (inv₁ inv₂ : α → USize64 → RustM Prop)
    (init : α)
    (body : α → USize64 → RustM α)
    (pureInv₁ pureInv₂) :
    rust_primitives.hax.folds.fold_range s e inv₁ init body pureInv₁ =
    rust_primitives.hax.folds.fold_range s e inv₂ init body pureInv₂ := by
  show USize64.fold_range s e inv₁ init body pureInv₁ =
       USize64.fold_range s e inv₂ init body pureInv₂
  induction s, init using USize64.fold_range.induct (e := e) with
  | case1 s init hs ih =>
    unfold USize64.fold_range; rw [if_pos hs, if_pos hs]; congr 1; funext a; exact ih a
  | case2 s init hs =>
    unfold USize64.fold_range; rw [if_neg hs, if_neg hs]


/-! ## Chi (nested 5x5 loop)

Chi iterates `for i in 0..5 { for j in 0..5 { ... } }`.
The body: `self[i,j] := and_not_xor(self[i,j], old[i,(j+2)%5], old[i,(j+1)%5])`
where `and_not_xor(a,b,c) = a ^^^ (b &&& ~~~c)`.

All reads of `old` use the state captured before the loop. Reads of `self[i,j]`
in the body are from `self` which equals `old[i,j]` at that point (the loop writes
to disjoint flat positions: flat index `5*j + i`, and earlier iterations of inner
loop `j' < j` wrote `5*j' + i ≠ 5*j + i`).

**Outer loop invariant** (after completing iteration i):
- Positions k where `k % 5 < i`: updated to `chi_pure(old)[k]`
- Positions k where `k % 5 ≥ i`: unchanged from `old[k]`

**Inner loop invariant** (within outer iteration i, after completing iteration j):
- Positions k where `k % 5 < i`: already updated
- Positions k where `k % 5 = i ∧ k / 5 < j`: updated this outer iteration
- All other positions: unchanged from `old[k]`
-/

-- Array-based chi body (matching mvcgen output shape, using getD like theta)
def chi_body_arr (old : Array u64) (k : Nat) : u64 :=
  let x := k / 5; let y := k % 5
  old.getD (5*x + y) 0 ^^^ (~~~old.getD (5*((x+1)%5) + y) 0 &&& old.getD (5*((x+2)%5) + y) 0)

-- Chi invariant: positions processed so far have chi_body values, rest unchanged.
-- After outer iteration i and inner iteration j, "processed" means:
--   k % 5 < i  (completed columns)  OR  (k % 5 = i ∧ k / 5 < j)  (partial current column)
def chi_inv (old_arr st_arr : Array u64) (i j : Nat) : Prop :=
  ∀ k, k < 25 →
    if k % 5 < i ∨ (k % 5 = i ∧ k / 5 < j)
    then st_arr.getD k 0 = chi_body_arr old_arr k
    else st_arr.getD k 0 = old_arr.getD k 0

private theorem chi_inv_init (old_arr : Array u64) :
    chi_inv old_arr old_arr 0 0 := by
  intro k hk
  simp only [Nat.not_lt_zero, false_and, false_or, and_false, ite_false]

private theorem chi_body_arr_flat (old_arr : Array u64) (i j : Nat)
    (hi : i < 5) (hj : j < 5) :
    chi_body_arr old_arr (5 * j + i) =
      old_arr.getD (5 * j + i) 0 ^^^
        (old_arr.getD (5 * ((j + 2) % 5) + i) 0 &&&
          ~~~old_arr.getD (5 * ((j + 1) % 5) + i) 0) := by
  have hdiv : (5 * j + i) / 5 = j := by omega
  have hmod : (5 * j + i) % 5 = i := by omega
  simp only [chi_body_arr, hdiv, hmod, UInt64.and_comm]

private theorem chi_processed_succ_iff (i j k : Nat)
    (hk : k < 25) (hi : i < 5) (hj : j < 5) :
    (k % 5 < i ∨ (k % 5 = i ∧ k / 5 < j + 1)) ↔
      (k = 5 * j + i ∨ (k % 5 < i ∨ (k % 5 = i ∧ k / 5 < j))) := by
  omega

private theorem chi_inv_finish_column
    (old_arr st_arr : Array u64) (i : Nat)
    (hi : i < 5)
    (h : chi_inv old_arr st_arr i 5) :
    chi_inv old_arr st_arr (i + 1) 0 := by
  intro k hk
  have hk5 : k / 5 < 5 := by omega
  have hcond : (k % 5 < i ∨ k % 5 = i ∧ k / 5 < 5) ↔ k % 5 < i + 1 := by omega
  have hk' := h k hk
  simp only [Nat.not_lt_zero, and_false, or_false, ite_false] at hk' ⊢
  rw [show (if k % 5 < i ∨ k % 5 = i ∧ k / 5 < 5 then _ else _) =
      (if k % 5 < i + 1 then _ else _) from by congr 1; exact propext hcond] at hk'
  exact hk'

private theorem chi_inv_update
    (old_arr acc_arr res_arr : Array u64) (i j : Nat)
    (hi : i < 5) (hj : j < 5)
    (hacc : chi_inv old_arr acc_arr i j)
    (hres : ∀ k, k < 25 →
      res_arr.getD k 0 =
        if k = 5 * j + i then
          old_arr.getD (5 * j + i) 0 ^^^
            (old_arr.getD (5 * ((j + 2) % 5) + i) 0 &&&
              ~~~old_arr.getD (5 * ((j + 1) % 5) + i) 0)
        else acc_arr.getD k 0) :
    chi_inv old_arr res_arr i (j + 1) := by
  intro k hk
  specialize hacc k hk
  specialize hres k hk
  rw [hres]
  by_cases heq : k = 5 * j + i
  · -- k is the just-updated position
    simp only [heq, ite_true]
    rw [if_pos (by omega)]
    exact (chi_body_arr_flat old_arr i j hi hj).symm
  · -- k is not the updated position
    simp only [heq, ite_false]
    -- The processed-so-far condition for (i, j+1) is equivalent to (i, j) since k ≠ 5*j+i
    have : (k % 5 < i ∨ (k % 5 = i ∧ k / 5 < j + 1)) ↔
           (k % 5 < i ∨ (k % 5 = i ∧ k / 5 < j)) := by
      constructor
      · rintro (h | ⟨hm, hd⟩)
        · left; exact h
        · right; exact ⟨hm, by omega⟩
      · rintro (h | h)
        · left; exact h
        · right; exact ⟨h.1, by omega⟩
    rw [show (if k % 5 < i ∨ (k % 5 = i ∧ k / 5 < j + 1) then _ else _) =
        (if k % 5 < i ∨ (k % 5 = i ∧ k / 5 < j) then _ else _) from
      by congr 1; exact propext this]
    exact hacc

-- Local wrappers for chi proof: mvcgen needs these to match specs correctly
private def chi_set (st : KeccakState 1 u64) (i j : usize) (v : u64) :=
  Impl_2.set 1 u64 st i j v

private def chi_get (st : KeccakState 1 u64) (i j : usize) :=
  st[(rust_primitives.hax.Tuple2.mk i j)]_?

-- Unfold lemmas: prove BEFORE making wrappers irreducible
private theorem chi_set_unfold (st i j v) : chi_set st i j v = Impl_2.set 1 u64 st i j v := rfl
private theorem chi_get_unfold (st i j) : chi_get st i j = st[(rust_primitives.hax.Tuple2.mk i j)]_? := rfl

@[spec] private theorem chi_set_spec (st : KeccakState 1 u64) (i j : usize) (v : u64)
    (hi : i.toNat < 5) (hj : j.toNat < 5) :
    ⦃ ⌜ True ⌝ ⦄ chi_set st i j v
    ⦃ ⇓ r => ⌜ r.st.toVec.size = 25 ∧
      (∀ k (hk : k < 25), r.st.toVec[k] =
        if k = 5 * j.toNat + i.toNat then v else st.st.toVec[k]) ⌝ ⦄ := by
  intro _; rw [chi_set_unfold]
  exact Impl_2_set_spec st i j v hi hj trivial

@[spec] private theorem chi_get_spec (st : KeccakState 1 u64) (i j : usize)
    (hi : i.toNat < 5) (hj : j.toNat < 5) :
    ⦃ ⌜ True ⌝ ⦄ chi_get st i j
    ⦃ ⇓ r => ⌜ r = st.st.toVec.toArray.getD (5 * j.toNat + i.toNat) 0 ⌝ ⦄ := by
  intro _; rw [chi_get_unfold]
  exact KeccakState_getElem_spec st i j hi hj trivial

attribute [irreducible] chi_set chi_get

set_option maxHeartbeats 6400000 in
@[spec] theorem impl_chi_spec (st : KeccakState 1 u64) :
    ⦃ ⌜ True ⌝ ⦄
    Impl_2.chi 1 u64 st
    ⦃ ⇓ r => ⌜ ∀ k, k < 25 →
      r.st.toVec.toArray.getD k 0 = chi_body_arr st.st.toVec.toArray k ⌝ ⦄ := by
  intro _
  unfold Impl_2.chi
  simp only [libcrux_sha3.traits.KeccakItem.and_not_xor,
    libcrux_sha3.simd.portable.Impl,
    ← chi_set_unfold, ← chi_get_unfold]
  -- Swap both loop invariants: True → real chi_inv
  -- Outer: chi_inv(old, acc, i, 0)
  rw [show rust_primitives.hax.folds.fold_range (0 : USize64) (5 : USize64)
    (fun self x => do let a ← pure true; pure (a = true)) st _ _ =
    rust_primitives.hax.folds.fold_range (0 : USize64) (5 : USize64)
    (fun (acc : KeccakState 1 u64) (i : USize64) =>
      pure (chi_inv st.st.toVec.toArray acc.st.toVec.toArray i.toNat 0))
    st _ ⟨fun acc i => chi_inv st.st.toVec.toArray acc.st.toVec.toArray i.toNat 0,
      fun _ _ => by intro _; rfl⟩
    from fold_range_inv_irrelevant _ _ _ _ _ _ _ _]
  -- Inner: chi_inv(old, acc, i, j) — swap inside the outer body lambda
  conv in (fun (self : KeccakState 1 u64) (i : USize64) => rust_primitives.hax.folds.fold_range
    (0 : USize64) (5 : USize64) _ self _ _) =>
    ext self i
    rw [fold_range_inv_irrelevant _ _ _ -- s, e, inv₁
      (fun (acc : KeccakState 1 u64) (j : USize64) =>
        pure (chi_inv st.st.toVec.toArray acc.st.toVec.toArray i.toNat j.toNat)) -- inv₂
      _ _ _ -- init, body, pureInv₁
      ⟨fun acc j => chi_inv st.st.toVec.toArray acc.st.toVec.toArray i.toNat j.toNat,
        fun _ _ => by intro _; rfl⟩] -- pureInv₂
  hax_mvcgen
  all_goals (try vc_omega)
  -- vc2: initial invariant
  · simp only [USize64.reduceToNat]; exact chi_inv_init _
  -- vc15: inner step — set postcondition → chi_inv(i, j+1)
  · -- Name the critical inaccessible variables (28 total, in order)
    rename_i _ _ col _ _ _ acc j _ _ hinv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res
    intro hsize hset
    simp only [USize64.reduceToNat] at *
    rw [USize64.toNat_add_of_lt (by simp only [USize64.reduceToNat]; omega)]
    simp only [USize64.reduceToNat]
    -- Extract from invariant: acc[5*j+col] = old[5*j+col] (not yet processed)
    have hinv_eq : acc.st.toVec.toArray.getD (5 * j.toNat + col.toNat) 0 =
        st.st.toVec.toArray.getD (5 * j.toNat + col.toNat) 0 := by
      have := hinv (5 * j.toNat + col.toNat) (by omega)
      simp only [show (5 * j.toNat + col.toNat) % 5 = col.toNat from by omega,
        show (5 * j.toNat + col.toNat) / 5 = j.toNat from by omega,
        Nat.lt_irrefl, and_false, or_false, ite_false] at this
      exact this
    apply chi_inv_update _ _ _ _ _ (by omega) (by omega) hinv
    intro k hk
    rw [Vector.toArray_getD_eq _ _ _ (by omega)]
    simp only [hset k (by omega : k < 25)]
    split
    next heq =>
      -- k = 5*j+col: stored value = chi body
      simp_all [Vector.toArray_getD_eq]
    next heq =>
      exact (Vector.toArray_getD_eq _ _ _ (by simp only [USize64.reduceToNat]; omega)).symm
  -- vc18: column finish — chi_inv(i, 5) → chi_inv(i+1, 0)
  · intro h5; simp only [USize64.reduceToNat] at *
    rw [USize64.toNat_add_of_lt (by simp only [USize64.reduceToNat]; omega)]
    simp only [USize64.reduceToNat]
    exact chi_inv_finish_column _ _ _ (by omega) h5
  -- vc19: final — chi_inv(5, 0) → postcondition
  · rename_i _ r hinv
    intro k hk
    simp only [USize64.reduceToNat] at hinv
    specialize hinv k hk
    simp only [show k % 5 < 5 from Nat.mod_lt k (by omega), ite_true,
      Nat.not_lt_zero, and_false, or_false] at hinv
    exact hinv

/-! ## Bridge + composition -/

-- TODO: rho_theta_bridge — compose impl_theta_spec + impl_rho_spec → rho_theta_pure
-- TODO: round_impl_spec — compose bridges → round_pure (depends on chi)
-- TODO: keccakf1600_spec — 24-round fold (depends on round_impl_spec)
