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

/-! ## Round + keccak_f composition -/

-- Seal chi after proof
attribute [local irreducible] Impl_2.chi

-- Local wrapper for iota (mvcgen needs this to handle the hi parameter)
private def round_iota (st : KeccakState 1 u64) (i : usize) :=
  Impl_2.iota 1 u64 st i

private theorem round_iota_unfold (st i) : round_iota st i = Impl_2.iota 1 u64 st i := rfl

@[spec] private theorem round_iota_spec (st : KeccakState 1 u64) (i : usize)
    (hi : i.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄ round_iota st i
    ⦃ ⇓ r => ⌜ ∀ k (hk : k < 25), r.st.toVec[k] =
        if k = 0 then
          st.st.toVec.toArray.getD 0 0 ^^^
            libcrux_sha3.generic_keccak.constants.ROUNDCONSTANTS.toVec.toArray.getD i.toNat 0
        else st.st.toVec[k] ⌝ ⦄ := by
  intro _; rw [round_iota_unfold]
  exact impl_iota_spec st i hi trivial

attribute [irreducible] round_iota

/-! ### Bridge lemmas: element-wise specs → pure functions

Each step spec gives element-wise getD postconditions. These bridges
show the output Vector equals the pure function, via Vector.ext. -/

private theorem iota_bridge (sv rv : Vector u64 25) (i : Nat) (hi : i < 24)
    (h : ∀ k (hk : k < 25), rv[k]'(by omega) =
      if k = 0 then sv.toArray.getD 0 0 ^^^
        ROUND_CONSTANTS_pure[i]'(by omega)
      else sv[k]'(by omega)) :
    rv = iota_pure sv ⟨i, hi⟩ := by
  apply Vector.ext; intro k; intro hk
  specialize h k hk; rw [h]
  simp only [iota_pure, Vector.getElem_set, Vector.toArray_getD_eq _ _ _ (by omega : 0 < 25)]
  split <;> (split <;> simp_all)

set_option linter.unusedSimpArgs false in
private theorem chi_bridge (sv rv : Vector u64 25)
    (h : ∀ k, k < 25 → rv.toArray.getD k 0 = chi_body_arr sv.toArray k) :
    rv = chi_pure sv := by
  apply Vector.ext; intro k; intro hk
  rw [← Vector.toArray_getD_eq rv k 0 hk, h k hk]
  simp only [chi_pure, Vector.getElem_ofFn, chi_body_arr]
  rw [Vector.toArray_getD_eq _ _ _ (by omega),
      Vector.toArray_getD_eq _ _ _ (by omega),
      Vector.toArray_getD_eq _ _ _ (by omega),
      UInt64.and_comm]

private theorem pi_bridge (sv rv : Vector u64 25)
    (h : ∀ k (_ : k < 25), rv.toArray.getD k 0 = sv.toArray.getD (pi_perm_table.getD k 0) 0) :
    rv = pi_pure sv := by
  apply Vector.ext; intro k; intro hk
  rw [← Vector.toArray_getD_eq rv k 0 hk, h k hk]
  simp only [pi_pure, Vector.getElem_ofFn]
  -- Verify pi_perm_table matches pi_pure by exhaustion on k
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨
    k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨
    k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24
    by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [pi_perm_table, List.getD, Vector.toArray_getD_eq] <;> rfl

-- theta_c: Array helper = pure function
private theorem theta_c_arr_eq_pure (sv : Vector u64 25) (j : Nat) (hj : j < 5) :
    theta_c_arr sv.toArray j = theta_c_pure sv ⟨j, hj⟩ := by
  simp only [theta_c_arr, theta_c_pure]
  rw [Vector.toArray_getD_eq _ _ _ (by omega), Vector.toArray_getD_eq _ _ _ (by omega),
      Vector.toArray_getD_eq _ _ _ (by omega), Vector.toArray_getD_eq _ _ _ (by omega),
      Vector.toArray_getD_eq _ _ _ (by omega)]

-- theta_d: Array helper = pure function (uses theta_c bridge)
private theorem theta_d_arr_eq_pure (sv : Vector u64 25) (j : Nat) (hj : j < 5) :
    theta_d_arr sv.toArray j = theta_d_pure (Vector.ofFn (theta_c_pure sv)) ⟨j, hj⟩ := by
  simp only [theta_d_arr, theta_d_pure, Vector.getElem_ofFn]
  rw [theta_c_arr_eq_pure sv _ (by omega), theta_c_arr_eq_pure sv _ (by omega)]

-- Rho offsets: hardcoded list matches RHO_OFFSETS_pure after Int32.toUInt32
private theorem rho_offsets_eq (k : Nat) (hk : k < 25) :
    (Int32.toUInt32
      ([0,36,3,41,18,1,44,10,45,2,62,6,43,15,61,28,55,25,21,56,27,20,39,8,14].getD k 0)) =
    RHO_OFFSETS_pure[k]'(by omega) := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨
    k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨
    k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24
    by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  native_decide +revert

-- Full rho∘theta bridge
set_option maxHeartbeats 400000 in
private theorem rho_theta_bridge (sv rv : Vector u64 25) (d_arr : Array u64)
    (hd : ∀ j, j < 5 → d_arr.getD j 0 = theta_d_arr sv.toArray j)
    (hrho : ∀ k (_ : k < 25), rv.toArray.getD k 0 =
      rotate_left_pure (sv.toArray.getD k 0 ^^^ d_arr.getD (k / 5) 0)
        (Int32.toUInt32
          ([0,36,3,41,18,1,44,10,45,2,62,6,43,15,61,28,55,25,21,56,27,20,39,8,14].getD k 0))) :
    rv = rho_theta_pure sv := by
  apply Vector.ext; intro k; intro hk
  -- Unfold RHS
  simp only [rho_theta_pure, Vector.getElem_ofFn]
  -- Rewrite LHS to match
  rw [← Vector.toArray_getD_eq rv k 0 hk, hrho k hk,
      Vector.toArray_getD_eq _ _ _ hk,
      hd (k / 5) (by omega),
      theta_d_arr_eq_pure sv (k / 5) (by omega),
      rho_offsets_eq k hk,
      show sv[k]'hk = sv[(⟨k, hk⟩ : Fin 25)] from rfl,
      show RHO_OFFSETS_pure[k]'hk = RHO_OFFSETS_pure[(⟨k, hk⟩ : Fin 25)] from rfl]

attribute [local irreducible] round_pure

set_option maxHeartbeats 6400000 in
theorem round_body_spec (st : KeccakState 1 u64) (i : usize) (hi : i.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let ⟨tmp0, out⟩ ← Impl_2.theta 1 u64 st
        let self := tmp0; let t := out
        let self ← Impl_2.rho 1 u64 self t
        let self ← Impl_2.pi 1 u64 self
        let self ← Impl_2.chi 1 u64 self
        let self ← round_iota self i
        pure self)
    ⦃ ⇓ r => ⌜ r.st.toVec = round_pure st.st.toVec ⟨i.toNat, hi⟩ ⌝ ⦄ := by
  intro _
  hax_mvcgen
  -- Single remaining VC: chain specs via bridge lemmas → round_pure
  -- Name: _ r_θ h_θ r_ρ h_ρ r_π h_π r_χ h_χ r_ι h_ι
  rename_i _ _ h_θ _ h_ρ _ h_π _ h_χ _ h_ι
  obtain ⟨hst_eq, hd⟩ := h_θ
  subst hst_eq
  unfold round_pure
  rw [← iota_bridge _ _ _ hi h_ι,
      ← chi_bridge _ _ h_χ,
      ← pi_bridge _ _ h_π,
      ← rho_theta_bridge _ _ _ hd h_ρ]
