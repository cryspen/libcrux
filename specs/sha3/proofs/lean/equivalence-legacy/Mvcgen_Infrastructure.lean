import Hax
import Stubs
import Std.Do.Triple
import Std.Tactic.Do

/-!
# Shared mvcgen infrastructure

`@[spec]` lemmas for checked arithmetic, array access, and VC-closing tactics.
Imported by both `Spec_Pure_Mvcgen.lean` (spec verification) and
`Impl_Spec_Mvcgen.lean` (impl verification).
-/

open Std.Do

/-! ## Checked arithmetic specs -/

@[spec] theorem usize_div_spec (a b : usize) :
    ⦃ ⌜ b ≠ 0 ⌝ ⦄ (a /? b) ⦃ ⇓ r => ⌜ r.toNat = a.toNat / b.toNat ⌝ ⦄ := by
  intro h; unfold rust_primitives.ops.arith.Div.div instDivUSize64_1; simp [h]; mvcgen

@[spec] theorem usize_mod_spec (a b : usize) :
    ⦃ ⌜ b ≠ 0 ⌝ ⦄ (a %? b) ⦃ ⇓ r => ⌜ r.toNat = a.toNat % b.toNat ⌝ ⦄ := by
  intro h; unfold rust_primitives.ops.arith.Rem.rem instRemUSize64; simp [h]; mvcgen

@[spec] axiom usize_mul_spec (a b : usize) :
    ⦃ ⌜ a.toNat * b.toNat < USize64.size ⌝ ⦄ (a *? b)
    ⦃ ⇓ r => ⌜ r.toNat = a.toNat * b.toNat ⌝ ⦄
@[spec] axiom usize_add_spec (a b : usize) :
    ⦃ ⌜ a.toNat + b.toNat < USize64.size ⌝ ⦄ (a +? b)
    ⦃ ⇓ r => ⌜ r.toNat = a.toNat + b.toNat ⌝ ⦄

/-! ## Array/slice access -/

@[spec] theorem getElemResult_usize_spec {α : Type} [Inhabited α] {n : usize}
    (xs : RustArray α n) (i : usize) :
    ⦃ ⌜ i.toNat < n.toNat ⌝ ⦄ xs[i]_?
    ⦃ ⇓ r => ⌜ r = xs.toVec.toArray.getD i.toNat default ⌝ ⦄ := by
  intro h; unfold getElemResult usize.instGetElemResultVector; mvcgen; simp [Array.getD, h]

/-! ## Lane index bound -/

/-- `5 * (d % 5) + d / 5 < 25` whenever `d < 25`.
    This is a nonlinear fact that omega cannot derive on its own. -/
theorem lane_index_bound {d : Nat} (hd : d < 25) : 5 * (d % 5) + d / 5 < 25 := by
  have h1 : d % 5 < 5 := Nat.mod_lt _ (by omega)
  have h2 : d / 5 < 5 := Nat.div_lt_of_lt_mul (by omega)
  omega

/-! ## USize64 numeral reduction -/

-- USize64.reduceToNat doesn't fire reliably in all simp/dsimp contexts.
-- These explicit lemmas ensure omega sees concrete Nat values.
theorem usize_toNat_0  : (0  : usize).toNat = 0   := by native_decide
theorem usize_toNat_1  : (1  : usize).toNat = 1   := by native_decide
theorem usize_toNat_2  : (2  : usize).toNat = 2   := by native_decide
theorem usize_toNat_3  : (3  : usize).toNat = 3   := by native_decide
theorem usize_toNat_4  : (4  : usize).toNat = 4   := by native_decide
theorem usize_toNat_5  : (5  : usize).toNat = 5   := by native_decide
theorem usize_toNat_8  : (8  : usize).toNat = 8   := by native_decide
theorem usize_toNat_24 : (24 : usize).toNat = 24  := by native_decide
theorem usize_toNat_25 : (25 : usize).toNat = 25  := by native_decide
theorem usize_toNat_200 : (200 : usize).toNat = 200 := by native_decide
