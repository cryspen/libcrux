import Hax
import extraction.libcrux_intrinsics
import extraction.libcrux_sha3
import extraction.hacspec_sha3
import equivalence.Spec_Pure_Defs
import Std.Do.Triple
import Std.Tactic.Do

/-!
# SHA-3 implementation verification via mvcgen

Proves that the portable implementation (`N=1, T=u64`) of each Keccak-f step
matches the pure spec definitions in `Spec_Pure_Defs.lean`.

The implementation functions live in `libcrux_sha3.generic_keccak.Impl_2`.
They are generic over `N` (lane count) and `T` (element type) with a `KeccakItem`
trait. For portable verification, we instantiate at `N=1, T=u64`.
-/

open Std.Do
open libcrux_sha3.generic_keccak
open Spec.Pure

/-! ## Infrastructure: checked arithmetic specs (same as Spec_Pure_Mvcgen) -/

@[spec] axiom usize_mul_spec (a b : usize) :
    ⦃ ⌜ a.toNat * b.toNat < USize64.size ⌝ ⦄ (a *? b)
    ⦃ ⇓ r => ⌜ r.toNat = a.toNat * b.toNat ⌝ ⦄
@[spec] axiom usize_add_spec (a b : usize) :
    ⦃ ⌜ a.toNat + b.toNat < USize64.size ⌝ ⦄ (a +? b)
    ⦃ ⇓ r => ⌜ r.toNat = a.toNat + b.toNat ⌝ ⦄

@[spec] theorem getElemResult_usize_spec {α : Type} [Inhabited α] {n : usize}
    (xs : RustArray α n) (i : usize) :
    ⦃ ⌜ i.toNat < n.toNat ⌝ ⦄ xs[i]_?
    ⦃ ⇓ r => ⌜ r = xs.toVec.toArray.getD i.toNat default ⌝ ⦄ := by
  intro h; unfold getElemResult usize.instGetElemResultVector; mvcgen; simp [Array.getD, h]

/-! ## Infrastructure: KeccakState access -/

-- get_ij: arr[5*j + i] — the impl's state accessor
@[spec] theorem get_ij_spec (arr : RustArray u64 25) (i j : usize) :
    ⦃ ⌜ i.toNat < 5 ∧ j.toNat < 5 ⌝ ⦄
    libcrux_sha3.traits.get_ij 1 u64 arr i j
    ⦃ ⇓ r => ⌜ r = arr.toVec.toArray.getD (5 * j.toNat + i.toNat) 0 ⌝ ⦄ := by
  intro ⟨hi, hj⟩; unfold libcrux_sha3.traits.get_ij
  -- get_ij is just arr[5*j + i], same as spec's get but with swapped axes
  sorry

/-! ## Iota (simplest step — validates the approach) -/

-- iota: XORs round constant into cell [0,0]
-- Impl: `Impl_2.iota 1 u64 st i` uses `KeccakItem.xor_constant`
-- Spec: `iota_pure st.toVec ⟨i, h⟩` = `st.set 0 (st[0] ^^^ ROUND_CONSTANTS_pure[i])`

set_option maxHeartbeats 6400000 in
@[spec] theorem iota_impl_spec (st : KeccakState 1 u64) (i : usize) (h : i.toNat < 24) :
    ⦃ ⌜ i.toNat < 24 ⌝ ⦄ Impl_2.iota 1 u64 st i
    ⦃ ⇓ r => ⌜ r.st.toVec = iota_pure st.st.toVec ⟨i.toNat, h⟩ ⌝ ⦄ := by
  intro _; unfold Impl_2.iota Impl_2.set iota_pure; mvcgen
  all_goals sorry

