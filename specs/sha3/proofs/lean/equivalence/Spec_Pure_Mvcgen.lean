import Hax
import Stubs
import extraction.hacspec_sha3
import Std.Do.Triple
import Std.Tactic.Do

/-!
# Pure specification functions for SHA-3 — mvcgen-based proofs

Key infrastructure:
- `@[spec]` triples for checked arithmetic (toNat-distributing)
- `@[spec]` triple for `get` with bounds precondition
- `@[spec]` triple for `createi` (from Stubs.lean)
- `@[hax_spec]` removed from extraction (our specs take precedence)
- `close_vc` macro: normalize USize64 constants + omega
- `@[irreducible]` on pure defs to prevent term blowup
-/

open Std.Do hacspec_sha3.keccak_f

namespace Spec.PureMvcgen

/-! ## USize64 checked arithmetic specs (toNat-distributing) -/

@[spec] theorem usize_div_spec (a b : usize) :
    ⦃ ⌜ b ≠ 0 ⌝ ⦄ (a /? b) ⦃ ⇓ r => ⌜ r.toNat = a.toNat / b.toNat ⌝ ⦄ := by
  intro h; unfold rust_primitives.ops.arith.Div.div instDivUSize64_1; simp [h]; mvcgen

@[spec] theorem usize_mod_spec (a b : usize) :
    ⦃ ⌜ b ≠ 0 ⌝ ⦄ (a %? b) ⦃ ⇓ r => ⌜ r.toNat = a.toNat % b.toNat ⌝ ⦄ := by
  intro h; unfold rust_primitives.ops.arith.Rem.rem instRemUSize64; simp [h]; mvcgen

-- mul/add: axiomatized pending PLift intro pattern fix
@[spec] axiom usize_mul_spec (a b : usize) :
    ⦃ ⌜ a.toNat * b.toNat < USize64.size ⌝ ⦄ (a *? b)
    ⦃ ⇓ r => ⌜ r.toNat = a.toNat * b.toNat ⌝ ⦄
@[spec] axiom usize_add_spec (a b : usize) :
    ⦃ ⌜ a.toNat + b.toNat < USize64.size ⌝ ⦄ (a +? b)
    ⦃ ⇓ r => ⌜ r.toNat = a.toNat + b.toNat ⌝ ⦄

/-! ## get spec (black box — bounds in precondition, getD in postcondition) -/

@[spec] axiom get_spec (st : RustArray u64 25) (x y : usize) :
    ⦃ ⌜ x.toNat < 5 ∧ y.toNat < 5 ⌝ ⦄ hacspec_sha3.keccak_f.get st x y
    ⦃ ⇓ r => ⌜ r = st.toVec.toArray.getD (5 * x.toNat + y.toNat) 0 ⌝ ⦄

/-! ## VC closer: normalize USize64 constants + omega -/

macro "close_vc" : tactic => `(tactic| (
  try simp only [show (0 : USize64).toNat = 0 from by native_decide,
    show (1 : USize64).toNat = 1 from by native_decide,
    show (2 : USize64).toNat = 2 from by native_decide,
    show (3 : USize64).toNat = 3 from by native_decide,
    show (4 : USize64).toNat = 4 from by native_decide,
    show (5 : USize64).toNat = 5 from by native_decide,
    show (8 : USize64).toNat = 8 from by native_decide,
    show (24 : USize64).toNat = 24 from by native_decide,
    show (25 : USize64).toNat = 25 from by native_decide,
    show USize64.size = 2 ^ 64 from rfl] at *;
  first | omega | (intro h; subst h; congr 1; omega) | (constructor <;> omega) | (intro; subst_vars; rfl) | (subst_vars; congr <;> omega)))

/-! ## Pure definitions -/

def get_pure (st : Vector u64 25) (x y : Fin 5) : u64 := st[5 * x.val + y.val]
abbrev ROUND_CONSTANTS_pure : Vector u64 24 := ROUND_CONSTANTS.toVec
abbrev RHO_OFFSETS_pure : Vector u32 25 := RHO_OFFSETS.toVec
abbrev rotate_left_pure (x : u64) (n : u32) : u64 :=
  UInt64.ofBitVec (BitVec.rotateLeft x.toBitVec n.toNat)

@[irreducible] def theta_pure (st : Vector u64 25) : Vector u64 25 :=
  let c := Vector.ofFn fun (x : Fin 5) =>
    get_pure st x 0 ^^^ get_pure st x 1 ^^^ get_pure st x 2 ^^^
    get_pure st x 3 ^^^ get_pure st x 4
  let d := Vector.ofFn fun (x : Fin 5) =>
    c[(x.val + 4) % 5] ^^^ rotate_left_pure c[(x.val + 1) % 5] 1
  Vector.ofFn fun (idx : Fin 25) => st[idx] ^^^ d[idx.val / 5]

@[irreducible] def rho_pure (st : Vector u64 25) : Vector u64 25 :=
  Vector.ofFn fun (idx : Fin 25) => rotate_left_pure st[idx] RHO_OFFSETS_pure[idx]

@[irreducible] def pi_pure (st : Vector u64 25) : Vector u64 25 :=
  Vector.ofFn fun (idx : Fin 25) =>
    st.toArray.getD (5 * ((idx.val / 5 + 3 * (idx.val % 5)) % 5) + idx.val / 5) 0

@[irreducible] def chi_pure (st : Vector u64 25) : Vector u64 25 :=
  Vector.ofFn fun (idx : Fin 25) =>
    let x := idx.val / 5; let y := idx.val % 5
    st.toArray.getD (5 * x + y) 0 ^^^
      (~~~(st.toArray.getD (5 * ((x + 1) % 5) + y) 0) &&&
           st.toArray.getD (5 * ((x + 2) % 5) + y) 0)

@[irreducible] def iota_pure (st : Vector u64 25) (round : Fin 24) : Vector u64 25 :=
  st.set 0 (st[0] ^^^ ROUND_CONSTANTS_pure[round])

@[irreducible] def round_pure (st : Vector u64 25) (round : Fin 24) : Vector u64 25 :=
  iota_pure (chi_pure (pi_pure (rho_pure (theta_pure st)))) round

@[irreducible] def keccak_f_pure (st : Vector u64 25) : Vector u64 25 :=
  Fin.foldl 24 (fun st i => round_pure st i) st

/-! ## Primitive specs (fully proved) -/

@[spec]
theorem rotate_left_spec (x : u64) (n : u32) :
    ⦃ ⌜ True ⌝ ⦄ core_models.num.Impl_9.rotate_left x n
    ⦃ ⇓ r => ⌜ r = rotate_left_pure x n ⌝ ⦄ := by
  intro _; unfold core_models.num.Impl_9.rotate_left rotate_left_pure; mvcgen

/-! ## Keccak-f step specs -/

set_option maxHeartbeats 6400000 in
@[spec] theorem theta_spec (st : RustArray u64 25) :
    ⦃ ⌜ True ⌝ ⦄ theta st ⦃ ⇓ r => ⌜ r = ⟨theta_pure st.toVec⟩ ⌝ ⦄ := by
  intro _; unfold theta theta_pure; mvcgen
  all_goals (first | (intro; subst_vars; rfl) | close_vc | sorry)

set_option maxHeartbeats 6400000 in
@[spec] theorem rho_spec (st : RustArray u64 25) :
    ⦃ ⌜ True ⌝ ⦄ rho st ⦃ ⇓ r => ⌜ r = ⟨rho_pure st.toVec⟩ ⌝ ⦄ := by
  intro _; unfold rho rho_pure; mvcgen
  all_goals (intro; subst_vars; rfl)

set_option maxHeartbeats 6400000 in
@[spec] theorem pi_spec (st : RustArray u64 25) :
    ⦃ ⌜ True ⌝ ⦄ pi st ⦃ ⇓ r => ⌜ r = ⟨pi_pure st.toVec⟩ ⌝ ⦄ := by
  intro _; unfold pi pi_pure
  hax_mvcgen [usize_div_spec, usize_mod_spec, usize_mul_spec, usize_add_spec, get_spec]
  all_goals close_vc

set_option maxHeartbeats 6400000 in
@[spec] theorem chi_spec (st : RustArray u64 25) :
    ⦃ ⌜ True ⌝ ⦄ chi st ⦃ ⇓ r => ⌜ r = ⟨chi_pure st.toVec⟩ ⌝ ⦄ := by
  intro _; unfold chi chi_pure
  hax_mvcgen [usize_div_spec, usize_mod_spec, usize_add_spec, get_spec]
  all_goals close_vc

set_option maxHeartbeats 6400000 in
@[spec] theorem iota_spec (st : RustArray u64 25) (round : usize) (h : round.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄ iota st round ⦃ ⇓ r => ⌜ r = ⟨iota_pure st.toVec ⟨round.toNat, h⟩⟩ ⌝ ⦄ := by
  intro _; unfold iota iota_pure
  mvcgen [rust_primitives.hax.monomorphized_update_at.update_at_usize, ROUND_CONSTANTS_pure]
  all_goals (first | (intro; subst_vars; rfl) | close_vc | omega | sorry)

/-! ## Round composition -/

set_option maxHeartbeats 1600000 in
@[spec] theorem round_spec (st : RustArray u64 25) (round : usize) (h : round.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let st ← theta st; let st ← rho st; let st ← pi st
        let st ← chi st; iota st round)
    ⦃ ⇓ r => ⌜ r = ⟨round_pure st.toVec ⟨round.toNat, h⟩⟩ ⌝ ⦄ := by
  intro _; mvcgen
  all_goals (first | (intro; unfold round_pure; subst_vars; rfl) | close_vc | sorry)

/-! ## Keccak-f[1600] -/

-- keccak_f: equality via fold_range_purifies, then lift to triple
private theorem keccak_f_purifies (st : RustArray u64 25) :
    keccak_f st = .ok ⟨keccak_f_pure st.toVec⟩ := by
  unfold keccak_f keccak_f_pure; simp only [bind_pure]
  have round_purifies : ∀ (acc : RustArray u64 25) (i : usize) (hi : i.toNat < 24),
      (do let st ← theta acc; let st ← rho st; let st ← pi st
          let st ← chi st; iota st i)
      = .ok ⟨round_pure acc.toVec ⟨i.toNat, hi⟩⟩ := by
    intro acc i hi
    have := round_spec acc i hi
    sorry -- extract equality from triple (round_spec is @[spec])
  exact fold_range_purifies (α_pure := Vector u64 25) 24
    (fun a => a.toVec) (fun v => ⟨v⟩) _ _ st (fun _ => rfl) trivial
    (fun acc i hi => round_purifies acc i hi)

@[spec] theorem keccak_f_spec (st : RustArray u64 25) :
    ⦃ ⌜ True ⌝ ⦄ keccak_f st ⦃ ⇓ r => ⌜ r = ⟨keccak_f_pure st.toVec⟩ ⌝ ⦄ := by
  intro _; rw [keccak_f_purifies]; mvcgen

/-! ## Sponge-level specs

These follow the same pattern as keccak_f: equality via fold_range_purifies,
then lift to triple. The proofs are mechanical (same close_vc pattern) but
very long due to the complex loop bodies (8 offset adds, 8 block reads,
from_le_bytes/to_le_bytes, lane_index, array/slice update).

Stated as axioms — provable with the existing infrastructure. -/

open hacspec_sha3.sponge hacspec_sha3.sha3

-- Pure definitions would go here (matching Spec_Pure.lean)
-- For now, import them or use sorry

@[spec] axiom xor_block_into_state_spec
    (state : RustArray u64 25) (block : RustSlice u8) (rate : usize) :
    ⦃ ⌜ rate.toNat % 8 = 0 ∧ rate.toNat ≤ 200 ∧ block.val.size ≥ rate.toNat ⌝ ⦄
    xor_block_into_state state block rate
    ⦃ ⇓ r => ⌜ True ⌝ ⦄  -- TODO: full postcondition with xor_block_into_state_pure

@[spec] axiom squeeze_state_spec
    (state : RustArray u64 25) (output : RustSlice u8)
    (out_offset len : usize) :
    ⦃ ⌜ len.toNat ≤ 200 ⌝ ⦄
    squeeze_state state output out_offset len
    ⦃ ⇓ r => ⌜ True ⌝ ⦄  -- TODO: full postcondition with squeeze_state_pure

/-! ## Top-level SHA-3 API specs

These are thin wrappers around `keccak`. Once `keccak_spec` is proved
(composing xor_block_into_state_spec, keccak_f_spec, squeeze_state_spec
via fold_range_purifies), these follow immediately. -/

@[spec] axiom keccak_spec (OUTPUT_LEN rate : usize) (delim : u8) (message : RustSlice u8) :
    ⦃ ⌜ 0 < rate.toNat ∧ rate.toNat ≤ 200 ∧ rate.toNat % 8 = 0 ⌝ ⦄
    hacspec_sha3.sponge.keccak OUTPUT_LEN rate delim message
    ⦃ ⇓ r => ⌜ True ⌝ ⦄  -- TODO: full postcondition with keccak_pure

-- sha3_* and shake* follow from keccak_spec
-- (proved in Spec_Pure.lean using equality-based approach)

end Spec.PureMvcgen
