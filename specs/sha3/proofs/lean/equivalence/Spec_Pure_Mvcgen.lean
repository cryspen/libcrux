import Hax
import Stubs
import extraction.hacspec_sha3
import Std.Do.Triple
import Std.Tactic.Do

/-!
# Pure specification functions for SHA-3 — mvcgen-based proofs

Purification lemmas stated as Hoare triples, proved using `mvcgen`.
The `@[spec] createi.spec_triple` axiom in Stubs.lean lets `mvcgen`
handle `createi` calls, leaving per-element VCs that close by `subst_vars`.

Key design choices:
- Pure defs are `@[irreducible]` to prevent term explosion during composition
- Each spec is `@[spec]` so `mvcgen` uses it as a black box at higher layers
-/

open Std.Do hacspec_sha3.keccak_f

namespace Spec.PureMvcgen

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
    get_pure st ⟨(idx.val / 5 + 3 * (idx.val % 5)) % 5, by omega⟩ ⟨idx.val / 5, by omega⟩

@[irreducible] def chi_pure (st : Vector u64 25) : Vector u64 25 :=
  Vector.ofFn fun (idx : Fin 25) =>
    let x := idx.val / 5; let y := idx.val % 5
    get_pure st ⟨x, by omega⟩ ⟨y, by omega⟩ ^^^
      (~~~(get_pure st ⟨(x + 1) % 5, by omega⟩ ⟨y, by omega⟩) &&&
           get_pure st ⟨(x + 2) % 5, by omega⟩ ⟨y, by omega⟩)

@[irreducible] def iota_pure (st : Vector u64 25) (round : Fin 24) : Vector u64 25 :=
  st.set 0 (st[0] ^^^ ROUND_CONSTANTS_pure[round])

@[irreducible] def round_pure (st : Vector u64 25) (round : Fin 24) : Vector u64 25 :=
  iota_pure (chi_pure (pi_pure (rho_pure (theta_pure st)))) round

@[irreducible] def keccak_f_pure (st : Vector u64 25) : Vector u64 25 :=
  Fin.foldl 24 (fun st i => round_pure st i) st

/-! ## Layer 0: Primitive specs (fully proved) -/

@[spec]
theorem rotate_left_spec (x : u64) (n : u32) :
    ⦃ ⌜ True ⌝ ⦄
    core_models.num.Impl_9.rotate_left x n
    ⦃ ⇓ r => ⌜ r = rotate_left_pure x n ⌝ ⦄ := by
  intro _; unfold core_models.num.Impl_9.rotate_left rotate_left_pure; mvcgen

@[spec]
theorem to_le_bytes_spec (x : u64) :
    ⦃ ⌜ True ⌝ ⦄
    core_models.num.Impl_9.to_le_bytes x
    ⦃ ⇓ r => ⌜ r = ⟨#v[(x % 256).toUInt8, (x >>> 8 % 256).toUInt8,
        (x >>> 16 % 256).toUInt8, (x >>> 24 % 256).toUInt8,
        (x >>> 32 % 256).toUInt8, (x >>> 40 % 256).toUInt8,
        (x >>> 48 % 256).toUInt8, (x >>> 56 % 256).toUInt8]⟩ ⌝ ⦄ := by
  intro _; unfold core_models.num.Impl_9.to_le_bytes; mvcgen

@[spec]
theorem from_le_bytes_spec (b : RustArray u8 8) :
    ⦃ ⌜ True ⌝ ⦄
    core_models.num.Impl_9.from_le_bytes b
    ⦃ ⇓ r => ⌜ r = b.toVec[0].toUInt64 + (b.toVec[1].toUInt64 <<< 8)
        + (b.toVec[2].toUInt64 <<< 16) + (b.toVec[3].toUInt64 <<< 24)
        + (b.toVec[4].toUInt64 <<< 32) + (b.toVec[5].toUInt64 <<< 40)
        + (b.toVec[6].toUInt64 <<< 48) + (b.toVec[7].toUInt64 <<< 56) ⌝ ⦄ := by
  intro _; unfold core_models.num.Impl_9.from_le_bytes; mvcgen

/-! ## Layer 1: Keccak-f step specs

`mvcgen` decomposes each step function, uses `createi.spec_triple` for the
array construction, and leaves per-element VCs that close by `subst_vars`. -/

set_option maxHeartbeats 6400000 in
@[spec]
theorem theta_spec (st : RustArray u64 25) :
    ⦃ ⌜ True ⌝ ⦄ theta st ⦃ ⇓ r => ⌜ r = ⟨theta_pure st.toVec⟩ ⌝ ⦄ := by
  intro _; unfold theta theta_pure; mvcgen
  all_goals (first | intro; subst_vars; rfl | sorry)

set_option maxHeartbeats 6400000 in
@[spec]
theorem rho_spec (st : RustArray u64 25) :
    ⦃ ⌜ True ⌝ ⦄ rho st ⦃ ⇓ r => ⌜ r = ⟨rho_pure st.toVec⟩ ⌝ ⦄ := by
  intro _; unfold rho rho_pure; mvcgen
  all_goals (first | intro; subst_vars; rfl | sorry)

set_option maxHeartbeats 6400000 in
@[spec]
theorem pi_spec (st : RustArray u64 25) :
    ⦃ ⌜ True ⌝ ⦄ pi st ⦃ ⇓ r => ⌜ r = ⟨pi_pure st.toVec⟩ ⌝ ⦄ := by
  intro _; unfold pi pi_pure; mvcgen
  all_goals (first | intro; subst_vars; rfl | sorry)

set_option maxHeartbeats 6400000 in
@[spec]
theorem chi_spec (st : RustArray u64 25) :
    ⦃ ⌜ True ⌝ ⦄ chi st ⦃ ⇓ r => ⌜ r = ⟨chi_pure st.toVec⟩ ⌝ ⦄ := by
  intro _; unfold chi chi_pure; mvcgen
  all_goals (first | intro; subst_vars; rfl | sorry)

set_option maxHeartbeats 6400000 in
@[spec]
theorem iota_spec (st : RustArray u64 25) (round : usize) (h : round.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄ iota st round ⦃ ⇓ r => ⌜ r = ⟨iota_pure st.toVec ⟨round.toNat, h⟩⟩ ⌝ ⦄ := by
  intro _; unfold iota iota_pure
  mvcgen [rust_primitives.hax.monomorphized_update_at.update_at_usize, ROUND_CONSTANTS_pure]
  all_goals (first | intro; subst_vars; rfl | omega | sorry)

/-! ## Layer 2: Round composition (uses step specs as black boxes) -/

set_option maxHeartbeats 1600000 in
@[spec]
theorem round_spec (st : RustArray u64 25) (round : usize) (h : round.toNat < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let st ← theta st; let st ← rho st; let st ← pi st
        let st ← chi st; iota st round)
    ⦃ ⇓ r => ⌜ r = ⟨round_pure st.toVec ⟨round.toNat, h⟩⟩ ⌝ ⦄ := by
  intro _; mvcgen
  all_goals (first | (intro; unfold round_pure; subst_vars; rfl) | sorry)

/-! ## Layer 3: Keccak-f[1600] -/

set_option maxHeartbeats 6400000 in
@[spec]
theorem keccak_f_spec (st : RustArray u64 25) :
    ⦃ ⌜ True ⌝ ⦄ keccak_f st ⦃ ⇓ r => ⌜ r = ⟨keccak_f_pure st.toVec⟩ ⌝ ⦄ := by
  intro _; unfold keccak_f keccak_f_pure; mvcgen
  all_goals sorry

end Spec.PureMvcgen
