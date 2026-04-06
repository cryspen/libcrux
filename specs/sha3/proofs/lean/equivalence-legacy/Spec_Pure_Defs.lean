import Hax
import Stubs
import extraction.hacspec_sha3

/-!
# Pure definitions for SHA-3 functions

Pure (non-monadic) counterparts for every function in the SHA-3 spec extraction.
No proofs — just definitions. Imported by both the equality-based and mvcgen-based
proof files.
-/

open hacspec_sha3.keccak_f

namespace Spec.Pure

/-! ## Keccak-f layer -/

def get_pure (st : Vector u64 25) (x y : Fin 5) : u64 := st[5 * x.val + y.val]

abbrev ROUND_CONSTANTS_pure : Vector u64 24 := ROUND_CONSTANTS.toVec
abbrev RHO_OFFSETS_pure : Vector u32 25 := RHO_OFFSETS.toVec

@[irreducible] def rotate_left_pure (x : u64) (n : u32) : u64 :=
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

/-! ## Sponge layer -/

open hacspec_sha3.sponge hacspec_sha3.sha3

@[irreducible] def lane_index_pure (l : Fin 25) : Fin 25 :=
  ⟨5 * (l.val % 5) + l.val / 5, by omega⟩

-- TODO: xor_block_into_state_pure, squeeze_state_pure, keccak_pure
-- These are complex (loop bodies with byte conversion) but purely definitional.

end Spec.Pure
