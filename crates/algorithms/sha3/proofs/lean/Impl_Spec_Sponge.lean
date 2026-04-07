import Impl_Spec_Compose
set_option linter.unusedSimpArgs false
/-!
# SHA-3 sponge construction proofs

Imports keccak_f proofs from Compose and proves the sponge layer:
load_block, store_block, absorb_block, absorb_final, squeeze, keccak1.

## Proof strategy
- Define pure sponge functions mirroring the implementation.
- Prove impl functions satisfy Hoare triples matching the pure defs.
- Build up from primitives (load_block, store_block) to keccak1.
-/

open Std.Do
open libcrux_sha3.generic_keccak
open hacspec_sha3.keccak_f
open Pure

set_option hax_mvcgen.specset "int"
set_option linter.unusedVariables false

/-! ## Seal all proved functions from Mvcgen + Compose -/

-- Everything from Mvcgen is already irreducible via Compose imports.
-- Seal Compose-level functions:
attribute [local irreducible]
  Impl_2.chi
  keccak_f_pure apply_rounds round_pure chi_pure pi_pure iota_pure rho_theta_pure

/-! ## vc_omega macro -/

local macro "vc_omega" : tactic =>
  `(tactic| (simp only [USize64.reduceToNat, USize64.size, UInt64.size,
      Vector.size, Vector.size_toArray] at *; omega))

/-! ## State initialization -/

-- Impl_2.new creates a zero-initialized KeccakState
@[spec] theorem impl_new_spec :
    ⦃ ⌜ True ⌝ ⦄
    Impl_2.new 1 u64 rust_primitives.hax.Tuple0.mk
    ⦃ ⇓ r => ⌜ ∀ k, k < 25 → r.st.toVec.toArray.getD k 0 = 0 ⌝ ⦄ := by
  intro _
  unfold Impl_2.new
  simp only [libcrux_sha3.traits.KeccakItem.zero, libcrux_sha3.simd.portable.Impl]
  hax_mvcgen

/-! ## TODO: load_block, store_block, absorb_block, keccak1 -/
