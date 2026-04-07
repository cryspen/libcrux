import Impl_Spec_Compose
set_option linter.unusedSimpArgs false
/-!
# SHA-3 sponge construction proofs

Top-down: define spec lemmas with sorry proofs, verify they compose,
then fill in lower-level proofs.
-/

open Std.Do
open libcrux_sha3.generic_keccak
open hacspec_sha3.keccak_f
open Pure

set_option hax_mvcgen.specset "int"
set_option linter.unusedVariables false

/-! ## Seal all proved functions -/

attribute [local irreducible]
  Impl_2.chi Impl_2.theta Impl_2.rho Impl_2.pi
  libcrux_sha3.generic_keccak.Impl_2.iota
  keccak_f_pure apply_rounds round_pure chi_pure pi_pure iota_pure rho_theta_pure
  libcrux_sha3.traits.get_ij libcrux_sha3.traits.set_ij
  libcrux_sha3.generic_keccak.Impl_2.set
  getElemResult instGetElemResultOfIndex

local macro "vc_omega" : tactic =>
  `(tactic| (simp only [USize64.reduceToNat, USize64.size, UInt64.size,
      Vector.size, Vector.size_toArray] at *; omega))

/-! ## Pure sponge functions (abstract — details to be filled in) -/

namespace Sponge

/-- XOR RATE/8 lanes from input bytes into state -/
def load_block_pure (RATE : Nat) (state : Vector u64 25)
    (input : List u8) (start : Nat) : Vector u64 25 := sorry

/-- Extract bytes from state lanes -/
def store_block_pure (RATE : Nat) (state : Vector u64 25)
    (start : Nat) (len : Nat) : List u8 := sorry

/-- Pad last block + XOR into state -/
def load_last_pure (RATE : Nat) (DELIM : u8) (state : Vector u64 25)
    (input : List u8) (start : Nat) (len : Nat) : Vector u64 25 := sorry

/-- absorb_block = load_block + keccak_f -/
def absorb_block_pure (RATE : Nat) (state : Vector u64 25)
    (input : List u8) (start : Nat) : Vector u64 25 :=
  keccak_f_pure (load_block_pure RATE state input start)

/-- absorb_final = load_last + keccak_f -/
def absorb_final_pure (RATE : Nat) (DELIM : u8) (state : Vector u64 25)
    (input : List u8) (start : Nat) (len : Nat) : Vector u64 25 :=
  keccak_f_pure (load_last_pure RATE DELIM state input start len)

end Sponge

/-! ## State initialization -/

@[spec] theorem impl_new_spec :
    ⦃ ⌜ True ⌝ ⦄
    Impl_2.new 1 u64 rust_primitives.hax.Tuple0.mk
    ⦃ ⇓ r => ⌜ ∀ k, k < 25 → r.st.toVec.toArray.getD k 0 = 0 ⌝ ⦄ := by
  intro _
  unfold Impl_2.new
  simp only [libcrux_sha3.traits.KeccakItem.zero, libcrux_sha3.simd.portable.Impl]
  hax_mvcgen

attribute [local irreducible] Impl_2.new

/-! ## Spec lemmas: sorry proofs, full postconditions -/

attribute [local irreducible] Impl_2.keccakf1600

-- load_block
attribute [local irreducible] libcrux_sha3.simd.portable.load_block

@[spec] theorem load_block_spec (RATE : usize) (state : RustArray u64 25)
    (blocks : RustSlice u8) (start : usize)
    (hrate : RATE.toNat % 8 = 0)
    (hbounds : start.toNat + RATE.toNat ≤ blocks.val.size) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_sha3.simd.portable.load_block RATE state blocks start
    ⦃ ⇓ r => ⌜ r.toVec = Sponge.load_block_pure RATE.toNat state.toVec
        blocks.val.toList start.toNat ⌝ ⦄ := by
  sorry

-- store_block
attribute [local irreducible] libcrux_sha3.simd.portable.store_block

@[spec] theorem store_block_spec (RATE : usize) (s : RustArray u64 25)
    (out : RustSlice u8) (start : usize) (len : usize)
    (hlen : len.toNat ≤ RATE.toNat) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_sha3.simd.portable.store_block RATE s out start len
    ⦃ ⇓ r => ⌜ True ⌝ ⦄ := by  -- TODO: strengthen
  sorry

-- load_last
attribute [local irreducible] libcrux_sha3.simd.portable.load_last

@[spec] theorem load_last_spec (RATE : usize) (DELIM : u8)
    (state : RustArray u64 25) (blocks : RustSlice u8)
    (start : usize) (len : usize)
    (hrate : RATE.toNat % 8 = 0) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_sha3.simd.portable.load_last RATE DELIM state blocks start len
    ⦃ ⇓ r => ⌜ r.toVec = Sponge.load_last_pure RATE.toNat DELIM state.toVec
        blocks.val.toList start.toNat len.toNat ⌝ ⦄ := by
  sorry

-- absorb_block = Absorb.load_block + keccakf1600
attribute [local irreducible] Impl_2.absorb_block

@[spec] theorem absorb_block_spec (RATE : usize) (st : KeccakState 1 u64)
    (input : RustArray (RustSlice u8) 1) (start : usize)
    (hrate : RATE.toNat % 8 = 0) :
    ⦃ ⌜ True ⌝ ⦄
    Impl_2.absorb_block 1 u64 RATE st input start
    ⦃ ⇓ r => ⌜ r.st.toVec = Sponge.absorb_block_pure RATE.toNat st.st.toVec
        (input.toVec[(0 : Fin 1)]).val.toList start.toNat ⌝ ⦄ := by
  sorry

-- absorb_final = Absorb.load_last + keccakf1600
attribute [local irreducible] Impl_2.absorb_final

@[spec] theorem absorb_final_spec (RATE : usize) (DELIM : u8)
    (st : KeccakState 1 u64) (input : RustArray (RustSlice u8) 1)
    (start : usize) (len : usize)
    (hrate : RATE.toNat % 8 = 0) :
    ⦃ ⌜ True ⌝ ⦄
    Impl_2.absorb_final 1 u64 RATE DELIM st input start len
    ⦃ ⇓ r => ⌜ r.st.toVec = Sponge.absorb_final_pure RATE.toNat DELIM st.st.toVec
        (input.toVec[(0 : Fin 1)]).val.toList start.toNat len.toNat ⌝ ⦄ := by
  sorry

/-! ## Squeeze -/

-- Squeeze.squeeze (portable) = store_block on st.st
-- The trait instance dispatches to store_block directly.
-- We need a spec for the trait method call as it appears in keccak1.

attribute [local irreducible]
  libcrux_sha3.traits.Squeeze.squeeze

@[spec] theorem squeeze_spec (RATE : usize)
    (st : KeccakState 1 u64) (out : RustSlice u8)
    (start : usize) (len : usize)
    (hlen : len.toNat ≤ RATE.toNat) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_sha3.traits.Squeeze.squeeze
      (KeccakState 1 u64) u64 RATE st out start len
    ⦃ ⇓ r => ⌜ True ⌝ ⦄ := by  -- TODO: postcondition about output bytes
  sorry

-- Also need: core_models.slice.Impl.len
@[spec] theorem slice_len_spec (out : RustSlice u8) :
    ⦃ ⌜ True ⌝ ⦄
    core_models.slice.Impl.len u8 out
    ⦃ ⇓ r => ⌜ r.toNat = out.val.size ⌝ ⦄ := by
  sorry

-- proof_utils.lemmas.lemma_mul_succ_le (ghost lemma used in keccak1)
@[spec] theorem lemma_mul_succ_le_spec (i n RATE : usize) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_sha3.proof_utils.lemmas.lemma_mul_succ_le i n RATE
    ⦃ ⇓ r => ⌜ True ⌝ ⦄ := by
  sorry

/-! ## keccak1: try mvcgen with True postcondition to test composition -/

attribute [local irreducible] libcrux_sha3.generic_keccak.portable.keccak1

set_option maxHeartbeats 6400000 in
theorem keccak1_spec (RATE : usize) (DELIM : u8)
    (input output : RustSlice u8)
    (hrate : RATE.toNat % 8 = 0)
    (hrate_pos : 0 < RATE.toNat) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_sha3.generic_keccak.portable.keccak1 RATE DELIM input output
    ⦃ ⇓ r => ⌜ True ⌝ ⦄ := by
  intro _
  unfold libcrux_sha3.generic_keccak.portable.keccak1
  hax_mvcgen
  all_goals sorry
