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

/-- Transposition permutation: loop index i maps to flat position 5*(i%5) + i/5.
    set_ij(state, i/5, i%5, v) writes to this flat position. -/
def flat_perm (i : Nat) : Nat := 5 * (i % 5) + i / 5

/-- Inverse: flat position k maps to loop index 5*(k%5) + k/5 -/
def flat_perm_inv (k : Nat) : Nat := 5 * (k % 5) + k / 5

-- flat_perm is an involution on [0,25): verify by exhaustion
theorem flat_perm_inv_flat_perm (i : Nat) (hi : i < 25) :
    flat_perm_inv (flat_perm i) = i := by
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
    i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨
    i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24
    by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [flat_perm, flat_perm_inv]

theorem flat_perm_lt (i : Nat) (hi : i < 25) : flat_perm i < 25 := by
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
    i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨
    i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24
    by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [flat_perm]

-- k = flat_perm i ↔ flat_perm_inv k = i (for k,i < 25)
theorem flat_perm_inv_eq_iff (k i : Nat) (hk : k < 25) (hi : i < 25) :
    flat_perm_inv k = i ↔ k = flat_perm i := by
  constructor
  · intro h
    have : flat_perm (flat_perm_inv k) = flat_perm i := by rw [h]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨
      k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨
      k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24
      by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [flat_perm, flat_perm_inv] at this ⊢ <;> omega
  · intro h; rw [h, flat_perm_inv_flat_perm i hi]

/-- Invariant for XOR loop (loop 2 of load_block):
    After i iterations, positions flat_perm(j) for j < i have been XOR'd
    with state_flat[j]. All other positions unchanged. -/
def xor_loop_inv (old_state state_flat cur_state : Array u64) (i : Nat) : Prop :=
  ∀ k, k < 25 →
    cur_state.getD k 0 =
      if flat_perm_inv k < i
      then old_state.getD k 0 ^^^ state_flat.getD (flat_perm_inv k) 0
      else old_state.getD k 0

theorem xor_loop_inv_init (state state_flat : Array u64) :
    xor_loop_inv state state_flat state 0 := by
  intro k hk; simp [xor_loop_inv, Nat.not_lt_zero]

theorem xor_loop_inv_step (old_state state_flat cur_state new_state : Array u64)
    (i : Nat) (hi : i < 25)
    (hinv : xor_loop_inv old_state state_flat cur_state i)
    (hset : ∀ k, k < 25 → new_state.getD k 0 =
      if k = flat_perm i then
        cur_state.getD (flat_perm i) 0 ^^^ state_flat.getD i 0
      else cur_state.getD k 0) :
    xor_loop_inv old_state state_flat new_state (i + 1) := by
  intro k hk
  simp only [xor_loop_inv] at hinv
  specialize hset k hk
  have hinv_k := hinv k hk
  rw [hset]
  by_cases hki : k = flat_perm i
  · -- k = flat_perm i: just written
    rw [if_pos hki, hki, flat_perm_inv_flat_perm i hi]
    simp only [Nat.lt_succ_iff, Nat.le_refl, ite_true]
    congr 1
    -- cur_state at flat_perm(i) was unchanged (flat_perm_inv(flat_perm(i)) = i, not < i)
    rw [hki] at hinv_k
    rw [flat_perm_inv_flat_perm i hi] at hinv_k
    rw [hinv_k, if_neg (by omega)]
  · -- k ≠ flat_perm i: unchanged from cur_state
    rw [if_neg hki]
    have hne : flat_perm_inv k ≠ i :=
      fun h => hki ((flat_perm_inv_eq_iff k i hk hi).mp h)
    simp only [show (flat_perm_inv k < i + 1) ↔ (flat_perm_inv k < i) from by omega]
    exact hinv_k

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

set_option maxHeartbeats 800000 in
@[spec] theorem absorb_block_spec (RATE : usize) (st : KeccakState 1 u64)
    (input : RustArray (RustSlice u8) 1) (start : usize)
    (hrate : RATE.toNat % 8 = 0) :
    ⦃ ⌜ True ⌝ ⦄
    Impl_2.absorb_block 1 u64 RATE st input start
    ⦃ ⇓ r => ⌜ r.st.toVec = Sponge.absorb_block_pure RATE.toNat st.st.toVec
        (input.toVec[(0 : Fin 1)]).val.toList start.toNat ⌝ ⦄ := by
  intro _
  unfold Impl_2.absorb_block
  -- Resolve Absorb trait dispatch to portable load_block
  simp only [libcrux_sha3.traits.Absorb.load_block,
    libcrux_sha3.simd.portable.Impl_1,
    libcrux_sha3.traits.Absorb.AssociatedTypes,
    libcrux_sha3.simd.portable.Impl_1.AssociatedTypes]
  hax_mvcgen
  all_goals sorry

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
