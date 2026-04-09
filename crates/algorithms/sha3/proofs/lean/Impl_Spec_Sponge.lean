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

/-! ## Pure sponge functions -/

namespace Sponge

/-- Transposition permutation: loop index i maps to flat position 5*(i%5) + i/5.
    set_ij(state, i/5, i%5, v) writes to this flat position. -/
def flat_perm (i : Nat) : Nat := 5 * (i % 5) + i / 5

/-- Inverse: flat position k maps to loop index 5*(k%5) + k/5 -/
def flat_perm_inv (k : Nat) : Nat := 5 * (k % 5) + k / 5

/-- Convert 8 little-endian bytes from a list at offset `off` to a u64. -/
def bytes_to_u64_le (bytes : List u8) (off : Nat) : u64 :=
  let get (i : Nat) : u64 := (bytes.getD (off + i) 0).toUInt64
  get 0
  + (get 1 <<< 8)
  + (get 2 <<< 16)
  + (get 3 <<< 24)
  + (get 4 <<< 32)
  + (get 5 <<< 40)
  + (get 6 <<< 48)
  + (get 7 <<< 56)

/-- XOR RATE/8 lanes from input bytes into state.
    Lane i of input (8 bytes at start + 8*i, LE) is XOR'd into
    state position flat_perm(i) = 5*(i%5) + i/5. -/
def load_block_pure (RATE : Nat) (state : Vector u64 25)
    (input : List u8) (start : Nat) : Vector u64 25 :=
  Vector.ofFn fun ⟨k, hk⟩ =>
    if flat_perm_inv k < RATE / 8
    then state[k] ^^^ bytes_to_u64_le input (start + 8 * flat_perm_inv k)
    else state[k]

/-- Extract the k-th LE byte (k < 8) from a u64 lane. -/
def lane_byte (lane : u64) (k : Nat) : u8 := (lane >>> (UInt64.ofNat (8 * k))).toUInt8

/-- Extract `len` bytes from state lanes (LE, lane-interleaved via flat_perm).
    Byte b comes from the (b%8)-th LE byte of lane at flat_perm(b/8). -/
def store_block_pure (RATE : Nat) (state : Vector u64 25)
    (start : Nat) (len : Nat) : List u8 :=
  (List.range len).map fun b =>
    lane_byte (state.toArray.getD (flat_perm (b / 8)) 0) (b % 8)

/-- Pad last block + XOR into state -/
def load_last_pure (RATE : Nat) (DELIM : u8) (state : Vector u64 25)
    (input : List u8) (start : Nat) (len : Nat) : Vector u64 25 :=
  let buffer := (List.range RATE).map fun b =>
    let x := if b < len then input.getD (start + b) 0 else 0
    let x := if b = len then x ||| DELIM else x
    let x := if b = RATE - 1 then x ||| (128 : u8) else x
    x
  load_block_pure RATE state buffer 0

/-- absorb_block = load_block + keccak_f -/
def absorb_block_pure (RATE : Nat) (state : Vector u64 25)
    (input : List u8) (start : Nat) : Vector u64 25 :=
  keccak_f_pure (load_block_pure RATE state input start)

/-- absorb_final = load_last + keccak_f -/
def absorb_final_pure (RATE : Nat) (DELIM : u8) (state : Vector u64 25)
    (input : List u8) (start : Nat) (len : Nat) : Vector u64 25 :=
  keccak_f_pure (load_last_pure RATE DELIM state input start len)

/-- Invariant for store_block main loop:
    After i iterations, the first 8*i bytes starting at `start` have been written
    with LE encodings of the corresponding state lanes. Size is preserved. -/
def store_loop_inv (state : Vector u64 25) (out_size start : Nat)
    (cur_out : Array u8) (i : Nat) : Prop :=
  cur_out.size = out_size ∧
  ∀ b, b < 8 * i →
    cur_out.toList.getD (start + b) 0 =
      lane_byte (state.toArray.getD (flat_perm (b / 8)) 0) (b % 8)

-- store_loop_inv_step removed — proved inline in vc18 using splice_seq_getD

attribute [irreducible] bytes_to_u64_le load_block_pure

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

/-- Invariant for byte conversion loop (loop 1 of load_block):
    After i iterations, state_flat[j] for j < i holds the LE-decoded lane,
    and state_flat[j] for j ≥ i is still 0. -/
def byte_loop_inv (input : List u8) (start : Nat) (state_flat : Array u64) (i : Nat) : Prop :=
  state_flat.size = 25 ∧
  ∀ j, j < 25 →
    state_flat.getD j 0 = if j < i then bytes_to_u64_le input (start + 8 * j) else 0

theorem byte_loop_inv_init (input : List u8) (start : Nat) :
    byte_loop_inv input start (Vector.replicate 25 (0 : u64)).toArray 0 := by
  constructor
  · simp [Vector.size_toArray]
  · intro j hj; simp [byte_loop_inv, Array.getD, Nat.not_lt_zero]

theorem byte_loop_inv_step (input : List u8) (start : Nat)
    (cur_state : Array u64) (i : Nat) (hi : i < 25)
    (hinv : byte_loop_inv input start cur_state i)
    (val : u64)
    (hval : val = bytes_to_u64_le input (start + 8 * i))
    (new_state : Array u64)
    (hset_size : new_state.size = 25)
    (hset : ∀ j, j < 25 → new_state.getD j 0 =
      if j = i then val else cur_state.getD j 0) :
    byte_loop_inv input start new_state (i + 1) := by
  have ⟨hsize, hspec⟩ := hinv
  exact ⟨hset_size, fun j hj => by
    rw [hset j hj]
    split
    · rename_i hji; subst hji; rw [if_pos (by omega), hval]
    · rename_i hji
      rw [hspec j hj]
      simp only [show (j < i + 1) ↔ (j < i) from by omega]⟩

/-- Composition: byte_loop_inv + xor_loop_inv → load_block_pure -/
theorem byte_xor_compose (RATE : Nat) (state : Vector u64 25)
    (input : List u8) (start : Nat) (state_flat result : Array u64)
    (n : Nat) (hn : n = RATE / 8)
    (hbyte : byte_loop_inv input start state_flat n)
    (hxor : xor_loop_inv state.toArray state_flat result n)
    (hsize : result.size = 25) :
    (⟨result, by rw [hsize]⟩ : Vector u64 25) = load_block_pure RATE state input start := by
  have ⟨hsf_size, hsf_spec⟩ := hbyte
  have toVec_getD {m : Nat} (v : Vector u64 m) (j : Nat) (hj : j < m) :
      v.toArray.getD j 0 = v[j] := by
    unfold Array.getD
    rw [dif_pos (show j < v.toArray.size by rw [Vector.size_toArray]; exact hj)]
    exact Vector.getElem_toArray _
  subst hn
  ext k hk
  simp only [Vector.getElem_mk, load_block_pure, Vector.getElem_ofFn]
  rw [show result[k] = result.getD k 0 from by
    simp [Array.getD, show k < result.size from by omega]]
  rw [hxor k (by omega), toVec_getD state k hk]
  split <;> rename_i hlt
  · congr 1
    have h := hsf_spec (flat_perm_inv k) (show flat_perm_inv k < 25 from flat_perm_lt k hk)
    rw [h, if_pos hlt]
  · rfl

end Sponge

/-! ## Byte conversion loop standalone spec (loop 1 of load_block) -/

set_option maxHeartbeats 6400000 in
theorem byte_loop_spec (n : usize) (blocks : RustSlice u8) (start : usize)
    (state_flat : RustArray u64 25)
    (hn : n.toNat ≤ 25)
    (hbounds : ∀ i, i < n.toNat → start.toNat + 8 * i + 8 ≤ blocks.val.size) :
    ⦃ ⌜ Sponge.byte_loop_inv blocks.val.toList start.toNat state_flat.toVec.toArray 0 ⌝ ⦄
    rust_primitives.hax.folds.fold_range (0 : usize) n
      (fun state_flat _ => (do (pure true) : RustM Bool))
      state_flat
      (fun state_flat i => do
        let offset ← (start +? (← ((8 : usize) *? i)))
        let slice ← blocks[core_models.ops.range.Range.mk offset (← (offset +? (8 : usize)))]_?
        let arr ← core_models.convert.TryInto.try_into (RustSlice u8) (RustArray u8 8) slice
        let bytes ← core_models.result.Impl.unwrap (RustArray u8 8)
          core_models.array.TryFromSliceError arr
        let val ← core_models.num.Impl_9.from_le_bytes bytes
        rust_primitives.hax.monomorphized_update_at.update_at_usize state_flat i val)
      ⟨fun _ _ => True, sorry⟩
    ⦃ ⇓ r => ⌜ Sponge.byte_loop_inv blocks.val.toList start.toNat
        r.toVec.toArray n.toNat ⌝ ⦄ := by
  intro _
  rw [show rust_primitives.hax.folds.fold_range (0 : USize64) n
    (fun state_flat x => do let a ← pure true; pure (a = true)) state_flat _ _ =
    rust_primitives.hax.folds.fold_range (0 : USize64) n
    (fun (sf : RustArray u64 25) (k : USize64) =>
      pure (Sponge.byte_loop_inv blocks.val.toList start.toNat sf.toVec.toArray k.toNat))
    state_flat _
    ⟨fun sf k => Sponge.byte_loop_inv blocks.val.toList start.toNat sf.toVec.toArray k.toNat,
      fun _ _ => by intro _; rfl⟩
    from fold_range_inv_irrelevant _ _ _ _ _ _ _ _]
  hax_mvcgen
  all_goals (try vc_omega)
  all_goals (try (have := blocks.size_lt_usizeSize; have := hbounds; vc_omega))
  all_goals (try grind)
  -- vc4/vc5: overflow
  all_goals (try (rename_i _ _ i _ _ _ _; exact absurd (hbounds i.toNat (by vc_omega)) (by have := blocks.size_lt_usizeSize; vc_omega)))
  all_goals (try (rename_i _ _ i _ _ _ _ _ _ _; have := hbounds i.toNat (by vc_omega); have := blocks.size_lt_usizeSize; vc_omega))
  -- vc4: overflow (missed by earlier tactics)
  · rename_i _ _ i _ hi_lt _ _ _
    have := hbounds i.toNat (by vc_omega)
    have := blocks.size_lt_usizeSize; vc_omega
  -- vc11: step — byte_loop_inv maintained after Vector.set with from_le_bytes result
  · rename_i _ acc i _ hi_lt inv _ _ _ _ _ _ _ _ _ _ bytes hbytes _
    simp only [USize64.reduceToNat] at *
    rw [USize64.toNat_add_of_lt (by simp [USize64.size, UInt64.size]; omega)]
    have hbd := hbounds i.toNat (by vc_omega)
    have ⟨hsize_inv, hspec_inv⟩ := inv
    unfold Sponge.byte_loop_inv
    refine ⟨by simp [Vector.size_toArray], ?_⟩
    intro j hj
    subst hbytes
    simp only [Vector.toArray_set, USize64.reduceToNat] at *
    have ⟨_, hspec⟩ := inv
    simp_all [Array.getElem_set, Array.getD]
    -- Goal: (if i=j then from_le_bytes_expanded else old_inv) = (if j<i+1 then bytes_to_u64_le else 0)
    split
    · -- i = j: bridge from_le_bytes ↔ bytes_to_u64_le
      rename_i hji; subst hji; simp only [show i.toNat < i.toNat + 1 from by omega, ite_true]
      have hbd := hbounds i.toNat (by vc_omega)
      unfold Sponge.bytes_to_u64_le; unfold List.getD
      simp [show ∀ k, k ≤ 7 → USize64.toNat start + 8 * i.toNat + k < blocks.val.size from by omega,
        show USize64.toNat start + 8 * i.toNat < blocks.val.size from by omega]
    · -- i ≠ j: old invariant, j < i+1 ↔ j < i
      rename_i hji
      simp only [show (j < i.toNat + 1) ↔ (j < i.toNat) from by omega]

/-! ## XOR loop standalone spec (loop 2 of load_block) -/

-- Local wrappers for get_ij/set_ij (mvcgen can't match type-level args)
private def lb_get (arr : RustArray u64 25) (i j : usize) :=
  libcrux_sha3.traits.get_ij 1 u64 arr i j
private def lb_set (arr : RustArray u64 25) (i j : usize) (v : u64) :=
  libcrux_sha3.traits.set_ij 1 u64 arr i j v

private theorem lb_get_eq (arr i j) :
    lb_get arr i j = libcrux_sha3.traits.get_ij 1 u64 arr i j := rfl
private theorem lb_set_eq (arr i j v) :
    lb_set arr i j v = libcrux_sha3.traits.set_ij 1 u64 arr i j v := rfl

@[spec] private theorem lb_get_spec (arr : RustArray u64 25) (i j : usize)
    (hi : i.toNat < 5) (hj : j.toNat < 5) :
    ⦃ ⌜ True ⌝ ⦄ lb_get arr i j
    ⦃ ⇓ r => ⌜ r = arr.toVec.toArray.getD (5 * j.toNat + i.toNat) 0 ⌝ ⦄ := by
  intro _; rw [lb_get_eq]; exact get_ij_spec arr i j hi hj trivial

@[spec] private theorem lb_set_spec (arr : RustArray u64 25) (i j : usize) (v : u64)
    (hi : i.toNat < 5) (hj : j.toNat < 5) :
    ⦃ ⌜ True ⌝ ⦄ lb_set arr i j v
    ⦃ ⇓ r => ⌜ r.toVec.size = 25 ∧
      (∀ k (hk : k < 25), r.toVec[k] =
        if k = 5 * j.toNat + i.toNat then v else arr.toVec[k]) ⌝ ⦄ := by
  intro _; rw [lb_set_eq]; exact set_ij_spec arr i j v hi hj trivial

attribute [irreducible] lb_get lb_set

-- The XOR loop: for i in 0..n, state[i/5, i%5] ^= state_flat[i]
-- Uses the chi pattern: swap trivial invariant → real invariant, then hax_mvcgen.
set_option maxHeartbeats 3200000 in
theorem xor_loop_spec (n : usize) (state state_flat : RustArray u64 25)
    (hn : n.toNat ≤ 25) :
    ⦃ ⌜ True ⌝ ⦄
    rust_primitives.hax.folds.fold_range (0 : usize) n
      (fun state _ => (do (pure true) : RustM Bool))
      state
      (fun state i => do
        libcrux_sha3.traits.set_ij 1 u64 state (← (i /? 5)) (← (i %? 5))
          (← ((← (libcrux_sha3.traits.get_ij 1 u64 state (← (i /? 5)) (← (i %? 5))))
            ^^^? (← state_flat[i]_?))))
      ⟨fun _ _ => True, sorry⟩
    ⦃ ⇓ r => ⌜ Sponge.xor_loop_inv state.toVec.toArray state_flat.toVec.toArray
        r.toVec.toArray n.toNat ⌝ ⦄ := by
  intro _
  -- Rewrite get_ij/set_ij to local wrappers
  simp only [← lb_get_eq, ← lb_set_eq]
  -- Swap trivial invariant → xor_loop_inv
  rw [show rust_primitives.hax.folds.fold_range (0 : USize64) n
    (fun state _ => (do (pure true) : RustM Bool)) state _ ⟨fun _ _ => True, sorry⟩ =
    rust_primitives.hax.folds.fold_range (0 : USize64) n
    (fun (acc : RustArray u64 25) (k : USize64) =>
      pure (Sponge.xor_loop_inv state.toVec.toArray state_flat.toVec.toArray acc.toVec.toArray k.toNat))
    state _
    ⟨fun acc k => Sponge.xor_loop_inv state.toVec.toArray state_flat.toVec.toArray acc.toVec.toArray k.toNat,
      fun _ _ => by intro _; rfl⟩
    from fold_range_inv_irrelevant _ _ _ _ _ _ _ _]
  hax_mvcgen
  all_goals (try vc_omega)
  -- vc2: initial invariant
  · exact Sponge.xor_loop_inv_init _ _
  -- vc11: r✝⁴ < 5 where r✝⁴ = i % 5
  · grind
  -- vc12: step — set postcondition → xor_loop_inv (i+1)
  -- Structure: apply xor_loop_inv_step, convert Vector.getElem ↔ Array.getD,
  -- wire set_ij postcondition (flat_perm matching). Needs careful name management.
  · rename_i _ acc i _ hi_lt inv rdiv hdiv rmod hmod rdiv2 hdiv2 rmod2 hmod2 rget hget rsf hsf rnew
    intro hsize hset_post
    have hi : i.toNat < 25 := by omega
    rw [show (i + 1).toNat = i.toNat + 1 from
      USize64.toNat_add_of_lt (by simp [USize64.size, UInt64.size]; omega)]
    apply Sponge.xor_loop_inv_step _ _ _ _ _ hi inv
    intro k hk
    simp only [USize64.reduceToNat, USize64.size, UInt64.size] at hdiv hmod hdiv2 hmod2
    simp only [Sponge.flat_perm]
    -- Convert hpost: substitute all intermediate USize64 values
    have hpost := hset_post k hk
    rw [hget, hsf, hmod, hdiv, hmod2, hdiv2] at hpost
    -- Convert between Array.getD and Vector.getElem
    have toVec_getD {n : Nat} (v : Vector u64 n) (j : Nat) (hj : j < n) :
        v.toArray.getD j 0 = v[j] := by
      unfold Array.getD
      rw [dif_pos (show j < v.toArray.size by rw [Vector.size_toArray]; exact hj)]
      exact Vector.getElem_toArray _
    have hfp_lt : 5 * (i.toNat % 5) + i.toNat / 5 < 25 := by omega
    rw [toVec_getD _ _ hfp_lt] at hpost
    rw [toVec_getD _ k hk, toVec_getD _ _ hfp_lt, toVec_getD _ _ hi, toVec_getD _ k hk]
    exact hpost

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

set_option maxHeartbeats 6400000 in
@[spec] theorem load_block_spec (RATE : usize) (state : RustArray u64 25)
    (blocks : RustSlice u8) (start : usize)
    (hrate : RATE.toNat % 8 = 0)
    (hrate_le : RATE.toNat ≤ 200)
    (hbounds : start.toNat + RATE.toNat ≤ blocks.val.size) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_sha3.simd.portable.load_block RATE state blocks start
    ⦃ ⇓ r => ⌜ r.toVec = Sponge.load_block_pure RATE.toNat state.toVec
        blocks.val.toList start.toNat ⌝ ⦄ := by
  intro _
  unfold libcrux_sha3.simd.portable.load_block
  simp only [← lb_get_eq, ← lb_set_eq, ite_true]
  -- Step 1: Replace extraction's sorry invariants with True (removes sorry in pureInv)
  simp only [fold_range_inv_irrelevant (α := RustArray u64 25)
    (inv₂ := fun _ _ => pure True)
    (pureInv₂ := ⟨fun _ _ => True, fun _ _ => by intro _; rfl⟩)]
  -- Step 2: Replace second loop's True inv with xor_loop_inv (state_flat is in scope)
  conv in (rust_primitives.hax.folds.fold_range (0 : usize) _ (fun _ _ => pure True) state _ _) =>
    rw [fold_range_inv_irrelevant (α := RustArray u64 25)
      (inv₂ := fun (cur : RustArray u64 25) (k : USize64) =>
        pure (Sponge.xor_loop_inv state.toVec.toArray state_flat.toVec.toArray
          cur.toVec.toArray k.toNat))
      (pureInv₂ := ⟨fun cur k =>
        Sponge.xor_loop_inv state.toVec.toArray state_flat.toVec.toArray
          cur.toVec.toArray k.toNat,
        fun _ _ => by intro _; rfl⟩)]
  -- Step 3: Replace first loop's True inv with byte_loop_inv (only remaining True)
  simp only [fold_range_inv_irrelevant (α := RustArray u64 25)
    (inv₁ := fun _ _ => pure True)
    (inv₂ := fun (sf : RustArray u64 25) (k : USize64) =>
      pure (Sponge.byte_loop_inv blocks.val.toList start.toNat sf.toVec.toArray k.toNat))
    (pureInv₂ := ⟨fun sf k =>
      Sponge.byte_loop_inv blocks.val.toList start.toNat sf.toVec.toArray k.toNat,
      fun _ _ => by intro _; rfl⟩)]
  hax_mvcgen
  all_goals (try vc_omega)
  all_goals (try (have := blocks.size_lt_usizeSize; vc_omega))
  all_goals (try grind)
  -- vc5: byte_loop_inv init (all zeros, iteration 0)
  · simp only [USize64.reduceToNat]
    exact Sponge.byte_loop_inv_init blocks.val.toList start.toNat
  -- vc14: byte_loop_inv step (TODO: bridge from_le_bytes ↔ bytes_to_u64_le with USize64 arithmetic)
  · sorry
  -- vc18: xor_loop_inv init
  · exact Sponge.xor_loop_inv_init _ _
  -- vc28: xor_loop_inv step (same as xor_loop_spec vc12)
  · sorry -- vc28: xor_loop_inv step (TODO: USize64 arithmetic issues)
  -- vc29: composition via byte_xor_compose
  · simp only [USize64.reduceToNat] at *
    rename_i _ _ _ _ _ _ _ _ _ _ _ _ _ _ rn hn sf hbyte rn2 hn2 result hxor
    have : rn.toNat = rn2.toNat := by omega
    rw [this] at hbyte
    exact Sponge.byte_xor_compose RATE.toNat state.toVec blocks.val.toList start.toNat
      sf.toVec.toArray result.toVec.toArray rn2.toNat (by omega) hbyte hxor
      (by simp [Vector.size_toArray])

/-! ## Specs for store_block helpers -/

-- copy_from_slice: replaces destination with source (requires equal lengths)
-- Must be @[specset int] so hax_mvcgen with specset "int" finds it
-- (the Hax library only has a @[hax_spec] with specset "bv")
@[specset int] theorem copy_from_slice_spec {α : Type}
    [inst1 : core_models.marker.Copy.AssociatedTypes α]
    [inst2 : core_models.marker.Copy α]
    (s src : RustSlice α)
    (hlen : s.val.size = src.val.size) :
    ⦃ ⌜ True ⌝ ⦄
    core_models.slice.Impl.copy_from_slice α s src
    ⦃ ⇓ r => ⌜ r = src ⌝ ⦄ := by
  intro _
  unfold core_models.slice.Impl.copy_from_slice rust_primitives.mem.replace
  simp

/-- Splice: replace s[start..stop] with v, keep the rest. -/
private def splice_seq (s : RustSlice α) (start stop : Nat) (v : RustSlice α)
    (hend : stop ≤ s.val.size) (hstart : start ≤ stop)
    (hv : v.val.size = stop - start) : RustSlice α :=
  let result := (s.val.extract 0 start) ++ v.val ++ (s.val.extract stop s.val.size)
  have : result.size = s.val.size := by
    simp only [result, Array.size_append, Array.size_extract, Nat.min_self,
      Nat.min_eq_left hend, Nat.min_eq_left (Nat.le_trans hstart hend)]; omega
  ⟨result, by rw [this]; exact s.size_lt_usizeSize⟩

/-- Element-wise description of splice_seq: positions in [start, stop) come from v,
    positions outside come from s. -/
private theorem splice_seq_getD {α : Type}
    (s : RustSlice α) (start stop : Nat) (v : RustSlice α)
    (hend : stop ≤ s.val.size) (hstart : start ≤ stop)
    (hv : v.val.size = stop - start)
    (k : Nat) (hk : k < s.val.size) (d : α) :
    (splice_seq s start stop v hend hstart hv).val.toList.getD k d =
      if start ≤ k ∧ k < stop
      then v.val.toList.getD (k - start) d
      else s.val.toList.getD k d := by
  sorry

open core_models.ops.range in
@[spec] theorem update_at_range_spec {α : Type}
    (s : RustSlice α) (r : Range usize) (v : RustSlice α)
    (hend : r._end.toNat ≤ s.val.size) (hstart : r.start.toNat ≤ r._end.toNat)
    (hv : v.val.size = r._end.toNat - r.start.toNat) :
    ⦃ ⌜ True ⌝ ⦄
    rust_primitives.hax.monomorphized_update_at.update_at_range s r v
    ⦃ ⇓ res => ⌜ res = splice_seq s r.start.toNat r._end.toNat v hend hstart hv ⌝ ⦄ := by
  intro _
  unfold rust_primitives.hax.monomorphized_update_at.update_at_range
  rw [dif_pos ⟨hend, hstart, hv⟩]
  simp [splice_seq]

attribute [local irreducible] rust_primitives.hax.monomorphized_update_at.update_at_range

-- RangeTo indexing for RustArray
open core_models.ops.range in
@[spec] theorem RangeTo_getElemRustArray_spec {α : Type} {n : usize}
    (a : RustArray α n) (e : usize) (he : e.toNat ≤ a.toVec.size) :
    ⦃ ⌜ True ⌝ ⦄
    (a[RangeTo.mk e]_?)
    ⦃ ⇓ r => ⌜ r.val = (Vector.extract a.toVec 0 e.toNat).toArray ⌝ ⦄ := by
  sorry

/-! ## store_block proof -/

attribute [irreducible] Sponge.lane_byte Sponge.store_block_pure

/-- The size of a slice extracted from `out` at `[pos, pos+rem]` equals
    the size of a Vector extract `[0, rem]` from an 8-element vector,
    when `rem ≤ 8` and `pos + rem ≤ out.size`. -/
private theorem remainder_copy_len_eq
    (out_arr : Array u8) (pos rem : Nat)
    (v : Vector u8 8)
    (hrem : rem ≤ 8)
    (hpos : pos + rem ≤ out_arr.size) :
    (out_arr.extract pos (pos + rem)).size = (Vector.extract v 0 rem).toArray.size := by
  simp [Array.size_extract, Vector.size_toArray, Nat.min_eq_left hpos,
    Nat.min_eq_left hrem]

attribute [local irreducible]
  libcrux_sha3.simd.portable.store_block

set_option maxHeartbeats 6400000 in
@[spec] theorem store_block_spec (RATE : usize) (s : RustArray u64 25)
    (out : RustSlice u8) (start : usize) (len : usize)
    (hrate_le : RATE.toNat ≤ 200)
    (hlen : len.toNat ≤ RATE.toNat)
    (hout : start.toNat + len.toNat ≤ out.val.size) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_sha3.simd.portable.store_block RATE s out start len
    ⦃ ⇓ r => ⌜ r.val.size = out.val.size ∧
      (∀ b, b < len.toNat →
        r.val.toList.getD (start.toNat + b) 0 =
          Sponge.lane_byte (s.toVec.toArray.getD (Sponge.flat_perm (b / 8)) 0) (b % 8)) ⌝ ⦄ := by
  sorry
  /- Original proof (depends on splice_seq_getD):
  intro _
  unfold libcrux_sha3.simd.portable.store_block
  simp only [ite_true]
  -- Step 1: Replace extraction's invariant with True (removes the sorry in pureInv)
  simp only [fold_range_inv_irrelevant (α := RustSlice u8)
    (inv₂ := fun _ _ => pure True)
    (pureInv₂ := ⟨fun _ _ => True, fun _ _ => by intro _; rfl⟩)]
  -- Step 2: Replace True with our real invariant
  simp only [fold_range_inv_irrelevant (α := RustSlice u8)
    (inv₂ := fun (o : RustSlice u8) (k : USize64) =>
      pure (Sponge.store_loop_inv s.toVec out.val.size start.toNat o.val k.toNat))
    (pureInv₂ := ⟨fun o k => Sponge.store_loop_inv s.toVec out.val.size start.toNat o.val k.toNat,
      fun _ _ => by intro _; rfl⟩)]
  -- Eliminate dead `let out_len ← Impl.len` binding
  simp only [core_models.slice.Impl.len, rust_primitives.slice.slice_length, pure_bind]
  -- Replace get_ij and copy_from_slice with irreducible wrappers
  simp only [← lb_get_eq, ← copy_from_slice_u8_eq]
  hax_mvcgen
  all_goals (try vc_omega)
  all_goals (try (have := out.size_lt_usizeSize; vc_omega))
  all_goals (try grind)
  -- vc3: initial invariant
  · simp only [USize64.reduceToNat]; unfold Sponge.store_loop_inv
    exact ⟨rfl, fun _ h => absurd h (by omega)⟩
  -- vc13/14/15/29/32: bounds + size equalities
  all_goals (try (simp only [Sponge.store_loop_inv, USize64.reduceToNat, Array.size_extract,
    Vector.size_toArray] at *; omega))
  -- vc14: extract size = to_le_bytes array size (= 8)
  · simp only [Sponge.store_loop_inv, USize64.reduceToNat] at *; subst_vars
    simp [Array.size_extract]; omega
  -- vc18: loop step — splice_seq preserves invariant at i+1
  · -- Name mvcgen variables
    rename_i _ nfull hnfull acc i _ hi_lt hinv
      rdiv hdiv rmod hmod lane hlane r8i h8i rpos hpos rend hend rend2 hend2
      rslice hslice rbytes hbytes rspliced hspliced
    simp only [USize64.reduceToNat] at *
    -- Eliminate intermediate variables
    subst hspliced hslice
    -- Unfold the invariant
    rw [USize64.toNat_add_of_lt (by simp [USize64.size, UInt64.size]; omega)]
    obtain ⟨hsize, hspec⟩ := hinv
    unfold Sponge.store_loop_inv
    refine ⟨by simp [splice_seq, hsize]; vc_omega, ?_⟩
    intro b hb
    -- Use splice_seq_getD to case-split
    have hb_lt : start.toNat + b < acc.val.size := by
      rw [hsize]; vc_omega
    have hgetD := splice_seq_getD acc (rpos.toNat) (rend.toNat) rbytes
      (by vc_omega) (by vc_omega) (by subst hbytes hlane; simp; vc_omega)
      (start.toNat + b) hb_lt (0 : u8)
    rw [hgetD]
    split
    · -- New region: start + 8*i ≤ start + b < start + 8*i + 8
      -- So b is in [8*i, 8*(i+1)), meaning b/8 = i and b%8 = b - 8*i
      rename_i hcase
      obtain ⟨hlo, hhi⟩ := hcase
      rw [hpos, h8i] at hlo hhi
      simp only [USize64.reduceToNat] at hlo hhi
      subst hbytes hlane hpos h8i hmod hdiv
      simp only [USize64.reduceToNat] at *
      -- b - (start + 8*i) selects the byte within the 8-byte LE encoding
      have hbi : b / 8 = i.toNat := by omega
      have hbm : b % 8 = b - 8 * i.toNat := by omega
      -- The getD into the 8-element array selects the (b - 8*i)-th byte
      simp only [Sponge.flat_perm, hbi]
      -- Unfold lane_byte
      simp only [Sponge.lane_byte]
      -- Now we need: rbytes.val.toList.getD (start+b - rpos) 0 = (lane >>> (8*(b%8))).toUInt8
      -- where rbytes is the 8-byte LE encoding of lane
      -- The array is #[lane%256, (lane>>>8)%256, ..., (lane>>>56)%256]
      -- and we're accessing index (b - 8*i) = b%8
      rw [show start.toNat + b - (start.toNat + 8 * i.toNat) = b - 8 * i.toNat from by omega]
      interval_cases (b - 8 * i.toNat) <;> simp_all
    · -- Old region: b < 8*i or b ≥ 8*(i+1)
      -- But b < 8*(i+1), so b < 8*i
      rename_i hold
      rw [hpos, h8i] at hold
      simp only [USize64.reduceToNat] at hold
      have hbi : b < 8 * i.toNat := by omega
      exact hspec b hbi
  -- vc31: remainder length match
  · simp only [USize64.reduceToNat, Sponge.store_loop_inv] at *; subst_vars
    simp_all [Array.size_extract, Vector.size_toArray]; omega
  -- vc35: composition (with remainder)
  · -- Name mvcgen variables
    rename_i _ nfull hnfull loop_out hinv rem hrem rdec hdec_true hdec_eq
      rdiv hdiv rmod hmod lane hlane rend hend rsub hsub rpos hpos rend2 hend2
      rslice hslice rbytes hbytes rcopy hcopy rspliced hspliced
    simp only [USize64.reduceToNat, decide_eq_true_eq] at *
    -- Eliminate intermediate variables
    subst hspliced hcopy
    obtain ⟨hsize, hspec⟩ := hinv
    -- Derive key arithmetic facts
    have hrem_pos : rem.toNat > 0 := by omega
    have hrem_le8 : rem.toNat ≤ 8 := by omega
    have hlen_eq : len.toNat = 8 * nfull.toNat + rem.toNat := by omega
    constructor
    · -- size preserved by splice_seq
      simp [splice_seq, hsize]; vc_omega
    · intro b hb
      have hb_lt : start.toNat + b < loop_out.val.size := by rw [hsize]; vc_omega
      have hgetD := splice_seq_getD loop_out (rsub.toNat) (rpos.toNat) rbytes
        (by vc_omega) (by vc_omega) (by subst hbytes hlane hslice; simp [Array.size_extract, Vector.size_toArray]; vc_omega)
        (start.toNat + b) hb_lt (0 : u8)
      rw [hgetD]
      split
      · -- New region: in the remainder splice [start+8*nfull, start+len)
        rename_i hcase
        obtain ⟨hlo, hhi⟩ := hcase
        rw [hsub, hend, hpos] at hlo hhi
        simp only [USize64.reduceToNat] at hlo hhi
        subst hbytes hlane hslice hsub hend hpos hmod hdiv hrem hnfull
        simp only [USize64.reduceToNat] at *
        -- b/8 = nfull (= len/8), b%8 = b - 8*nfull
        have hbi : b / 8 = nfull.toNat := by omega
        simp only [Sponge.flat_perm, hbi, Sponge.lane_byte]
        -- The rbytes array is the first `rem` bytes of the LE encoding, accessed at index (b - 8*nfull)
        -- rbytes.val = (Vector.extract #v[..8 bytes..] 0 rem).toArray
        -- getD at (start+b - (start+8*nfull)) = getD at (b - 8*nfull)
        rw [show start.toNat + b - (start.toNat + len.toNat - len.toNat % 8) =
          b - 8 * (len.toNat / 8) from by omega]
        -- The extract of the 8-byte vector at index (b - 8*nfull) where b - 8*nfull < rem ≤ 8
        have hbm_lt : b - 8 * (len.toNat / 8) < len.toNat % 8 := by omega
        -- 8-way case split on b - 8*nfull to match byte positions
        interval_cases (b - 8 * (len.toNat / 8)) <;> simp_all [Vector.extract, Vector.toArray, Array.extract, List.getD, Array.toList]
      · -- Old region: b < 8*nfull (outside splice range)
        rename_i hold
        rw [hsub, hend, hpos] at hold
        simp only [USize64.reduceToNat] at hold
        have hbi : b < 8 * nfull.toNat := by omega
        exact hspec b hbi
  -- vc36: composition (without remainder, len % 8 = 0)
  · rename_i _ nfull hnfull loop_out hinv rem hrem rdec hdec_false hdec_eq
    simp only [USize64.reduceToNat, decide_eq_true_eq] at *
    obtain ⟨hsize, hspec⟩ := hinv
    exact ⟨hsize, fun b hb => hspec b (by omega)⟩
  -/

-- load_last
attribute [local irreducible] libcrux_sha3.simd.portable.load_last

set_option maxHeartbeats 3200000 in
@[spec] theorem load_last_spec (RATE : usize) (DELIM : u8)
    (state : RustArray u64 25) (blocks : RustSlice u8)
    (start : usize) (len : usize)
    (hrate : RATE.toNat % 8 = 0)
    (hlen : start.toNat + len.toNat ≤ blocks.val.size)
    (hlen_rate : len.toNat < RATE.toNat) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_sha3.simd.portable.load_last RATE DELIM state blocks start len
    ⦃ ⇓ r => ⌜ r.toVec = Sponge.load_last_pure RATE.toNat DELIM state.toVec
        blocks.val.toList start.toNat len.toNat ⌝ ⦄ := by
  intro _
  unfold libcrux_sha3.simd.portable.load_last
  simp only [← copy_from_slice_u8_eq]
  hax_mvcgen
  all_goals (try vc_omega)
  all_goals (try grind)
  -- vc1, vc4: start + len < USize64.size (overflow)
  all_goals (try (have := blocks.size_lt_usizeSize; omega))
  -- vc3, vc8: len ≤ RATE (replicate size)
  all_goals (try (simp only [Vector.size, Vector.size_toArray]; omega))
  -- vc7: copy_from_slice size match (both extracts have size len)
  all_goals (try (subst_vars; simp only [Array.size_extract, Vector.size_toArray,
    Vector.extract, Vector.replicate, Nat.min_eq_left (by omega : len.toNat ≤ RATE.toNat)] at *; omega))
  -- vc17: assert failure path (contradiction: len < RATE but ¬len < buffer.size where buffer.size = RATE)
  all_goals (try (exfalso; simp only [splice_seq, Vector.size, Array.size_append,
    Array.size_extract, Vector.replicate, Vector.size_toArray,
    Nat.min_eq_left (by omega : len.toNat ≤ RATE.toNat)] at *; omega))
  -- vc14, vc15: depend on load_block sorry
  all_goals sorry

-- absorb_block = Absorb.load_block + keccakf1600
attribute [local irreducible] Impl_2.absorb_block

set_option maxHeartbeats 800000 in
@[spec] theorem absorb_block_spec (RATE : usize) (st : KeccakState 1 u64)
    (input : RustArray (RustSlice u8) 1) (start : usize)
    (hrate : RATE.toNat % 8 = 0)
    (hrate_le : RATE.toNat ≤ 200)
    (hbounds : start.toNat + RATE.toNat ≤ (input.toVec[(0 : Fin 1)]).val.size) :
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
  all_goals (try vc_omega)
  all_goals (try grind)
  -- vc2: load_block precondition (sorry from hax_spec pureRequires)
  · sorry
  -- vc3: composition — load_block (sorry postcondition) + keccakf1600
  · rename_i _ blocks hblocks st' hst' result hresult
    -- hst' : sorry.val st' (= st'.toVec = load_block_pure ...)
    -- hresult : result.st.toVec = keccak_f_pure st'.toVec
    rw [hresult]
    unfold Sponge.absorb_block_pure
    congr 1
    -- st'.toVec = load_block_pure ... (depends on load_block sorry)
    sorry

-- absorb_final = Absorb.load_last + keccakf1600
attribute [local irreducible] Impl_2.absorb_final

set_option maxHeartbeats 800000 in
@[spec] theorem absorb_final_spec (RATE : usize) (DELIM : u8)
    (st : KeccakState 1 u64) (input : RustArray (RustSlice u8) 1)
    (start : usize) (len : usize)
    (hrate : RATE.toNat % 8 = 0)
    (hlen : len.toNat < RATE.toNat) :
    ⦃ ⌜ True ⌝ ⦄
    Impl_2.absorb_final 1 u64 RATE DELIM st input start len
    ⦃ ⇓ r => ⌜ r.st.toVec = Sponge.absorb_final_pure RATE.toNat DELIM st.st.toVec
        (input.toVec[(0 : Fin 1)]).val.toList start.toNat len.toNat ⌝ ⦄ := by
  intro _
  unfold Impl_2.absorb_final
  simp only [libcrux_sha3.traits.Absorb.load_last,
    libcrux_sha3.simd.portable.Impl_1,
    libcrux_sha3.traits.Absorb.AssociatedTypes,
    libcrux_sha3.simd.portable.Impl_1.AssociatedTypes]
  hax_mvcgen
  all_goals (try vc_omega)
  all_goals (try grind)
  -- vc2: load_last precondition (sorry from hax_spec pureRequires)
  · sorry
  -- vc3: composition — load_last (sorry postcondition) + keccakf1600
  · rename_i _ _ _ _ _ _ _ blocks hblocks st' hst' result hresult
    rw [hresult]
    unfold Sponge.absorb_final_pure
    congr 1
    -- st'.toVec = load_last_pure ... (depends on load_last sorry)
    sorry

/-! ## Squeeze -/

-- Squeeze.squeeze (portable) = store_block on st.st
-- The trait instance dispatches to store_block directly.
-- We need a spec for the trait method call as it appears in keccak1.

@[spec] theorem squeeze_spec (RATE : usize)
    (st : KeccakState 1 u64) (out : RustSlice u8)
    (start : usize) (len : usize)
    (hlen : len.toNat ≤ RATE.toNat)
    (hrate_le : RATE.toNat ≤ 200)
    (hout : start.toNat + len.toNat ≤ out.val.size) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_sha3.traits.Squeeze.squeeze
      (KeccakState 1 u64) u64 RATE st out start len
    ⦃ ⇓ r => ⌜ True ⌝ ⦄ := by
  intro _
  unfold libcrux_sha3.traits.Squeeze.squeeze
  simp only [libcrux_sha3.simd.portable.Impl_2]
  simp only [Std.Do.WPMonad.wp_bind, Std.Do.WPMonad.wp_pure, bind_pure]
  exact Std.Do.Triple.of_entails_right _ _ _ _
    (store_block_spec RATE st.st out start len hrate_le hlen hout)
    (by simp [Std.Do.PostCond.entails, Std.Do.ExceptConds.entails]) trivial

attribute [local irreducible]
  libcrux_sha3.traits.Squeeze.squeeze

-- Also need: core_models.slice.Impl.len
@[spec] theorem slice_len_spec (out : RustSlice u8) :
    ⦃ ⌜ True ⌝ ⦄
    core_models.slice.Impl.len u8 out
    ⦃ ⇓ r => ⌜ r.toNat = out.val.size ⌝ ⦄ := by
  intro _; unfold core_models.slice.Impl.len rust_primitives.slice.slice_length
  simp; exact out.size_lt_usizeSize

-- proof_utils.lemmas.lemma_mul_succ_le (ghost lemma used in keccak1)
@[spec] theorem lemma_mul_succ_le_spec (i n RATE : usize) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_sha3.proof_utils.lemmas.lemma_mul_succ_le i n RATE
    ⦃ ⇓ r => ⌜ True ⌝ ⦄ := by
  intro _; unfold libcrux_sha3.proof_utils.lemmas.lemma_mul_succ_le; simp

/-! ## keccak1: try mvcgen with True postcondition to test composition -/

attribute [local irreducible] libcrux_sha3.generic_keccak.portable.keccak1

-- Helper: RATE ≠ 0 from 0 < RATE.toNat
private theorem rate_ne_zero {RATE : usize} (h : 0 < RATE.toNat) : RATE ≠ 0 := by
  intro heq; subst heq; simp [USize64.reduceToNat] at h

-- Helper: subOverflow is false when b ≤ a (Nat level)
private theorem sub_no_overflow {a b : usize}
    (h : b.toNat ≤ a.toNat) : ¬USize64.subOverflow a b = true := by
  simp only [USize64.subOverflow, Bool.not_eq_true]
  rw [BitVec.usubOverflow_eq, decide_eq_false_iff_not]
  intro hlt; simp [BitVec.lt_def, USize64.toNat_toBitVec] at hlt; omega

-- Helper: USize64.ofNat a.val.size == output_len from squeeze_spec preserving size
-- (squeeze/store_block preserves slice size — needed for loop invariant)

set_option maxHeartbeats 6400000 in
theorem keccak1_spec (RATE : usize) (DELIM : u8)
    (input output : RustSlice u8)
    (hrate : RATE.toNat % 8 = 0)
    (hrate_pos : 0 < RATE.toNat)
    (hrate_le : RATE.toNat ≤ 200) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_sha3.generic_keccak.portable.keccak1 RATE DELIM input output
    ⦃ ⇓ r => ⌜ True ⌝ ⦄ := by
  intro _
  unfold libcrux_sha3.generic_keccak.portable.keccak1
  hax_mvcgen
  all_goals (try vc_omega)
  all_goals (try grind)
  all_goals (try trivial)
  -- RATE ≠ 0 goals
  all_goals (try exact rate_ne_zero hrate_pos)
  -- RATE ≤ 200 goals
  all_goals (try exact hrate_le)
  -- subOverflow goals: mod ≤ value
  all_goals (try (apply sub_no_overflow; simp_all [USize64.reduceToNat]; omega))
  -- output_rem ≤ RATE: mod < divisor
  all_goals (try (simp_all [USize64.reduceToNat]; omega))
  all_goals sorry
