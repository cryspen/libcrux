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

/-- Absorb all full blocks: fold absorb_block_pure over n_blocks blocks of RATE bytes. -/
def absorb_all_pure (RATE : Nat) (state : Vector u64 25)
    (input : List u8) (n_blocks : Nat) : Vector u64 25 :=
  (List.range n_blocks).foldl (fun st i => absorb_block_pure RATE st input (i * RATE)) state

/-- Full squeeze phase: extract `output_len` bytes from state.
    Applies keccak_f between rate-sized blocks.
    Round 0 extracts from the current state; subsequent rounds apply keccak_f first.
    This matches FIPS 202 Algorithm 8 squeeze loop. -/
def squeeze_pure (RATE : Nat) (state : Vector u64 25) (output_len : Nat) : List u8 :=
  if RATE = 0 ∨ output_len = 0 then []
  else if output_len ≤ RATE then store_block_pure RATE state 0 output_len
  else store_block_pure RATE state 0 RATE ++
       squeeze_pure RATE (keccak_f_pure state) (output_len - RATE)
termination_by output_len

/-- Full keccak sponge: absorb input, squeeze output.
    Matches FIPS 202 Algorithm 8 (with pad10*1). -/
def keccak1_pure (RATE : Nat) (DELIM : u8) (input : List u8) (output_len : Nat) : List u8 :=
  if RATE = 0 then [] else
  let n_blocks := input.length / RATE
  let input_rem := input.length % RATE
  let state0 := Vector.replicate 25 (0 : u64)
  let state1 := absorb_all_pure RATE state0 input n_blocks
  let start := input.length - input_rem
  let state2 := absorb_final_pure RATE DELIM state1 input start input_rem
  squeeze_pure RATE state2 output_len

/-- State after the full absorb phase (absorb_all + absorb_final). -/
noncomputable def keccak1_absorb_state (RATE : Nat) (DELIM : u8) (input : List u8) : Vector u64 25 :=
  let n := input.length / RATE
  let st0 := Vector.replicate 25 (0 : u64)
  let st1 := absorb_all_pure RATE st0 input n
  absorb_final_pure RATE DELIM st1 input (input.length - input.length % RATE) (input.length % RATE)

theorem absorb_all_pure_zero (RATE : Nat) (state : Vector u64 25) (input : List u8) :
    absorb_all_pure RATE state input 0 = state := by
  simp [absorb_all_pure]

theorem absorb_all_pure_succ (RATE : Nat) (state : Vector u64 25) (input : List u8) (i : Nat) :
    absorb_all_pure RATE state input (i + 1) =
    absorb_block_pure RATE (absorb_all_pure RATE state input i) input (i * RATE) := by
  unfold absorb_all_pure
  rw [show List.range (i + 1) = List.range i ++ [i] from List.range_succ]
  simp [List.foldl_append]

theorem keccak1_pure_eq_squeeze (RATE : Nat) (DELIM : u8) (input : List u8) (output_len : Nat)
    (hrate : RATE > 0) :
    keccak1_pure RATE DELIM input output_len =
    squeeze_pure RATE (keccak1_absorb_state RATE DELIM input) output_len := by
  unfold keccak1_pure keccak1_absorb_state
  simp [show ¬(RATE = 0) from by omega]

theorem squeeze_pure_le_rate (RATE : Nat) (state : Vector u64 25) (output_len : Nat)
    (hR : 0 < RATE) (hle : output_len ≤ RATE) :
    squeeze_pure RATE state output_len = store_block_pure RATE state 0 output_len := by
  rw [squeeze_pure.eq_1]
  by_cases hout0 : output_len = 0
  · subst hout0; simp [store_block_pure]
  · simp [show ¬(RATE = 0 ∨ output_len = 0) from by omega, hle]

-- Helper: length of store_block_pure
private theorem store_block_pure_length' (RATE : Nat) (state : Vector u64 25) (start len : Nat) :
    (store_block_pure RATE state start len).length = len := by simp [store_block_pure]

-- Length of squeeze_pure
theorem squeeze_pure_length (RATE : Nat) (state : Vector u64 25) (output_len : Nat) (hR : 0 < RATE) :
    (squeeze_pure RATE state output_len).length = output_len := by
  induction output_len using Nat.strongRecOn generalizing state with
  | _ output_len ih =>
    by_cases h0 : output_len = 0
    · subst h0; simp [squeeze_pure]
    · rw [squeeze_pure.eq_1]
      simp only [show ¬(RATE = 0 ∨ output_len = 0) from by omega, ite_false]
      by_cases hle : output_len ≤ RATE
      · simp only [hle, ite_true, store_block_pure, List.length_map, List.length_range]
      · simp only [hle, ite_false, List.length_append, store_block_pure, List.length_map, List.length_range]
        rw [ih (output_len - RATE) (by omega) (keccak_f_pure state)]; omega

-- Helper: getD of append
private theorem getD_append_left {l₁ l₂ : List α} (h : n < l₁.length) :
    (l₁ ++ l₂).getD n d = l₁.getD n d := by
  simp only [List.getD, List.getElem?_append_left h]
private theorem getD_append_right {l₁ l₂ : List α} (h : l₁.length ≤ n) :
    (l₁ ++ l₂).getD n d = l₂.getD (n - l₁.length) d := by
  simp only [List.getD, List.getElem?_append_right h]

-- Helper: getD of store_block_pure
private theorem store_block_pure_getD' (RATE : Nat) (state : Vector u64 25)
    (len b : Nat) (hb : b < len) :
    (store_block_pure RATE state 0 len).getD b (0 : u8) =
    lane_byte (state.toArray.getD (flat_perm (b / 8)) 0) (b % 8) := by
  simp only [store_block_pure, List.getD]
  rw [List.getElem?_eq_getElem (by simp; omega)]; simp

-- Helper: (b - RATE) % RATE = b % RATE
private theorem sub_mod_rate (b RATE : Nat) (h : RATE ≤ b) : (b - RATE) % RATE = b % RATE := by
  have := Nat.add_mod_right (b - RATE) RATE; rw [Nat.sub_add_cancel h] at this; exact this.symm

-- Helper: (b - RATE) / RATE = b / RATE - 1
private theorem sub_div_rate (b RATE : Nat) (h : RATE ≤ b) (hR : 0 < RATE) :
    (b - RATE) / RATE = b / RATE - 1 := by
  have key : b / RATE = (b - RATE) / RATE + 1 := by
    rw [← Nat.add_div_right (b - RATE) hR, Nat.sub_add_cancel h]
  exact Nat.eq_sub_of_add_eq' (by rw [Nat.add_comm]; exact key.symm)

-- Helper: Nat.repeat keccak_f_pure shift
private theorem repeat_kf_shift (m : Nat) (s : Vector u64 25) :
    Nat.repeat keccak_f_pure m (keccak_f_pure s) = Nat.repeat keccak_f_pure (m + 1) s := by
  induction m with | zero => rfl | succ n ih => simp [Nat.repeat, ih]

-- Key access lemma: byte b of squeeze_pure = lane_byte of iterate(b/RATE) state
theorem squeeze_pure_getD (RATE : Nat) (state : Vector u64 25) (output_len : Nat)
    (hR : 0 < RATE) (b : Nat) (hb : b < output_len) :
    (squeeze_pure RATE state output_len).getD b (0 : u8) =
    lane_byte ((Nat.repeat keccak_f_pure (b / RATE) state).toArray.getD
      (flat_perm ((b % RATE) / 8)) 0) ((b % RATE) % 8) := by
  induction output_len using Nat.strongRecOn generalizing state b with
  | _ output_len ih =>
    rw [squeeze_pure.eq_1]
    simp only [show ¬(RATE = 0 ∨ output_len = 0) from by omega, ite_false]
    by_cases hle : output_len ≤ RATE
    · simp only [hle, ite_true]
      have hbR : b < RATE := by omega
      rw [show b / RATE = 0 from Nat.div_eq_zero_iff.mpr (Or.inr hbR)]
      simp only [Nat.repeat, Nat.mod_eq_of_lt hbR]
      exact store_block_pure_getD' RATE state output_len b hb
    · simp only [hle, ite_false]
      by_cases hb_first : b < RATE
      · rw [getD_append_left (by rw [store_block_pure_length']; exact hb_first)]
        rw [show b / RATE = 0 from Nat.div_eq_zero_iff.mpr (Or.inr hb_first)]
        simp only [Nat.repeat, Nat.mod_eq_of_lt hb_first]
        exact store_block_pure_getD' RATE state RATE b hb_first
      · have hge : RATE ≤ b := Nat.not_lt.mp hb_first
        rw [getD_append_right (by rw [store_block_pure_length']; exact hge), store_block_pure_length']
        rw [ih (output_len - RATE) (by omega) (keccak_f_pure state) (b - RATE) (by omega)]
        rw [sub_mod_rate b RATE hge, sub_div_rate b RATE hge hR]
        obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (show b / RATE ≠ 0 by
          intro h; have := Nat.div_eq_zero_iff.mp h; omega)
        rw [hm, show m + 1 - 1 = m from by omega, repeat_kf_shift]

-- Length of keccak1_pure
theorem keccak1_pure_length (RATE : Nat) (DELIM : u8) (input : List u8)
    (output_len : Nat) (hR : 0 < RATE) :
    (keccak1_pure RATE DELIM input output_len).length = output_len := by
  unfold keccak1_pure; simp [show ¬(RATE = 0) from by omega, squeeze_pure_length _ _ _ hR]

end Sponge

private theorem list_eq_map_range_of_getD {l : List u8} {n : Nat} {f : Nat → u8}
    (hlen : l.length = n)
    (helems : ∀ i, i < n → l.getD i 0 = f i) :
    l = (List.range n).map f := by
  apply List.ext_getElem (by simp; exact hlen)
  intro i hi₁ _
  have hi : i < n := by omega
  specialize helems i hi
  simp only [List.getD] at helems
  rw [List.getElem?_eq_getElem (by omega)] at helems
  simp only [Option.getD_some] at helems
  simp only [List.getElem_map, List.getElem_range, helems]

-- Chain absorb hypotheses to show state = keccak1_absorb_state
private theorem absorb_state_connection {RATE : Nat} {DELIM : u8}
    {input_arr : Array u8} (_ : 0 < RATE)
    {n_input n_blocks n_rem start : Nat}
    {st_all st_final : Vector u64 25}
    (h1 : n_input = input_arr.size)
    (h2 : n_blocks = n_input / RATE)
    (h3 : n_rem = n_input % RATE)
    (h4 : start = n_input - n_rem)
    (h5 : st_all = Sponge.absorb_all_pure RATE (Vector.replicate 25 0) input_arr.toList n_blocks)
    (h6 : st_final = Sponge.absorb_final_pure RATE DELIM st_all input_arr.toList start n_rem) :
    Sponge.keccak1_absorb_state RATE DELIM input_arr.toList = st_final := by
  unfold Sponge.keccak1_absorb_state
  simp only [Array.length_toList, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6]

private theorem new_state_is_replicate {v : Vector u64 25}
    (h : ∀ k, k < 25 → v.toArray.getD k 0 = 0) :
    v = Vector.replicate 25 0 := by
  apply Vector.ext; intro k hk
  rw [show (Vector.replicate 25 (0 : u64))[k] = 0 from by simp [Vector.getElem_replicate]]
  have := h k hk
  rwa [Vector.toArray_getD_eq v k 0 hk] at this

namespace Sponge

/-- Invariant for store_block main loop:
    After i iterations, the first 8*i bytes starting at `start` have been written
    with LE encodings of the corresponding state lanes. Size is preserved. -/
def store_loop_inv (state : Vector u64 25) (out_size start : Nat)
    (orig_out : List u8) (cur_out : Array u8) (i : Nat) : Prop :=
  cur_out.size = out_size ∧
  (∀ b, b < 8 * i →
    cur_out.toList.getD (start + b) 0 =
      lane_byte (state.toArray.getD (flat_perm (b / 8)) 0) (b % 8)) ∧
  (∀ b, b < out_size → (b < start ∨ b ≥ start + 8 * i) →
    cur_out.toList.getD b 0 = orig_out.getD b 0)

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
      ⟨fun _ _ => True, by intros; intro; mvcgen⟩
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
      ⟨fun _ _ => True, by intros; intro; mvcgen⟩
    ⦃ ⇓ r => ⌜ Sponge.xor_loop_inv state.toVec.toArray state_flat.toVec.toArray
        r.toVec.toArray n.toNat ⌝ ⦄ := by
  intro _
  -- Rewrite get_ij/set_ij to local wrappers
  simp only [← lb_get_eq, ← lb_set_eq]
  -- Swap trivial invariant → xor_loop_inv
  rw [show rust_primitives.hax.folds.fold_range (0 : USize64) n
    (fun state _ => (do (pure true) : RustM Bool)) state _ ⟨fun _ _ => True, by intros; intro; mvcgen⟩ =
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
  -- vc14: byte_loop_inv step
  · rename_i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ acc i _ hi_lt inv _ _ _ _ _ _ _ _ _ _ bytes hbytes _
    simp only [USize64.reduceToNat] at *
    have hi25 : i.toNat < 25 := by grind
    rw [USize64.toNat_add_of_lt (by simp [USize64.size, UInt64.size]; omega)]
    have ⟨hsize_inv, hspec_inv⟩ := inv
    unfold Sponge.byte_loop_inv
    refine ⟨by simp [Vector.size_toArray], ?_⟩
    intro j hj
    subst hbytes
    simp only [Vector.toArray_set, USize64.reduceToNat] at *
    have ⟨_, hspec⟩ := inv
    simp_all [Array.getElem_set, Array.getD]
    split
    · -- j = i: bridge from_le_bytes ↔ bytes_to_u64_le
      rename_i hji; subst hji; simp only [show i.toNat < i.toNat + 1 from by omega, ite_true]
      have hbd : start.toNat + 8 * i.toNat + 8 ≤ blocks.val.size := by
        have : i.toNat + 1 ≤ RATE.toNat / 8 := by grind
        have : (i.toNat + 1) * 8 ≤ (RATE.toNat / 8) * 8 :=
          Nat.mul_le_mul_right 8 this
        have := Nat.div_mul_le_self RATE.toNat 8; omega
      unfold Sponge.bytes_to_u64_le; unfold List.getD
      simp [show ∀ k, k ≤ 7 → start.toNat + 8 * i.toNat + k < blocks.val.size from by omega,
        show start.toNat + 8 * i.toNat < blocks.val.size from by omega]
    · -- j ≠ i: old invariant
      rename_i hji
      simp only [show (j < i.toNat + 1) ↔ (j < i.toNat) from by omega]
  -- vc18: xor_loop_inv init
  · exact Sponge.xor_loop_inv_init _ _
  -- vc28: xor_loop_inv step (same as xor_loop_spec vc12)
  · -- vc28: xor_loop_inv step
    rename_i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ acc i _ hi_lt inv rdiv hdiv rmod hmod rdiv2 hdiv2 rmod2 hmod2 rget hget rsf hsf rnew
    intro hsize hset_post
    simp only [USize64.reduceToNat] at *
    have hi : i.toNat < 25 := by grind
    rw [show (i + 1).toNat = i.toNat + 1 from
      USize64.toNat_add_of_lt (by simp [USize64.size, UInt64.size]; omega)]
    apply Sponge.xor_loop_inv_step _ _ _ _ _ hi inv
    intro k hk
    simp only [USize64.reduceToNat, USize64.size, UInt64.size] at hdiv hmod hdiv2 hmod2
    simp only [Sponge.flat_perm]
    have hpost := hset_post k hk
    rw [hget, hsf, hmod, hdiv, hmod2, hdiv2] at hpost
    have toVec_getD {m : Nat} (v : Vector u64 m) (j : Nat) (hj : j < m) :
        v.toArray.getD j 0 = v[j] := by
      unfold Array.getD
      rw [dif_pos (show j < v.toArray.size by rw [Vector.size_toArray]; exact hj)]
      exact Vector.getElem_toArray _
    have hfp_lt : 5 * (i.toNat % 5) + i.toNat / 5 < 25 := by omega
    rw [toVec_getD _ _ hfp_lt] at hpost
    rw [toVec_getD _ k hk, toVec_getD _ _ hfp_lt, toVec_getD _ _ hi, toVec_getD _ k hk]
    exact hpost
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
  unfold splice_seq
  simp only [Array.toList_append, Array.toList_extract, List.getD_eq_getElem?_getD,
    List.getElem?_append, List.length_append, Array.length_toList,
    List.extract_eq_take_drop, List.length_take, List.length_drop, Nat.sub_zero,
    List.drop_zero, hv, Nat.min_eq_left (show start ≤ s.val.size by omega),
    Nat.min_self, show start + (stop - start) = stop by omega]
  split <;> rename_i hlt
  · -- k < stop
    split <;> rename_i hlt2
    · -- k < start
      simp only [show ¬(start ≤ k ∧ k < stop) from by omega, ite_false,
        List.getElem?_take, if_pos hlt2]
    · -- start ≤ k < stop
      simp only [show (start ≤ k) from by omega, show (k < stop) from hlt,
        true_and, ite_true]
  · -- k ≥ stop
    have hkstop : k - stop < s.val.size - stop := by omega
    simp only [show ¬(start ≤ k ∧ k < stop) from by omega, ite_false,
      List.getElem?_take, hkstop, ite_true,
      List.getElem?_drop, show stop + (k - stop) = k from by omega]

open core_models.ops.range in
@[spec] theorem update_at_range_spec {α : Type}
    (s : RustSlice α) (r : Range usize) (v : RustSlice α)
    (hend : r._end.toNat ≤ s.val.size) (hstart : r.start.toNat ≤ r._end.toNat)
    (hv : v.val.size = r._end.toNat - r.start.toNat) :
    ⦃ ⌜ True ⌝ ⦄
    rust_primitives.hax.monomorphized_update_at.update_at_range s r v
    ⦃ ⇓ res => ⌜ res = splice_seq s r.start.toNat r._end.toNat v hend hstart hv ⌝ ⦄ := by
  intro _
  simp only [rust_primitives.hax.monomorphized_update_at.update_at_range,
    rust_primitives.hax.monomorphized_update_at.UpdateAtRange.doUpdateAtRange,
    rust_primitives.hax.monomorphized_update_at.instUpdateAtRangeSeq]
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
  intro _
  unfold getElemResult RangeTo.instGetElemResultRustArray GetElemResult.getElemResult Range.instGetElemResultRustArrayUSize64
  dsimp only []
  have hle2 : e.toNat ≤ n.toNat := by simp [Vector.size] at he; exact he
  rw [show (decide ((0 : usize) ≤ e) && decide (e.toNat ≤ n.toNat)) = true from by
    simp only [decide_eq_true_eq, Bool.and_eq_true]; exact ⟨Nat.zero_le _, hle2⟩]
  simp

/-! ## store_block proof -/

private theorem toUInt8_mod_256 (x : UInt64) : UInt64.toUInt8 (x % 256) = UInt64.toUInt8 x := by
  have h256 : (256 : UInt64).toNat = 256 := by native_decide
  simp only [UInt64.toUInt8]
  suffices h : (x % 256).toNat % 256 = x.toNat % 256 by
    simp only [Nat.toUInt8, UInt8.ofNat, BitVec.ofNat]
    exact congrArg _ (congrArg _ (Fin.ext h))
  rw [UInt64.toNat_mod, h256]
  exact Nat.mod_mod_of_dvd _ ⟨1, rfl⟩

/-- The k-th byte of a partial lane extraction equals the k-th byte shift.
    Key lemma for the remainder case of store_block. -/
private theorem lane_bytes_extract_getD (x : UInt64) (n k : Nat) (hk : k < n) (hn : n ≤ 8) :
  (#v[UInt64.toUInt8 (x % 256), UInt64.toUInt8 (x >>> 8 % 256), UInt64.toUInt8 (x >>> 16 % 256),
      UInt64.toUInt8 (x >>> 24 % 256), UInt64.toUInt8 (x >>> 32 % 256), UInt64.toUInt8 (x >>> 40 % 256),
      UInt64.toUInt8 (x >>> 48 % 256), UInt64.toUInt8 (x >>> 56 % 256)].extract
    0 n).toArray.toList.getD k (0 : UInt8) =
  UInt64.toUInt8 (x >>> UInt64.ofNat (8 * k)) := by
  -- Reduce Vector.extract to List.take, then strip take via k < n
  simp only [Vector.toArray_extract, Array.toList_extract, List.extract, Nat.sub_zero, List.drop_zero]
  have h_take : (List.take n [UInt64.toUInt8 (x % 256), UInt64.toUInt8 (x >>> 8 % 256),
      UInt64.toUInt8 (x >>> 16 % 256), UInt64.toUInt8 (x >>> 24 % 256),
      UInt64.toUInt8 (x >>> 32 % 256), UInt64.toUInt8 (x >>> 40 % 256),
      UInt64.toUInt8 (x >>> 48 % 256), UInt64.toUInt8 (x >>> 56 % 256)]).getD k (0 : UInt8) =
    [UInt64.toUInt8 (x % 256), UInt64.toUInt8 (x >>> 8 % 256), UInt64.toUInt8 (x >>> 16 % 256),
      UInt64.toUInt8 (x >>> 24 % 256), UInt64.toUInt8 (x >>> 32 % 256), UInt64.toUInt8 (x >>> 40 % 256),
      UInt64.toUInt8 (x >>> 48 % 256), UInt64.toUInt8 (x >>> 56 % 256)].getD k (0 : UInt8) := by
    simp [List.getD_eq_getElem?_getD, hk]
  rw [h_take]
  -- 8-way case split on k, then evaluate getD + apply toUInt8_mod_256
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 from by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [List.getD, toUInt8_mod_256]

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
          Sponge.lane_byte (s.toVec.toArray.getD (Sponge.flat_perm (b / 8)) 0) (b % 8)) ∧
      (∀ b, b < out.val.size → (b < start.toNat ∨ b ≥ start.toNat + len.toNat) →
        r.val.toList.getD b 0 = out.val.toList.getD b 0) ⌝ ⦄ := by
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
      pure (Sponge.store_loop_inv s.toVec out.val.size start.toNat out.val.toList o.val k.toNat))
    (pureInv₂ := ⟨fun o k => Sponge.store_loop_inv s.toVec out.val.size start.toNat out.val.toList o.val k.toNat,
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
    exact ⟨rfl, fun _ h => absurd h (by omega), fun _ _ _ => rfl⟩
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
    have hi25 : i.toNat < 25 := by grind
    rw [USize64.toNat_add_of_lt (by simp [USize64.size, UInt64.size]; omega)]
    obtain ⟨hsize, hspec, hpres⟩ := hinv
    unfold Sponge.store_loop_inv
    refine ⟨by simp [splice_seq, hsize]; grind, ?_, ?_⟩
    · -- Written bytes
      intro b hb
      have hb_lt : start.toNat + b < acc.val.size := by
        rw [hsize]; vc_omega
      have hgetD := splice_seq_getD acc (rpos.toNat) (rend.toNat) rbytes
        (by vc_omega) (by vc_omega) (by subst hbytes hlane; simp; vc_omega)
        (start.toNat + b) hb_lt (0 : u8)
      rw [hgetD]
      split
      · -- New region: start + 8*i ≤ start + b < start + 8*i + 8
        rename_i hcase
        obtain ⟨hlo, hhi⟩ := hcase
        subst hbytes hlane
        simp only [hpos, hend, h8i, hdiv, hmod, USize64.reduceToNat] at *
        have hbi : b / 8 = i.toNat := by omega
        have hbm : b % 8 = b - 8 * i.toNat := by omega
        simp only [Sponge.flat_perm, hbi]
        simp only [Sponge.lane_byte]
        rw [show start.toNat + b - (start.toNat + 8 * i.toNat) = b - 8 * i.toNat from by omega]
        rcases (show b - 8 * i.toNat = 0 ∨ b - 8 * i.toNat = 1 ∨ b - 8 * i.toNat = 2 ∨
          b - 8 * i.toNat = 3 ∨ b - 8 * i.toNat = 4 ∨ b - 8 * i.toNat = 5 ∨
          b - 8 * i.toNat = 6 ∨ b - 8 * i.toNat = 7 from by omega) with
          h | h | h | h | h | h | h | h <;> simp_all [toUInt8_mod_256]
      · -- Old region: b < 8*i
        rename_i hold
        simp only [hpos, hend, hend2, h8i, USize64.reduceToNat] at *
        have hbi : b < 8 * i.toNat := by omega
        exact hspec b hbi
    · -- Preservation: bytes outside [start, start + 8*(i+1)) unchanged from orig_out
      intro b hb_out hb_range
      have hb_lt : b < acc.val.size := by rw [hsize]; exact hb_out
      have hgetD := splice_seq_getD acc (rpos.toNat) (rend.toNat) rbytes
        (by vc_omega) (by vc_omega) (by subst hbytes hlane; simp; vc_omega)
        b hb_lt (0 : u8)
      rw [hgetD]
      split
      · -- b in splice region [start+8*i, start+8*i+8) — contradicts hb_range
        rename_i hcase
        obtain ⟨hlo, hhi⟩ := hcase
        simp only [hpos, hend, h8i, USize64.reduceToNat] at *
        exfalso; omega
      · -- b outside splice — use IH
        rename_i hout_splice
        simp only [hpos, hend, hend2, h8i, USize64.reduceToNat] at *
        apply hpres b hb_out
        rcases hb_range with hlt | hge
        · left; exact hlt
        · right; omega
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
    obtain ⟨hsize, hspec, hpres⟩ := hinv
    -- Derive key arithmetic facts
    have hrem_pos : rem.toNat > 0 := by grind
    have hrem_le8 : rem.toNat ≤ 8 := by grind
    have hlen_eq : len.toNat = 8 * nfull.toNat + rem.toNat := by grind
    refine ⟨by simp [splice_seq, hsize]; grind, ?_, ?_⟩
    · -- Written bytes
      intro b hb
      have hb_lt : start.toNat + b < loop_out.val.size := by rw [hsize]; vc_omega
      have hgetD := splice_seq_getD loop_out (rsub.toNat) (rpos.toNat) rcopy
        (by vc_omega) (by vc_omega) (by simp [hbytes, hlane, hslice, Array.size_extract, Vector.size_toArray]; vc_omega)
        (start.toNat + b) hb_lt (0 : u8)
      rw [hgetD]
      split
      · -- New region: in the remainder splice [start+8*nfull, start+len)
        rename_i hcase
        obtain ⟨hlo, hhi⟩ := hcase
        simp only [hbytes, hlane, hslice, hsub, hend, hpos, hdiv, hmod, hrem, hnfull, USize64.reduceToNat] at *
        have hbi : b / 8 = len.toNat / 8 := by omega
        simp only [Sponge.flat_perm, hbi, Sponge.lane_byte]
        rw [show start.toNat + b - (start.toNat + len.toNat - len.toNat % 8) =
          b - 8 * (len.toNat / 8) from by omega]
        have hbmod : b - 8 * (len.toNat / 8) = b % 8 := by omega
        rw [hbmod]
        exact lane_bytes_extract_getD _ _ _ (by grind) (by grind)
      · -- Old region: b < 8*nfull (outside splice range)
        rename_i hold
        simp only [hsub, hend, hpos, hrem, hnfull, USize64.reduceToNat] at *
        have hbi : b < 8 * (len.toNat / 8) := by omega
        exact hspec b hbi
    · -- Preservation: bytes outside [start, start+len) unchanged
      intro b hb_out hb_range
      have hb_lt : b < loop_out.val.size := by rw [hsize]; exact hb_out
      have hgetD := splice_seq_getD loop_out (rsub.toNat) (rpos.toNat) rcopy
        (by vc_omega) (by vc_omega) (by simp [hbytes, hlane, hslice, Array.size_extract, Vector.size_toArray]; vc_omega)
        b hb_lt (0 : u8)
      rw [hgetD]
      split
      · -- b in remainder splice — contradicts hb_range
        rename_i hcase
        obtain ⟨hlo, hhi⟩ := hcase
        simp only [hsub, hend, hpos, hrem, hnfull, USize64.reduceToNat] at *
        exfalso; omega
      · -- b outside splice — use IH from loop
        rename_i hout_splice
        simp only [hsub, hend, hpos, hrem, hnfull, USize64.reduceToNat] at *
        apply hpres b hb_out
        rcases hb_range with hlt | hge
        · left; exact hlt
        · right; omega
  -- vc36: composition (without remainder, len % 8 = 0)
  · rename_i _ nfull hnfull loop_out hinv rem hrem rdec hdec_false hdec_eq
    simp only [USize64.reduceToNat, decide_eq_true_eq] at *
    obtain ⟨hsize, hspec, hpres⟩ := hinv
    exact ⟨hsize, fun b hb => hspec b (by grind), fun b hb hr => hpres b hb (by grind)⟩

-- store_block_preserves removed — subsumed by strengthened store_block_spec
-- load_last
attribute [local irreducible] libcrux_sha3.simd.portable.load_last

set_option maxHeartbeats 3200000 in
@[spec] theorem load_last_spec (RATE : usize) (DELIM : u8)
    (state : RustArray u64 25) (blocks : RustSlice u8)
    (start : usize) (len : usize)
    (hrate : RATE.toNat % 8 = 0)
    (hlen : start.toNat + len.toNat ≤ blocks.val.size)
    (hlen_rate : len.toNat < RATE.toNat)
    (hrate_le : RATE.toNat ≤ 200) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_sha3.simd.portable.load_last RATE DELIM state blocks start len
    ⦃ ⇓ r => ⌜ r.toVec = Sponge.load_last_pure RATE.toNat DELIM state.toVec
        blocks.val.toList start.toNat len.toNat ⌝ ⦄ := by
  intro _
  unfold libcrux_sha3.simd.portable.load_last
  simp only [← copy_from_slice_u8_eq]
  hax_mvcgen [-libcrux_sha3.simd.portable.load_block.spec.contract]
  all_goals (try vc_omega)
  all_goals (try grind)
  all_goals (try (have := blocks.size_lt_usizeSize; omega))
  all_goals (try (simp only [Vector.size, Vector.size_toArray]; omega))
  all_goals (try (subst_vars; simp only [Array.size_extract, Vector.size_toArray,
    Vector.extract, Vector.replicate, Nat.min_eq_left (by omega : len.toNat ≤ RATE.toNat)] at *; omega))
  all_goals (try (exfalso; simp only [splice_seq, Vector.size, Array.size_append,
    Array.size_extract, Vector.replicate, Vector.size_toArray,
    Nat.min_eq_left (by omega : len.toNat ≤ RATE.toNat)] at *; omega))
  -- vc15: RATE ≤ 200 (from load_block_spec precondition)
  all_goals (try exact hrate_le)
  -- vc17: composition — load_block on padded buffer = load_last_pure
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
  hax_mvcgen [-libcrux_sha3.simd.portable.load_block.spec.contract]
  all_goals (try vc_omega)
  all_goals (try grind)
  all_goals (try (simp_all; omega))
  all_goals (try rfl)
  all_goals (try (simp_all [Sponge.absorb_block_pure]; rfl))

-- absorb_final = Absorb.load_last + keccakf1600
attribute [local irreducible] Impl_2.absorb_final

set_option maxHeartbeats 800000 in
@[spec] theorem absorb_final_spec (RATE : usize) (DELIM : u8)
    (st : KeccakState 1 u64) (input : RustArray (RustSlice u8) 1)
    (start : usize) (len : usize)
    (hrate : RATE.toNat % 8 = 0)
    (hlen : len.toNat < RATE.toNat)
    (hbounds : start.toNat + len.toNat ≤ (input.toVec[(0 : Fin 1)]).val.size)
    (hrate_le : RATE.toNat ≤ 200) :
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
  hax_mvcgen [-libcrux_sha3.simd.portable.load_last.spec.contract]
  all_goals (try vc_omega)
  all_goals (try grind)
  all_goals (try (simp_all; omega))
  all_goals (try exact hrate_le)
  all_goals (try rfl)
  all_goals (try (simp_all [Sponge.absorb_final_pure]; rfl))

/-! ## Wrappers for keccak1: unwrap RustArray.ofVec #v[input] (Pattern 2) -/

-- keccak1 wraps the single input into RustArray.ofVec #v[input] before passing to
-- absorb_block/absorb_final. These wrappers take RustSlice u8 directly so that
-- mvcgen VCs reference input.val.toList instead of #v[input][0].val.toList.

private def k1_absorb_block (RATE : usize) (st : KeccakState 1 u64)
    (input : RustSlice u8) (start : usize) :=
  Impl_2.absorb_block 1 u64 RATE st (RustArray.ofVec #v[input]) start

private theorem k1_absorb_block_eq (RATE : usize) (st : KeccakState 1 u64)
    (input : RustSlice u8) (start : usize) :
    Impl_2.absorb_block 1 u64 RATE st (RustArray.ofVec #v[input]) start =
    k1_absorb_block RATE st input start := rfl

@[spec] private theorem k1_absorb_block_spec (RATE : usize) (st : KeccakState 1 u64)
    (input : RustSlice u8) (start : usize)
    (hrate : RATE.toNat % 8 = 0)
    (hrate_le : RATE.toNat ≤ 200)
    (hbounds : start.toNat + RATE.toNat ≤ input.val.size) :
    ⦃ ⌜ True ⌝ ⦄
    k1_absorb_block RATE st input start
    ⦃ ⇓ r => ⌜ r.st.toVec = Sponge.absorb_block_pure RATE.toNat st.st.toVec
        input.val.toList start.toNat ⌝ ⦄ :=
  absorb_block_spec RATE st (RustArray.ofVec #v[input]) start hrate hrate_le hbounds

attribute [irreducible] k1_absorb_block

private def k1_absorb_final (RATE : usize) (DELIM : u8) (st : KeccakState 1 u64)
    (input : RustSlice u8) (start : usize) (len : usize) :=
  Impl_2.absorb_final 1 u64 RATE DELIM st (RustArray.ofVec #v[input]) start len

private theorem k1_absorb_final_eq (RATE : usize) (DELIM : u8) (st : KeccakState 1 u64)
    (input : RustSlice u8) (start : usize) (len : usize) :
    Impl_2.absorb_final 1 u64 RATE DELIM st (RustArray.ofVec #v[input]) start len =
    k1_absorb_final RATE DELIM st input start len := rfl

@[spec] private theorem k1_absorb_final_spec (RATE : usize) (DELIM : u8)
    (st : KeccakState 1 u64) (input : RustSlice u8)
    (start : usize) (len : usize)
    (hrate : RATE.toNat % 8 = 0)
    (hlen : len.toNat < RATE.toNat)
    (hbounds : start.toNat + len.toNat ≤ input.val.size)
    (hrate_le : RATE.toNat ≤ 200) :
    ⦃ ⌜ True ⌝ ⦄
    k1_absorb_final RATE DELIM st input start len
    ⦃ ⇓ r => ⌜ r.st.toVec = Sponge.absorb_final_pure RATE.toNat DELIM st.st.toVec
        input.val.toList start.toNat len.toNat ⌝ ⦄ :=
  absorb_final_spec RATE DELIM st (RustArray.ofVec #v[input]) start len hrate hlen hbounds hrate_le

attribute [irreducible] k1_absorb_final

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
    ⦃ ⇓ r => ⌜ r.val.size = out.val.size ∧
      (∀ b, b < len.toNat →
        r.val.toList.getD (start.toNat + b) 0 =
          Sponge.lane_byte (st.st.toVec.toArray.getD (Sponge.flat_perm (b / 8)) 0) (b % 8)) ∧
      (∀ b, b < out.val.size → (b < start.toNat ∨ b ≥ start.toNat + len.toNat) →
        r.val.toList.getD b 0 = out.val.toList.getD b 0) ⌝ ⦄ := by
  intro _
  unfold libcrux_sha3.traits.Squeeze.squeeze
  simp only [libcrux_sha3.simd.portable.Impl_2]
  simp only [Std.Do.WPMonad.wp_bind, Std.Do.WPMonad.wp_pure, bind_pure]
  exact store_block_spec RATE st.st out start len hrate_le hlen hout trivial

-- squeeze_preserves removed — subsumed by strengthened squeeze_spec

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

/-! ## keccak1 -/

attribute [local irreducible] libcrux_sha3.generic_keccak.portable.keccak1

-- Helper: element-wise getD agreement + equal length → list equality
private theorem list_eq_of_getD {l₁ l₂ : List u8}
    (h_len : l₁.length = l₂.length)
    (h_elem : ∀ i, i < l₁.length → l₁.getD i 0 = l₂.getD i 0) :
    l₁ = l₂ := by
  apply List.ext_getElem h_len
  intro n h1 h2
  have := h_elem n h1
  simp only [List.getD] at this
  rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at this
  simpa using this

-- Helper: store_block_pure length
private theorem store_block_pure_length (RATE : Nat) (state : Vector u64 25) (start len : Nat) :
    (Sponge.store_block_pure RATE state start len).length = len := by
  simp [Sponge.store_block_pure]

-- Helper: store_block_pure getD
private theorem store_block_pure_getD (RATE : Nat) (state : Vector u64 25) (start len : Nat)
    (b : Nat) (hb : b < len) :
    (Sponge.store_block_pure RATE state start len).getD b 0 =
    Sponge.lane_byte (state.toArray.getD (Sponge.flat_perm (b / 8)) 0) (b % 8) := by
  simp only [Sponge.store_block_pure, List.getD]
  rw [List.getElem?_eq_getElem (by simp; omega)]
  simp [List.getElem_map, hb]

-- Helper: USize64 loop bound implies add-one fits
private theorem usize_add_lt {i n : USize64} (_ : i.toNat < n.toNat) :
    i.toNat + (1 : USize64).toNat < 2 ^ 64 := by
  have : n.toNat < 2 ^ 64 := n.toBitVec.isLt
  simp only [USize64.reduceToNat] at *; omega

-- Helper: RATE ≠ 0 from 0 < RATE.toNat
private theorem rate_ne_zero {RATE : usize} (h : 0 < RATE.toNat) : RATE ≠ 0 := by
  intro heq; subst heq; simp [USize64.reduceToNat] at h

-- Helper: subOverflow is false when b ≤ a (Nat level)
private theorem sub_no_overflow {a b : usize}
    (h : b.toNat ≤ a.toNat) : ¬USize64.subOverflow a b = true := by
  simp only [USize64.subOverflow, Bool.not_eq_true]
  rw [BitVec.usubOverflow_eq, decide_eq_false_iff_not]
  intro hlt; simp [BitVec.lt_def, USize64.toNat_toBitVec] at hlt; omega

-- Nonlinear bridge: i * RATE < USize64.size from loop bound chain
private theorem mul_lt_size_from_loop {i blocks n RATE : Nat}
    (h_loop : i < blocks) (h_blocks : blocks = n / RATE) (h_size : n < USize64.size) :
    i * RATE < USize64.size := by
  have h1 : (i + 1) * RATE ≤ (n / RATE) * RATE := Nat.mul_le_mul_right RATE (by omega)
  have h2 : (n / RATE) * RATE ≤ n := Nat.div_mul_le_self n RATE
  have h3 : i * RATE + RATE = (i + 1) * RATE := by rw [Nat.add_mul]; simp
  omega

-- Nonlinear bridge: i * RATE + RATE ≤ n from loop bound chain
private theorem mul_add_le_from_loop {i blocks n RATE : Nat}
    (h_loop : i < blocks) (h_blocks : blocks = n / RATE) :
    i * RATE + RATE ≤ n := by
  have h1 : (i + 1) * RATE ≤ (n / RATE) * RATE := Nat.mul_le_mul_right RATE (by omega)
  have h2 : (n / RATE) * RATE ≤ n := Nat.div_mul_le_self n RATE
  have h3 : i * RATE + RATE = (i + 1) * RATE := by rw [Nat.add_mul]; simp
  omega

-- Bridge: division result ≥ 1 implies divisor ≤ dividend
private theorem le_of_div_pos {a b : Nat} (_ : 0 < b) (h : 0 < a / b) : b ≤ a := by
  have h1 : 1 * b ≤ (a / b) * b := Nat.mul_le_mul_right b h
  have h2 : (a / b) * b ≤ a := Nat.div_mul_le_self a b
  omega

-- Bridge: Nat.repeat keccak_f_pure shift (used outside Sponge namespace)
private theorem repeat_kf_shift' (m : Nat) (s : Vector u64 25) :
    Nat.repeat keccak_f_pure m (keccak_f_pure s) = Nat.repeat keccak_f_pure (m + 1) s := by
  induction m with | zero => rfl | succ n ih => simp [Nat.repeat, ih]

-- Bridge: division = 0 implies dividend < divisor
private theorem lt_of_div_zero {a b : Nat} (hb : 0 < b) (h : a / b = 0) : a < b := by
  have h1 := Nat.div_add_mod a b; rw [h] at h1
  have h2 := Nat.mod_lt a hb; omega

-- Squeeze loop invariant decoder (beq form, before normalization)
private theorem squeeze_inv_size (acc : RustSlice u8) (r : USize64)
    (h_inv : (USize64.ofNat acc.val.size == r) = true) (h_r : r.toNat = n) :
    acc.val.size = n := by
  simp [beq_iff_eq] at h_inv
  have h : (USize64.ofNat acc.val.size).toNat = r.toNat := by rw [h_inv]
  simp [USize64.toNat_ofNat'] at h
  have := acc.size_lt_usizeSize; have : USize64.size = 2 ^ 64 := rfl; omega

-- Squeeze loop invariant decoder (equality form, after beq normalization)
private theorem squeeze_inv_size' (acc : RustSlice u8) (r : USize64)
    (h_inv : USize64.ofNat acc.val.size = r) (h_r : r.toNat = n) :
    acc.val.size = n := by
  have h : (USize64.ofNat acc.val.size).toNat = r.toNat := by rw [h_inv]
  simp [USize64.toNat_ofNat'] at h
  have := acc.size_lt_usizeSize; have : USize64.size = 2 ^ 64 := rfl; omega

-- Helper: #v[a][0] = a for normalizing 1-element vector access (USize64 size parameter)
-- simp matches Fin up to proof irrelevance, so this works even when the Fin proof differs
@[simp] private theorem vec_single_getElem {α : Type} (a : α) (i : Fin (USize64.toNat 1)) :
    (#v[a] : Vector α (USize64.toNat 1))[i] = a := by
  have h : i = ⟨0, by simp [USize64.reduceToNat]⟩ := by ext; simp [USize64.reduceToNat] at *
  subst h; rfl

-- Helper: subOverflow is false when b = a % RATE
private theorem sub_no_overflow_mod {a b RATE : usize}
    (h : b.toNat = a.toNat % RATE.toNat) : ¬USize64.subOverflow a b = true :=
  sub_no_overflow (by have := Nat.mod_le a.toNat RATE.toNat; omega)

-- Helper: b < RATE when b = a % RATE and RATE > 0
private theorem mod_lt_of_eq {a b RATE : usize} (hR : 0 < RATE.toNat)
    (h : b.toNat = a.toNat % RATE.toNat) : b.toNat < RATE.toNat := by
  have := Nat.mod_lt a.toNat hR; omega

-- Squeeze loop invariant: tracks size, state, and byte correctness
private def squeeze_loop_inv (RATE : usize) (DELIM : u8) (input output : RustSlice u8)
    (pair : rust_primitives.hax.Tuple2 (RustSlice u8) (KeccakState 1 u64)) (k : USize64) : Prop :=
  pair._0.val.size = output.val.size ∧
  pair._1.st.toVec = Nat.repeat keccak_f_pure (k.toNat - 1)
    (Sponge.keccak1_absorb_state RATE.toNat DELIM input.val.toList) ∧
  ∀ b, b < k.toNat * RATE.toNat → b < output.val.size →
    pair._0.val.toList.getD b 0 =
    (Sponge.keccak1_pure RATE.toNat DELIM input.val.toList output.val.size).getD b 0

set_option maxHeartbeats 6400000 in
theorem keccak1_spec (RATE : usize) (DELIM : u8)
    (input output : RustSlice u8)
    (hrate : RATE.toNat % 8 = 0)
    (hrate_pos : 0 < RATE.toNat)
    (hrate_le : RATE.toNat ≤ 200) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_sha3.generic_keccak.portable.keccak1 RATE DELIM input output
    ⦃ ⇓ r => ⌜ r.val.toList = Sponge.keccak1_pure RATE.toNat DELIM
        input.val.toList output.val.size ⌝ ⦄ := by
  intro _
  unfold libcrux_sha3.generic_keccak.portable.keccak1
  -- Replace RustArray.ofVec #v[input] calls with k1_ wrappers (Pattern 2)
  -- This ensures VCs reference input.val.toList instead of #v[input][0].val.toList
  simp only [k1_absorb_block_eq, k1_absorb_final_eq]
  -- Swap absorb loop invariant from True to real invariant (Pattern 5)
  simp only [fold_range_inv_irrelevant (α := KeccakState 1 u64)
    (inv₂ := fun (st : KeccakState 1 u64) (k : USize64) =>
      pure (st.st.toVec = Sponge.absorb_all_pure RATE.toNat
        (Vector.replicate 25 0) input.val.toList k.toNat))
    (pureInv₂ := ⟨fun (st : KeccakState 1 u64) (k : USize64) =>
      st.st.toVec = Sponge.absorb_all_pure RATE.toNat
        (Vector.replicate 25 0) input.val.toList k.toNat,
      fun _ _ => by intro _; rfl⟩)]
  -- Swap squeeze loop invariant from True to real invariant (Pattern 5)
  simp only [fold_range_inv_irrelevant
    (α := rust_primitives.hax.Tuple2 (RustSlice u8) (KeccakState 1 u64))
    (inv₂ := fun (pair : rust_primitives.hax.Tuple2 (RustSlice u8)
        (KeccakState 1 u64)) (k : USize64) =>
      pure (squeeze_loop_inv RATE DELIM input output pair k))
    (pureInv₂ := ⟨fun (pair : rust_primitives.hax.Tuple2 (RustSlice u8)
        (KeccakState 1 u64)) (k : USize64) =>
      squeeze_loop_inv RATE DELIM input output pair k,
      fun _ _ => by intro _; rfl⟩)]
  hax_mvcgen [-libcrux_sha3.generic_keccak.Impl_2.absorb_block.spec.contract,
    -libcrux_sha3.generic_keccak.Impl_2.absorb_final.spec.contract]
  -- Phase 0: Normalize USize64 literals, decode Bool branches, normalize beq/bne
  all_goals (try (simp only [USize64.reduceToNat, Bool.not_eq_true'] at *))
  all_goals (try subst_eqs)
  all_goals (try (simp only [beq_iff_eq, bne_iff_ne, Bool.true_eq, Bool.false_eq,
      decide_eq_true_eq, decide_eq_false_iff_not] at *))
  -- Phase 1: Easy VCs (vc_omega, grind, trivial, constants)
  all_goals (try vc_omega)
  all_goals (try grind)
  all_goals (try trivial)
  all_goals (try exact rate_ne_zero hrate_pos)
  all_goals (try exact hrate_le)
  -- Phase 2: loop overflow VCs
  all_goals (try exact mul_lt_size_from_loop ‹_› ‹_› (by (have := input.size_lt_usizeSize; have := output.size_lt_usizeSize; omega)))
  -- Phase 3: Simple arithmetic
  all_goals (try omega)
  -- Phase 3a: mul_add_le bridge (vc8)
  all_goals (try (have := mul_add_le_from_loop ‹_› ‹_›; omega))
  -- Phase 3b: mod_lt (needs % intact, before mod_def) (vc12, vc32)
  all_goals (try (have := mod_lt_of_eq hrate_pos ‹_›; omega))
  -- Phase 3c: subOverflow from mod (vc10, vc31)
  all_goals (try (exact sub_no_overflow_mod ‹_›))
  -- Phase 3d: mod_def + omega for remaining mod/sub goals (vc13, vc34)
  all_goals (try (simp only [Nat.mod_def] at *; omega))
  -- Phase 4: absorb loop base case (vc4.hinit)
  all_goals (try (rw [Sponge.absorb_all_pure_zero]; exact new_state_is_replicate ‹_›))
  -- Phase 5: subOverflow from mod
  all_goals (try (exact sub_no_overflow_mod ‹_›))
  -- Remaining VCs: explicit case analysis
  case vc9.hstep.success.success.success =>
    -- Absorb step: invariant at i → invariant at i+1
    rw [USize64.toNat_add_of_lt (usize_add_lt ‹_›)]
    simp only [USize64.reduceToNat]
    rw [Sponge.absorb_all_pure_succ]; simp_all
  case vc17.hlen =>
    -- Output ≤ RATE when output_blocks = 0
    apply Nat.le_of_lt; apply lt_of_div_zero hrate_pos; omega
  case vc23.hout =>
    -- RATE ≤ output when output_blocks ≠ 0
    have h := ‹_ = output.val.size›
    simp only [Nat.zero_add, ← h]
    apply le_of_div_pos hrate_pos; omega
  case vc25.hinit =>
    -- Squeeze loop init: establish invariant at k=1
    unfold squeeze_loop_inv
    obtain ⟨hsize, helems, _⟩ := ‹_ ∧ _ ∧ _›
    simp only [Nat.zero_add] at helems
    have hstate := absorb_state_connection hrate_pos
      (show _ = input.val.size from ‹_›) ‹_› ‹_› ‹_› ‹_› ‹_›
    simp only [USize64.reduceToNat, Nat.sub_self, Nat.one_mul, Nat.repeat]
    refine ⟨hsize, hstate.symm, ?_⟩
    intro b hb_rate hb_out
    have h_elem := helems b hb_rate
    symm
    rw [Sponge.keccak1_pure_eq_squeeze _ _ _ _ hrate_pos, hstate,
        Sponge.squeeze_pure_getD _ _ _ hrate_pos b hb_out,
        show b / USize64.toNat RATE = 0 from Nat.div_eq_of_lt hb_rate,
        show b % USize64.toNat RATE = b from Nat.mod_eq_of_lt hb_rate]
    simp only [Nat.repeat]
    exact h_elem.symm
  case vc29.hout =>
    -- Squeeze loop: offset + RATE ≤ output_size
    have h_inv := ‹squeeze_loop_inv RATE DELIM input output _ _›
    unfold squeeze_loop_inv at h_inv
    obtain ⟨hsize, _, _⟩ := h_inv
    have := mul_add_le_from_loop ‹_› ‹_›; omega
  case vc30.hstep.success.success.success.success =>
    -- Squeeze loop step: invariant at i → invariant at i+1
    -- Extract loop invariant from hypothesis
    have h_inv := ‹squeeze_loop_inv RATE DELIM input output _ _›
    unfold squeeze_loop_inv at h_inv
    obtain ⟨h_size, h_state, h_bytes⟩ := h_inv
    -- Extract keccak_f step and offset
    have hkf : _ = keccak_f_pure _ := ‹_›
    have h_offset : (_ : USize64).toNat = (_ : USize64).toNat * USize64.toNat RATE := ‹_›
    -- Extract squeeze result triple
    obtain ⟨h_new_size, h_new_bytes, h_pres⟩ := ‹_ ∧ (∀ b, b < USize64.toNat RATE →
      _ = Sponge.lane_byte _ _) ∧ _›
    -- Name the offset bound (= i * RATE) using Exists packing
    obtain ⟨off, h_bytes_off, h_off_eq⟩ :
        ∃ n, (∀ b, b < n → b < output.val.size →
          (_ : RustSlice u8).val.toList.getD b 0 =
          (Sponge.keccak1_pure (USize64.toNat RATE) DELIM
            input.val.toList output.val.size).getD b 0) ∧
        (_ : USize64).toNat = n := ⟨_, h_bytes, h_offset⟩
    -- Derive off = i * RATE (connects off to loop index)
    have h_off_val := h_off_eq.symm.trans h_offset
    -- h_off_val : off = i✝.toNat * USize64.toNat RATE
    -- Rewrite h_pres and h_new_bytes to use `off` instead of USize64.toNat r✝¹
    rw [h_off_eq] at h_pres h_new_bytes
    -- Linearize hb: rewrite (i+1)*RATE to off + RATE using h_off_val
    -- Unfold goal and normalize (i+1)
    unfold squeeze_loop_inv
    rw [USize64.toNat_add_of_lt (usize_add_lt ‹_›)]
    simp only [USize64.reduceToNat, Nat.add_sub_cancel]
    -- Linearize the (i+1)*RATE in the goal to off + RATE for omega accessibility
    have h_bound : ∀ n, n < (_ + 1) * USize64.toNat RATE → n < off + USize64.toNat RATE := by
      intro n hn; rw [Nat.add_mul] at hn; simp only [Nat.one_mul] at hn; omega
    refine ⟨by omega, ?_, ?_⟩
    · -- State: r✝².st.toVec = Nat.repeat keccak_f_pure i✝.toNat absorb_state
      rw [hkf, h_state]; symm
      show Nat.repeat _ ((_ - 1) + 1) _ = Nat.repeat _ _ _
      congr 1; omega
    · -- Bytes: ∀ b < (i+1)*RATE → b < out.size → r.getD b = keccak1_pure.getD b
      intro b hb hb_out
      have hb_lin := h_bound b hb
      rcases Nat.lt_or_ge b off with hb_old | hb_new
      · -- Old byte: preserved from acc by h_pres, matches keccak1_pure by IH
        have h1 := h_pres b (by omega) (Or.inl hb_old)
        rw [h1]
        exact h_bytes_off b hb_old hb_out
      · -- New byte: written by squeeze at offset off (= i*RATE)
        have hb_new_lt : b - off < USize64.toNat RATE := by omega
        have h1 := h_new_bytes (b - off) hb_new_lt
        rw [show off + (b - off) = b from by omega] at h1
        rw [h1]
        -- Connect lane_byte to keccak1_pure via squeeze_pure_getD
        symm
        rw [Sponge.keccak1_pure_eq_squeeze _ _ _ _ hrate_pos]
        have habsorb := absorb_state_connection hrate_pos
          (show _ = input.val.size from ‹_›) ‹_› ‹_› ‹_› ‹_› ‹_›
        rw [habsorb]
        rw [Sponge.squeeze_pure_getD _ _ _ hrate_pos b hb_out]
        -- b / RATE = off / RATE (since off ≤ b < off + RATE)
        have h_bdiv : b / USize64.toNat RATE = off / USize64.toNat RATE := by
          have h1 : off / USize64.toNat RATE ≤ b / USize64.toNat RATE :=
            Nat.div_le_div_right hb_new
          have h2 : b / USize64.toNat RATE < off / USize64.toNat RATE + 1 :=
            Nat.div_lt_iff_lt_mul hrate_pos |>.mpr (by
              rw [h_off_val, Nat.mul_div_cancel _ hrate_pos, Nat.add_mul]
              simp only [Nat.one_mul]; omega)
          omega
        -- b % RATE = b - off (since off = i * RATE and b / RATE = i)
        have h_bmod : b % USize64.toNat RATE = b - off := by
          rw [Nat.mod_def, h_bdiv, h_off_val, Nat.mul_div_cancel _ hrate_pos, Nat.mul_comm]
        rw [h_bmod]
        congr 1
        · -- State equality: Nat.repeat (off/RATE) absorb_state = r✝².st.toVec
          rw [h_off_val, Nat.mul_div_cancel _ hrate_pos, hkf, h_state]
          symm
          show Nat.repeat _ ((_ - 1) + 1) _ = Nat.repeat _ _ _
          congr 1; omega
  case vc34.hout =>
    -- Remainder: start + rem ≤ output_size
    have h_inv := ‹squeeze_loop_inv RATE DELIM input output _ _›
    unfold squeeze_loop_inv at h_inv
    obtain ⟨hsize, _, _⟩ := h_inv
    simp only [Nat.mod_def] at *; omega
  case vc35.success.success.success.success.success.success.success.success.success.success.success.isFalse.success.success.success.isTrue.success.success.success =>
    -- Composition with remainder: final squeeze after loop
    sorry
  case vc36.success.success.success.success.success.success.success.success.success.success.success.isFalse.success.success.success.isFalse =>
    -- Composition without remainder: squeeze loop covered all bytes
    have h_osize_eq : _ = output.val.size := ‹_›
    simp only [h_osize_eq] at *
    have h_rem0 : output.val.size % USize64.toNat RATE = 0 := by omega
    have h_dm := Nat.div_add_mod output.val.size (USize64.toNat RATE)
    have h_inv := ‹squeeze_loop_inv RATE DELIM input output _ _›
    unfold squeeze_loop_inv at h_inv
    obtain ⟨h_size, _, h_bytes⟩ := h_inv
    apply list_eq_of_getD
    · rw [Array.length_toList, h_size, Sponge.keccak1_pure_length _ _ _ _ hrate_pos]
    · intro i hi
      rw [Array.length_toList, h_size] at hi
      apply h_bytes
      · have h_oblocks := ‹_ = output.val.size / USize64.toNat RATE›
        have h_dvd : USize64.toNat RATE ∣ output.val.size :=
          Nat.dvd_of_mod_eq_zero h_rem0
        rw [h_oblocks, Nat.div_mul_cancel h_dvd]; exact hi
      · exact hi
  case vc20.success.success.success.success.success.success.success.success.success.success.success.isTrue.success =>
    -- Single squeeze (output_blocks = 0): all bytes fit in one RATE block
    -- Normalize output size variable
    have h_osize_eq : _ = output.val.size := ‹_›
    simp only [h_osize_eq] at *
    obtain ⟨hsize, helems, _⟩ := ‹_ ∧ _ ∧ _›
    simp only [Nat.zero_add] at helems
    have hle : output.val.size ≤ USize64.toNat RATE := by
      apply Nat.le_of_lt; apply lt_of_div_zero hrate_pos; omega
    have hstate := absorb_state_connection hrate_pos
      (show _ = input.val.size from ‹_›) ‹_› ‹_› ‹_› ‹_› ‹_›
    rw [Sponge.keccak1_pure_eq_squeeze _ _ _ _ hrate_pos, hstate,
        Sponge.squeeze_pure_le_rate _ _ _ hrate_pos hle]
    unfold Sponge.store_block_pure
    apply list_eq_map_range_of_getD
    · rw [Array.length_toList]; exact hsize
    · intro b hb; exact helems b (by omega)
