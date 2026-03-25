
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import extraction.helpers
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace hacspec_sha3.keccak_f

--  Keccak-f[1600] state: 5×5 lanes of 64-bit words.
--  Keccak state type, exposed for cross-crate verification.
abbrev State : Type := (RustArray u64 25)

--  Read lane `A[x, y]`.
def get (state : (RustArray u64 25)) (x : usize) (y : usize) : RustM u64 := do
  state[(← ((← ((5 : usize) *? x)) +? y))]_?

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def get.spec (state : (RustArray u64 25)) (x : usize) (y : usize) :
    Spec
      (requires := do ((← (x <? (5 : usize))) &&? (← (y <? (5 : usize)))))
      (ensures := fun _ => pure True)
      (get (state : (RustArray u64 25)) (x : usize) (y : usize)) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [get] <;> sorry
}

--  Round constants `RC[ir]` for `ir = 0..23` — FIPS 202, Algorithm 5.
def ROUND_CONSTANTS : (RustArray u64 24) :=
  RustM.of_isOk
    (do
    (pure (RustArray.ofVec #v[(1 : u64),
                                (32898 : u64),
                                (9223372036854808714 : u64),
                                (9223372039002292224 : u64),
                                (32907 : u64),
                                (2147483649 : u64),
                                (9223372039002292353 : u64),
                                (9223372036854808585 : u64),
                                (138 : u64),
                                (136 : u64),
                                (2147516425 : u64),
                                (2147483658 : u64),
                                (2147516555 : u64),
                                (9223372036854775947 : u64),
                                (9223372036854808713 : u64),
                                (9223372036854808579 : u64),
                                (9223372036854808578 : u64),
                                (9223372036854775936 : u64),
                                (32778 : u64),
                                (9223372039002259466 : u64),
                                (9223372039002292353 : u64),
                                (9223372036854808704 : u64),
                                (2147483649 : u64),
                                (9223372039002292232 : u64)])))
    (by rfl)

--  Rotation offsets for ρ step — FIPS 202, Algorithm 2 / Table 2.
--
--  Indexed as `RHO_OFFSETS[5*x + y]`.
def RHO_OFFSETS : (RustArray u32 25) :=
  RustM.of_isOk
    (do
    (pure (RustArray.ofVec #v[(0 : u32),
                                (36 : u32),
                                (3 : u32),
                                (41 : u32),
                                (18 : u32),
                                (1 : u32),
                                (44 : u32),
                                (10 : u32),
                                (45 : u32),
                                (2 : u32),
                                (62 : u32),
                                (6 : u32),
                                (43 : u32),
                                (15 : u32),
                                (61 : u32),
                                (28 : u32),
                                (55 : u32),
                                (25 : u32),
                                (21 : u32),
                                (56 : u32),
                                (27 : u32),
                                (20 : u32),
                                (39 : u32),
                                (8 : u32),
                                (14 : u32)])))
    (by rfl)

--  ι step — FIPS 202, Algorithm 6.
--
--    A′[0,0] = A[0,0] ⊕ RC[ir]
def iota (state : (RustArray u64 25)) (round : usize) :
    RustM (RustArray u64 25) := do
  let state : (RustArray u64 25) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      state
      (0 : usize)
      (← ((← state[(0 : usize)]_?) ^^^? (← ROUND_CONSTANTS[round]_?))));
  (pure state)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def iota.spec (state : (RustArray u64 25)) (round : usize) :
    Spec
      (requires := do (round <? (24 : usize)))
      (ensures := fun _ => pure True)
      (iota (state : (RustArray u64 25)) (round : usize)) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [iota] <;> sorry
}

end hacspec_sha3.keccak_f


namespace hacspec_sha3.sha3

def SHA3_224_RATE : usize := (144 : usize)

def SHA3_256_RATE : usize := (136 : usize)

def SHA3_384_RATE : usize := (104 : usize)

def SHA3_512_RATE : usize := (72 : usize)

def SHAKE128_RATE : usize := (168 : usize)

def SHAKE256_RATE : usize := (136 : usize)

--  SHA-3 domain separation byte (0x06 = 0b0110: two-bit suffix "01" + first bit of pad10*1).
def SHA3_DELIM : u8 := (6 : u8)

--  SHAKE domain separation byte (0x1F = 0b11111: four-bit suffix "1111" + first bit of pad10*1).
def SHAKE_DELIM : u8 := (31 : u8)

end hacspec_sha3.sha3


namespace hacspec_sha3.sponge

--  Map byte-lane index `l` to the flat state array index.
--
--  FIPS 202 Section 3.1.2 defines how a bit string maps onto the state array.
--  In the byte-oriented convention used by the reference implementation,
--  byte-lane `l` maps to `A[l % 5, l / 5]` = `state[5*(l%5) + l/5]`.
def lane_index (l : usize) : RustM usize := do
  ((← ((5 : usize) *? (← (l %? (5 : usize))))) +? (← (l /? (5 : usize))))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def lane_index.spec (l : usize) :
    Spec
      (requires := do (l <? (25 : usize)))
      (ensures := fun _ => pure True)
      (lane_index (l : usize)) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [lane_index] <;> sorry
}

--  XOR a block of message bytes into the state (little-endian, lane-interleaved).
--
--  Corresponds to the `S ⊕ (Pi || 0^c)` step of Algorithm 8.
def xor_block_into_state
    (state : (RustArray u64 25))
    (block : (RustSlice u8))
    (rate : usize) :
    RustM (RustArray u64 25) := do
  let state : (RustArray u64 25) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      (← (rate /? (8 : usize)))
      (fun state _ => (do (pure true) : RustM Bool))
      state
      (fun state i =>
        (do
        let offset : usize ← ((8 : usize) *? i);
        let lane_val : u64 ←
          (core_models.num.Impl_9.from_le_bytes
            (RustArray.ofVec #v[(← block[offset]_?),
                                  (← block[(← (offset +? (1 : usize)))]_?),
                                  (← block[(← (offset +? (2 : usize)))]_?),
                                  (← block[(← (offset +? (3 : usize)))]_?),
                                  (← block[(← (offset +? (4 : usize)))]_?),
                                  (← block[(← (offset +? (5 : usize)))]_?),
                                  (← block[(← (offset +? (6 : usize)))]_?),
                                  (← block[(← (offset +? (7 : usize)))]_?)]));
        let idx : usize ← (lane_index i);
        let state : (RustArray u64 25) ←
          (rust_primitives.hax.monomorphized_update_at.update_at_usize
            state
            idx
            (← ((← state[idx]_?) ^^^? lane_val)));
        (pure state) :
        RustM (RustArray u64 25))));
  (pure state)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      xor_block_into_state.spec
      (state : (RustArray u64 25))
      (block : (RustSlice u8))
      (rate : usize) :
    Spec
      (requires := do
        ((← ((← (rate <=? (200 : usize)))
            &&? (← ((← (rate %? (8 : usize))) ==? (0 : usize)))))
          &&? (← ((← (core_models.slice.Impl.len u8 block)) >=? rate))))
      (ensures := fun _ => pure True)
      (xor_block_into_state
        (state : (RustArray u64 25))
        (block : (RustSlice u8))
        (rate : usize)) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [xor_block_into_state] <;> sorry
}

--  Extract `len` bytes from the rate portion of the state (little-endian, lane-interleaved).
--
--  Corresponds to `Trunc_r(S)` in Algorithm 8.
def squeeze_state
    (state : (RustArray u64 25))
    (output : (RustSlice u8))
    (out_offset : usize)
    (len : usize) :
    RustM (RustSlice u8) := do
  let _orig_len : usize ← (core_models.slice.Impl.len u8 output);
  let full_lanes : usize ← (len /? (8 : usize));
  let output : (RustSlice u8) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      full_lanes
      (fun output i =>
        (do
        ((← (core_models.slice.Impl.len u8 output)) ==? _orig_len) :
        RustM Bool))
      output
      (fun output i =>
        (do
        let idx : usize ← (lane_index i);
        let bytes : (RustArray u8 8) ←
          (core_models.num.Impl_9.to_le_bytes (← state[idx]_?));
        (rust_primitives.hax.folds.fold_range
          (0 : usize)
          (8 : usize)
          (fun output b =>
            (do
            ((← (core_models.slice.Impl.len u8 output)) ==? _orig_len) :
            RustM Bool))
          output
          (fun output b =>
            (do
            let output : (RustSlice u8) ←
              (rust_primitives.hax.monomorphized_update_at.update_at_usize
                output
                (← ((← (out_offset +? (← ((8 : usize) *? i)))) +? b))
                (← bytes[b]_?));
            (pure output) :
            RustM (RustSlice u8)))) :
        RustM (RustSlice u8))));
  let remaining : usize ← (len %? (8 : usize));
  let output : (RustSlice u8) ←
    if (← (remaining >? (0 : usize))) then do
      let idx : usize ← (lane_index full_lanes);
      let bytes : (RustArray u8 8) ←
        (core_models.num.Impl_9.to_le_bytes (← state[idx]_?));
      (rust_primitives.hax.folds.fold_range
        (0 : usize)
        remaining
        (fun output b =>
          (do
          ((← (core_models.slice.Impl.len u8 output)) ==? _orig_len) :
          RustM Bool))
        output
        (fun output b =>
          (do
          let output : (RustSlice u8) ←
            (rust_primitives.hax.monomorphized_update_at.update_at_usize
              output
              (← ((← (out_offset +? (← ((8 : usize) *? full_lanes)))) +? b))
              (← bytes[b]_?));
          (pure output) :
          RustM (RustSlice u8))))
    else do
      (pure output);
  (pure output)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      squeeze_state.spec
      (state : (RustArray u64 25))
      (output : (RustSlice u8))
      (out_offset : usize)
      (len : usize) :
    Spec
      (requires := do
        ((← ((← (len <=? (200 : usize)))
            &&? (← ((← (core_models.slice.Impl.len u8 output)) >=? len))))
          &&? (← (out_offset
            <=? (← ((← (core_models.slice.Impl.len u8 output)) -? len))))))
      (ensures := fun
          output_future => do
          ((← (core_models.slice.Impl.len u8 output_future))
            ==? (← (core_models.slice.Impl.len u8 output))))
      (squeeze_state
        (state : (RustArray u64 25))
        (output : (RustSlice u8))
        (out_offset : usize)
        (len : usize)) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [squeeze_state] <;> sorry
}

end hacspec_sha3.sponge


namespace hacspec_sha3

--  Utility function to create an array of size `N` by applying a function `f` to each index.
@[spec]
def createi:=
  core_models.array.from_fn

end hacspec_sha3


namespace hacspec_sha3.keccak_f

--  θ step — FIPS 202, Algorithm 1.
--
--    C[x]    = A[x,0] ⊕ A[x,1] ⊕ A[x,2] ⊕ A[x,3] ⊕ A[x,4]
--    D[x]    = C[x−1 mod 5] ⊕ rot(C[x+1 mod 5], 1)
--    A′[x,y] = A[x,y] ⊕ D[x]
@[spec]
def theta (state : (RustArray u64 25)) : RustM (RustArray u64 25) := do
  let c : (RustArray u64 5) ←
    (hacspec_sha3.createi u64 ((5 : usize)) (usize -> RustM u64)
      (fun x =>
        (do
        ((← ((← ((← ((← (get state x (0 : usize)))
                ^^^? (← (get state x (1 : usize)))))
              ^^^? (← (get state x (2 : usize)))))
            ^^^? (← (get state x (3 : usize)))))
          ^^^? (← (get state x (4 : usize)))) :
        RustM u64)));
  let d : (RustArray u64 5) ←
    (hacspec_sha3.createi u64 ((5 : usize)) (usize -> RustM u64)
      (fun x =>
        (do
        ((← c[(← ((← (x +? (4 : usize))) %? (5 : usize)))]_?)
          ^^^? (← (core_models.num.Impl_9.rotate_left
            (← c[(← ((← (x +? (1 : usize))) %? (5 : usize)))]_?)
            (1 : u32)))) :
        RustM u64)));
  (hacspec_sha3.createi u64 ((25 : usize)) (usize -> RustM u64)
    (fun idx =>
      (do
      ((← state[idx]_?) ^^^? (← d[(← (idx /? (5 : usize)))]_?)) : RustM u64)))

--  ρ step — FIPS 202, Algorithm 2.
--
--    A′[x,y] = rot(A[x,y], offset(x,y))
@[spec]
def rho (state : (RustArray u64 25)) : RustM (RustArray u64 25) := do
  (hacspec_sha3.createi u64 ((25 : usize)) (usize -> RustM u64)
    (fun idx =>
      (do
      (core_models.num.Impl_9.rotate_left
        (← state[idx]_?)
        (← RHO_OFFSETS[idx]_?)) :
      RustM u64)))

--  π step — FIPS 202, Algorithm 3.
--
--    A′[x,y] = A[(x + 3y) mod 5, x]
@[spec]
def pi (state : (RustArray u64 25)) : RustM (RustArray u64 25) := do
  (hacspec_sha3.createi u64 ((25 : usize)) (usize -> RustM u64)
    (fun idx =>
      (do
      let x : usize ← (idx /? (5 : usize));
      let y : usize ← (idx %? (5 : usize));
      (get state (← ((← (x +? (← ((3 : usize) *? y)))) %? (5 : usize))) x) :
      RustM u64)))

--  χ step — FIPS 202, Algorithm 4.
--
--    A′[x,y] = A[x,y] ⊕ (¬A[(x+1) mod 5, y] ∧ A[(x+2) mod 5, y])
@[spec]
def chi (state : (RustArray u64 25)) : RustM (RustArray u64 25) := do
  (hacspec_sha3.createi u64 ((25 : usize)) (usize -> RustM u64)
    (fun idx =>
      (do
      let x : usize ← (idx /? (5 : usize));
      let y : usize ← (idx %? (5 : usize));
      ((← (get state x y))
        ^^^? (← ((← (~? (← (get
            state
            (← ((← (x +? (1 : usize))) %? (5 : usize)))
            y))))
          &&&? (← (get state (← ((← (x +? (2 : usize))) %? (5 : usize))) y)))))
      :
      RustM u64)))

--  Keccak-f[1600] permutation — FIPS 202, Algorithm 7.
--
--    Rnd(A, ir) = ι(χ(π(ρ(θ(A)))), ir)
@[spec]
def keccak_f (state : (RustArray u64 25)) : RustM (RustArray u64 25) := do
  let state : (RustArray u64 25) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      (24 : usize)
      (fun state _ => (do (pure true) : RustM Bool))
      state
      (fun state round =>
        (do
        (iota (← (chi (← (pi (← (rho (← (theta state)))))))) round) :
        RustM (RustArray u64 25))));
  (pure state)

end hacspec_sha3.keccak_f


namespace hacspec_sha3.sponge

--  Keccak sponge — FIPS 202, Algorithm 8 combined with pad10*1 (Algorithm 9).
--
--  1. Absorb: split `message` into `rate`-byte blocks, XOR each into the
--     state, and apply Keccak-f. The final partial block is padded with
--     the domain separation byte `delim` and the pad10*1 terminator `0x80`.
--  2. Squeeze: extract `OUTPUT_LEN` bytes from the state, applying
--     Keccak-f between each `rate`-byte block of output.
--
--  The `OUTPUT_LEN < usize::MAX - 200` precondition is a Rust implementation
--  artifact to prevent arithmetic overflow; FIPS 202 places no upper bound
--  on the output length.
def keccak (OUTPUT_LEN : usize)
    (rate : usize)
    (delim : u8)
    (message : (RustSlice u8)) :
    RustM (RustArray u8 OUTPUT_LEN) := do
  let state : (RustArray u64 25) ←
    (rust_primitives.hax.repeat (0 : u64) (25 : usize));
  let num_full_blocks : usize ←
    ((← (core_models.slice.Impl.len u8 message)) /? rate);
  let state : (RustArray u64 25) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      num_full_blocks
      (fun state _ => (do (pure true) : RustM Bool))
      state
      (fun state block_idx =>
        (do
        let offset : usize ← (block_idx *? rate);
        let state : (RustArray u64 25) ←
          (xor_block_into_state
            state
            (← message[
              (core_models.ops.range.Range.mk
                (start := offset)
                (_end := (← (offset +? rate))))
              ]_?)
            rate);
        let state : (RustArray u64 25) ← (hacspec_sha3.keccak_f.keccak_f state);
        (pure state) :
        RustM (RustArray u64 25))));
  let last_block : (RustArray u8 200) ←
    (rust_primitives.hax.repeat (0 : u8) (200 : usize));
  let remaining : usize ←
    ((← (core_models.slice.Impl.len u8 message))
      -? (← (num_full_blocks *? rate)));
  let last_block : (RustArray u8 200) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      remaining
      (fun last_block _ => (do (pure true) : RustM Bool))
      last_block
      (fun last_block i =>
        (do
        (rust_primitives.hax.monomorphized_update_at.update_at_usize
          last_block
          i
          (← message[(← ((← (num_full_blocks *? rate)) +? i))]_?)) :
        RustM (RustArray u8 200))));
  let last_block : (RustArray u8 200) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      last_block
      remaining
      delim);
  let last_block : (RustArray u8 200) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      last_block
      (← (rate -? (1 : usize)))
      (← ((← last_block[(← (rate -? (1 : usize)))]_?) |||? (128 : u8))));
  let state : (RustArray u64 25) ←
    (xor_block_into_state state (← (rust_primitives.unsize last_block)) rate);
  let state : (RustArray u64 25) ← (hacspec_sha3.keccak_f.keccak_f state);
  let output : (RustArray u8 OUTPUT_LEN) ←
    (rust_primitives.hax.repeat (0 : u8) OUTPUT_LEN);
  let offset : usize := (0 : usize);
  let ⟨offset, output, state⟩ ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      (← ((← ((← (OUTPUT_LEN +? rate)) -? (1 : usize))) /? rate))
      (fun ⟨offset, output, state⟩ _squeeze_round =>
        (do (offset <=? OUTPUT_LEN) : RustM Bool))
      (rust_primitives.hax.Tuple3.mk offset output state)
      (fun ⟨offset, output, state⟩ _squeeze_round =>
        (do
        let to_copy : usize ←
          if (← ((← (OUTPUT_LEN -? offset)) <? rate)) then do
            (OUTPUT_LEN -? offset)
          else do
            (pure rate);
        let output : (RustArray u8 OUTPUT_LEN) ←
          (rust_primitives.hax.monomorphized_update_at.update_at_range_full
            output
            core_models.ops.range.RangeFull.mk
            (← (squeeze_state
              state
              (← output[core_models.ops.range.RangeFull.mk]_?)
              offset
              to_copy)));
        let offset : usize ← (offset +? to_copy);
        if (← (offset <? OUTPUT_LEN)) then do
          let state : (RustArray u64 25) ←
            (hacspec_sha3.keccak_f.keccak_f state);
          (pure (rust_primitives.hax.Tuple3.mk offset output state))
        else do
          (pure (rust_primitives.hax.Tuple3.mk offset output state)) :
        RustM
        (rust_primitives.hax.Tuple3
          usize
          (RustArray u8 OUTPUT_LEN)
          (RustArray u64 25)))));
  (pure output)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      keccak.spec (OUTPUT_LEN : usize)
      (rate : usize)
      (delim : u8)
      (message : (RustSlice u8)) :
    Spec
      (requires := do
        ((← ((← ((← (rate >? (0 : usize))) &&? (← (rate <=? (200 : usize)))))
            &&? (← ((← (rate %? (8 : usize))) ==? (0 : usize)))))
          &&? (← (OUTPUT_LEN
            <? (← (core_models.num.Impl_11.MAX -? (200 : usize)))))))
      (ensures := fun _ => pure True)
      (keccak
        (OUTPUT_LEN : usize)
        (rate : usize)
        (delim : u8)
        (message : (RustSlice u8))) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [keccak] <;> sorry
}

end hacspec_sha3.sponge


namespace hacspec_sha3.sha3

--  SHA3-224 — FIPS 202, Section 6.1.
@[spec]
def sha3_224 (message : (RustSlice u8)) : RustM (RustArray u8 28) := do
  (hacspec_sha3.sponge.keccak ((28 : usize)) SHA3_224_RATE SHA3_DELIM message)

--  SHA3-256 — FIPS 202, Section 6.1.
@[spec]
def sha3_256 (message : (RustSlice u8)) : RustM (RustArray u8 32) := do
  (hacspec_sha3.sponge.keccak ((32 : usize)) SHA3_256_RATE SHA3_DELIM message)

--  SHA3-384 — FIPS 202, Section 6.1.
@[spec]
def sha3_384 (message : (RustSlice u8)) : RustM (RustArray u8 48) := do
  (hacspec_sha3.sponge.keccak ((48 : usize)) SHA3_384_RATE SHA3_DELIM message)

--  SHA3-512 — FIPS 202, Section 6.1.
@[spec]
def sha3_512 (message : (RustSlice u8)) : RustM (RustArray u8 64) := do
  (hacspec_sha3.sponge.keccak ((64 : usize)) SHA3_512_RATE SHA3_DELIM message)

--  SHAKE128 — FIPS 202, Section 6.2.
--
--  FIPS 202 places no upper bound on the output length `N`.
--  The `N < usize::MAX - 200` precondition is a Rust implementation artifact
--  to prevent arithmetic overflow during squeeze-loop bound computation.
def shake128 (N : usize) (message : (RustSlice u8)) :
    RustM (RustArray u8 N) := do
  (hacspec_sha3.sponge.keccak (N) SHAKE128_RATE SHAKE_DELIM message)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def shake128.spec (N : usize) (message : (RustSlice u8)) :
    Spec
      (requires := do (N <? (← (core_models.num.Impl_11.MAX -? (200 : usize)))))
      (ensures := fun _ => pure True)
      (shake128 (N : usize) (message : (RustSlice u8))) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [shake128] <;> sorry
}

--  SHAKE256 — FIPS 202, Section 6.2.
--
--  FIPS 202 places no upper bound on the output length `N`.
--  The `N < usize::MAX - 200` precondition is a Rust implementation artifact
--  to prevent arithmetic overflow during squeeze-loop bound computation.
def shake256 (N : usize) (message : (RustSlice u8)) :
    RustM (RustArray u8 N) := do
  (hacspec_sha3.sponge.keccak (N) SHAKE256_RATE SHAKE_DELIM message)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def shake256.spec (N : usize) (message : (RustSlice u8)) :
    Spec
      (requires := do (N <? (← (core_models.num.Impl_11.MAX -? (200 : usize)))))
      (ensures := fun _ => pure True)
      (shake256 (N : usize) (message : (RustSlice u8))) := {
  pureRequires := by hax_construct_pure <;> sorry
  pureEnsures := by hax_construct_pure <;> sorry
  contract := by hax_mvcgen [shake256] <;> sorry
}

end hacspec_sha3.sha3
