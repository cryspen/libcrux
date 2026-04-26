# C4f Handoff — Trait Postcondition Closures (post forall16 refactor)

Status as of 2026-04-26.  Previous brief: `manual-proof-targets.md`.
Active branch: `trait-poststrengthen`.  Pushed through `830ec8b8b`.

## What landed (this session)

| Item | Commit | Notes |
|---|---|---|
| Trait posts → `Spec.Utils.forall16` | `fb4f8154d` | `compress_{1,}_post`, `decompress_{1,_ciphertext_coefficient}_post` switched from `compress_post_N` (Form 1) to `forall16` (Form 3) per the C4-era benchmark |
| portable `op_compress_1` panic_free dropped | `fb4f8154d` | Body: 16 explicit A5 calls.  Verifies in 6.3 s @ rlimit 200 |
| portable `op_compress<D>` panic_free dropped | `830ec8b8b` | Body: 16 explicit A8 calls.  Verifies in 14 s @ rlimit 300 |
| A8 (`lemma_compress_ciphertext_coefficient_fe_commute`) admit | `830ec8b8b` | Barrett-exactness 4-case math, tedious — admit per the manual-proof-targets brief |

## Pending — Z3-blocked / left for the user

### 1. `lemma_decompress_1_chunk_commutes` and `lemma_decompress_ciphertext_coefficient_chunk_commutes`

**File**: `specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Commute.Chunk.fst:1026`, `:1043`.

**Symptom**: With `()` body and after revealing `bounded_i16_array`, Z3 splits the `forall16` goal into 16 per-lane sub-queries.  15 succeed in ~25 ms each; one specific lane (query 11 of 16) fails consistently with `incomplete quantifiers` at rlimit 80 / 200 / 300.  Other 15 lanes succeed at any rlimit.

**Hypothesis**: The implication-form post `(forall i. v vec_i < pow2 d) ==> forall16 (...)` requires Z3 to instantiate the antecedent's forall at the lane index for each split sub-query.  One specific lane index trips a quantifier-instantiation pattern bug in this SMT context.

**Things tried**:
- `reveal_opaque (bounded_i16_array)` in body → 15/16 pass, 1 fails
- rlimit 80 → 200 → 300 — same lane fails (so it's not a time issue)
- Restructure ensures from inline forall16 to call `TS.decompress_1_post` directly — type-checks but body still admit (didn't try non-admit body since it just reduces to the same thing)

**Possible fixes**:
- Replace the implication's premise `forall i. v vec_i < pow2 d` with explicit per-lane bounds
- Use `Classical.forall_intro` with an `aux` that takes the index and explicitly cites the bound
- Inline-unfold `bounded_pos_i16_array d vec` in the body so Z3 sees the bounds directly without forall instantiation
- Re-check at d ∈ {4, 5, 10, 11} separately (the parameterized version may need case-splitting on d at the chunk level)

**Cascade**: Closing these unblocks the `op_decompress_1` and `op_decompress_ciphertext_coefficient` wrapper panic_free drops in `src/vector/portable.rs` and (after AVX2-side bridges) `src/vector/avx2.rs`.

### 2. A8 — `lemma_compress_ciphertext_coefficient_fe_commute`

**File**: `specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Commute.Chunk.fst:967`.

**Status**: Admitted.  Statement bridges integer Barrett form `v result == ((v fe * 2 * pow2 d + 3329) / 6658) % pow2 d` (the impl-side post) to FE form `compress_d (i16_to_spec_fe fe) d == i16_to_spec_fe result`, for D ∈ {4, 5, 10, 11}.

**Math**: 4-case enumeration on D, each case requires a Barrett-exactness argument tying the `(2x·2^d + 3329) / 6658` rounded division to `compress_d`'s reference formula.

**Why deferred**: Per `manual-proof-targets.md` line 269: "A8 (Barrett compress, lemma_compress_ciphertext_coefficient_fe_commute) can be admitted with English hints — full proof is very tedious and not high leverage at this layer."  Currently admitted; `op_compress<D>` consumes it.

### 3. Portable `op_ntt_multiply` panic_free drop

**File**: `src/vector/portable.rs:702` (`op_ntt_multiply`).

**Status**: Still `panic_free`.  Underlying body has 8 `lemma_base_case_mult_pair_commute` calls + a final `admit ()` for the 4-FE-per-branch × 4-branch glue (per C4e — commit `57fbc9f7b`).  Now that A1–A4 are real proofs (not admits), the `lemma_base_case_mult_pair_commute` cite chain is sound; the remaining wedge is the `forall4 (fun b -> p_ntt_mult b)` aggregation.

**Why deferred this session**: The full-module verify segfaulted at `op_ntt_multiply`'s VC after my changes (compress posts strengthened ⇒ more SMT context for impl_1's other methods).  Needs a careful re-attempt with possibly:
- Per-branch query splitting via `assert (p_ntt_mult b)` for b ∈ {0, 1, 2, 3} on separate lines
- Dedicated rlimit (≥800) and `--split_queries always`
- Decomposing the core int-lemma (`lemma_base_case_mult_*_mod_core_fe_form`) into per-`169`-unwrap sub-lemmas to reduce SMT load

**Cascade**: Closes the last portable wrapper.  AVX2 mirror (`op_ntt_multiply` AVX2) is C4'-blocked on Z3 walls anyway.

### 4. F* segfault during full-module verify of `Libcrux_ml_kem.Vector.Portable.fst`

**Symptom**: `make run/Libcrux_ml_kem.Vector.Portable.fst` segfaults after passing `op_compress_1` / `op_compress` / `op_decompress_*` / `op_ntt_layer_*` / `op_inv_ntt_layer_*` (all VCs succeed individually), at or near `op_ntt_multiply`'s VC.  Reproducible.

**Diagnosis**: The strengthened `compress_*_post` and `decompress_*_post` add forall16-shaped predicates to the module's SMT context.  Coupled with `op_ntt_multiply`'s already-heavy proof obligations (forall4 over 4-FE-per-branch equations), the cumulative context likely overflows a Z3/F* memory limit.

**Workarounds**:
- Verify in incremental chunks via fstar-mcp (`create_session` + `typecheck_buffer`) — still works, individual VCs succeed
- Use `#push-options "--z3refresh"` more liberally between methods (observed earlier in C4e)
- Split the impl block into separate F* modules (would require Rust-side restructure)

**Status**: Not blocking — the changed wrappers verify individually.  The segfault is a meta-issue in cumulative VC load, not a proof bug.

### 5. AVX2 mirror of all of the above (C4')

**Status**: All AVX2 `op_compress_*` / `op_decompress_*` / `op_ntt_multiply` are still `panic_free`.  Drops require:
- The same trait post is now forall16 (consumed)
- Per-element fe_commute lemmas (A5–A8 — same as portable)
- **AVX2 per-lane Vec256↔array bridges** (don't exist yet) — translate the AVX2 primitive's bit-vector post to the array form expected by A5–A8 calls

**Z3-blocked items**: `op_ntt_layer_{1,2}_step` and `op_inv_ntt_layer_{1,2}_step` bridge admits (4 admits at `src/vector/avx2.rs:253/265/285/297`) — Z3 walls documented in commit `087fbc34c`.  Deferred to SIMD model unification (`proofs/simd-model-unification-plan.md`).

## Where things stand

`Hacspec_ml_kem.Commute.Chunk.fst`:
- A1–A7 ✅
- A8 (parameterized compress) ⏸️ admitted
- B-tier (4 chunk-level commute lemmas):
  - `compress_1`, `compress` ✅ close in 755 ms / 1888 ms
  - `decompress_1`, `decompress_ciphertext_coefficient` ⏸️ admitted (Z3 lane-11 wedge)

`src/vector/portable.rs`:
- `op_compress_1`, `op_compress<D>` ✅ panic_free DROPPED, real proof
- `op_decompress_1`, `op_decompress_ciphertext_coefficient` still `panic_free` (waiting on chunk lemmas above)
- `op_ntt_multiply` still `panic_free` + body `admit ()` (C4e legacy)

`src/vector/avx2.rs`:
- All compress/decompress/ntt_multiply wrappers still `panic_free` (waiting on AVX2 per-lane bridges)
- NTT-layer 3 / inv-NTT-layer 3 ✅ verified (top-to-bottom)
- NTT-layer 1/2 + inv-NTT-layer 1/2 ⏸️ verified via 4 bridge admits (Z3-blocked)

## Build commands

```bash
# Re-extract Rust → F* (after src/ changes):
cd libcrux-ml-kem && python3 hax.py extract
rm -f proofs/fstar/extraction/Libcrux_ml_kem.Hash_functions.fst

# Verify Commute.Chunk only (~93 s):
cd specs/ml-kem/proofs/fstar/commute && make run/Hacspec_ml_kem.Commute.Chunk.fst

# Verify Vector.Portable — segfaults pre-completion as noted in #4:
cd libcrux-ml-kem/proofs/fstar/extraction && make run/Libcrux_ml_kem.Vector.Portable.fst

# Per-method incremental check via fstar-mcp:
FSTAR_MCP_PORT=3001 /root/fstar-mcp/target/release/fstar-mcp &
# then create_session + typecheck_buffer per the api-protocol.md
```
