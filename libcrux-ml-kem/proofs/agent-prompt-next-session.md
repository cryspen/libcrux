# Agent prompt — libcrux-ml-kem-proofs, impl-side pure-Rust migration

Paste this into a fresh Claude Code session opened in
`~/libcrux-trait-opacify/libcrux-ml-kem` (auto mode recommended).

You are a single-lane agent for the libcrux-ml-kem F\* verification
effort.  This session's goal: convert `#[hax_lib::requires(fstar!(...))]`
and `#[hax_lib::ensures(fstar!(...))]` annotations in
`libcrux-ml-kem/src/ind_cpa.rs` and `libcrux-ml-kem/src/ind_cca.rs`
from `Spec.MLKEM.*` citations in F\* syntax to **pure-Rust** citations
of `hacspec_ml_kem::*` (per R11).  The spec side has been stabilized in
the prior session — your work is impl-side only.

## Read first (in order)

  1. `proofs/agent-status/spec-audit-2026-05-01.md` — function-by-function
     audit (37 rows; impl ↔ Hacspec mapping).  **Lines 56-99 is the
     authoritative table.**  The Phase 2/3 execution log appended at
     line 197+ records the spec-side commits and what's deferred.
  2. The 11 spec-side commits since `723539e40`:
     ```
     8ebbce94a — close byte_decode panic_free (Phase 3 done)
     c13107543 — extract compress_then_serialize_u_into
     baf5eb3d3 — extract serialize_secret_key_into; remove vector_encode_12
     cb44addd3 — drop unused ensures from get_zeta, remove panic_free
     356f617f5 — append Phase 2/3 execution log to spec audit
     76baea2b1 — (superseded by 8ebbce94a) doc-only
     a4890d89a — (superseded by cb44addd3) doc-only
     e63973e54 — relax ind_cpa::generate_keypair seed to slice (P3)
     57d1a5e61 — drop redundant T_SIZE generic from serialize_public_key (P2)
     329d4195e — add 16 rank-generic size helpers to parameters.rs (P1)
     16ab471a4 — spec audit before refactor
     ```
     Read commit messages for `baf5eb3d3` (the `_into` pattern + the
     loop_invariant trick) and `8ebbce94a` (additive form for
     bit-OR Z3 obstruction) — both surface non-obvious lessons that
     apply to impl-side proofs too.
  3. The original `proofs/agent-prompt-clean-restart.md` for R1-R10,
     workflow, and Spec.MLKEM → Hacspec mapping table.

## Branch state at session start

```
$ git log --oneline -5
8ebbce94a agent-mlkem: specs/ml-kem — close byte_decode panic_free (Phase 3)
c13107543 agent-mlkem: specs/ml-kem — extract compress_then_serialize_u_into
baf5eb3d3 agent-mlkem: specs/ml-kem — extract serialize_secret_key_into; remove vector_encode_12
cb44addd3 agent-mlkem: specs/ml-kem — drop unused ensures from get_zeta, remove panic_free (Phase 3)
356f617f5 agent-mlkem: append Phase 2/3 execution log to spec audit
```

Branch: `libcrux-ml-kem-proofs`.  Tip: `8ebbce94a`.  Pushed to
`origin/libcrux-ml-kem-proofs`.

## Spec state (what you have to call from pure-Rust ensures)

### `specs/ml-kem/src/parameters.rs` — rank-generic helpers

Free functions added in commit `329d4195e` (P1) — all rank-only:

  * `is_rank(rank) -> bool`, `rank_to_params(rank) -> MlKemParams`
  * `cpa_public_key_size(rank)`, `cca_private_key_size(rank)`,
    `cpa_private_key_size(rank)`, `cpa_ciphertext_size(rank)`
  * `t_as_ntt_encoded_size(rank)`, `ranked_bytes_per_ring_element(rank)`
  * `c1_size(rank)`, `c2_size(rank)`, `c1_block_size(rank)`
  * `vector_u_compression_factor(rank)`, `vector_v_compression_factor(rank)`
  * `eta1(rank)`, `eta2(rank)`, `eta1_randomness_size(rank)`,
    `eta2_randomness_size(rank)`
  * `implicit_rejection_hash_input_size(rank)`
  * Constants: `SHARED_SECRET_SIZE = 32`, `CPA_KEY_GENERATION_SEED_SIZE = 32`

`MlKemParams` methods (`ek_size`, `dk_size`, `dk_pke_size`,
`u_encoded_size`, `v_encoded_size`, `ciphertext_size`,
`t_as_ntt_encoded_size`) are also available — pick whichever reads
better at the call site.

### `specs/ml-kem/src/serialize.rs` — `_into` pattern established

The encoding layer now consistently follows: `_into` is the canonical
primitive (writes to `&mut [u8]`), value-returning is a thin allocating
wrapper.  Three exemplars:

  * `byte_encode_into(p, d, &mut out)` ↔ `byte_encode<D32, D256>(p, d) -> [u8; D32]`
  * `serialize_secret_key_into<RANK>(vector, &mut out)` ↔
    `serialize_secret_key<RANK, T_SIZE>(vector) -> [u8; T_SIZE]` (commit `baf5eb3d3`)
  * `compress_then_serialize_u_into<RANK>(u, du, &mut out)` ↔
    `compress_then_serialize_u<RANK, U_SIZE>(u, du) -> [u8; U_SIZE]` (commit `c13107543`)

### `specs/ml-kem/src/ind_cpa.rs`

  * `ind_cpa::generate_keypair<RANK, EK_SIZE, DK_PKE_SIZE>(params, &[u8])`
    now takes `key_generation_seed: &[u8]` (relaxed from `&[u8; 32]` in
    commit `e63973e54`) so the libcrux side doesn't need an array bridge.

### Verification status

  * **All 10 `Hacspec_ml_kem.*.fst.checked` re-build clean** in ~28s.
  * **No `lax`, no `panic_free`, no `admit ()`** anywhere in
    `specs/ml-kem/src/` or extracted Hacspec_ml_kem F\*.  The
    `panic_free` items the prior session documented as out-of-budget
    (`get_zeta`, `byte_decode`) are both closed (commits `cb44addd3`,
    `8ebbce94a`).
  * `Hacspec_ml_kem.Commute.Chunk.fst:1046` failure remains
    pre-existing (predates the prior session — confirmed by `git stash`
    baseline).  Doesn't block impl-side migration.
  * `Libcrux_ml_kem.Ind_cca.fsti(165)` blocker (Spec.MLKEM not resolved
    in `encapsulate` requires) remains pre-existing.  Your impl-side
    migrations may eventually fix this by replacing the offending
    `Spec.MLKEM.*` cites with `hacspec_ml_kem::*` cites.

## Pure-Rust ensures patterns — pick per shape

There is **no precedent** in the codebase for pure-Rust ensures that
do array-equality with a Hacspec function call (all existing
array-equality ensures use `fstar!`).  You'll be pioneering.  Three
patterns to choose between, depending on the impl function's output
shape:

### Pattern A — value-returning function-call ensures

When the impl returns a sized array AND the size is a libcrux const
generic that lines up with a Hacspec const generic.  Example: existing
`ind_cca::generate_keypair` (libcrux's K, PUBLIC_KEY_SIZE,
PRIVATE_KEY_SIZE, CPA_PRIVATE_KEY_SIZE all match Hacspec's RANK,
EK_SIZE, DK_SIZE, DK_PKE_SIZE).

```rust
#[hax_lib::ensures(|result|
    match hacspec_ml_kem::ind_cca::generate_keypair::<K, PUBLIC_KEY_SIZE, PRIVATE_KEY_SIZE, CPA_PRIVATE_KEY_SIZE>(
        &hacspec_ml_kem::parameters::rank_to_params(K),
        randomness,
    ) {
        Ok((ek, dk)) => result.pk.value == ek && result.sk.value == dk,
        Err(_) => true,
    }
)]
```

### Pattern B — auxiliary-buffer ensures (slice-output impl)

When the impl writes into `&mut [u8]` (no const-generic for the size
on the impl side).  Use the `_into` companion via an auxiliary buffer:

```rust
#[hax_lib::ensures(|_| {
    let mut expected = [0u8; PARENT_SIZE];  // or another known size
    serialize_secret_key_into::<K>(&crate::vector::spec::vector_to_spec(key), &mut expected[..]);
    out_future == expected[..K * BYTES_PER_RING_ELEMENT]
})]
```

(This is *pioneered* — verify on one function before scaling out.)

### Pattern C — field-projection ensures (unpacked APIs)

When the impl mutates an unpacked struct.  Don't add a new spec helper
unless absolutely necessary — instead, project fields and cite the
existing packed helper:

```rust
#[hax_lib::ensures(|_| {
    let unpacked_future = future(unpacked_public_key);
    // project + cite packed helpers per field
    unpacked_future.t_as_ntt == ... &&
    unpacked_future.seed_for_A == ... &&
    unpacked_future.A == ...
})]
```

If a function genuinely needs a composed helper, **add it to
`specs/ml-kem/src/{ind_cpa,ind_cca}.rs`** as a separate
spec-side commit (per the workflow), then use it.

## Open work — priority order

### 1. Validate Pattern A on `ind_cca::generate_keypair` (line 199)

Already partially-migrated in commit `9ffc850db` — currently uses
`fstar!(...)` to cite `Hacspec_ml_kem.Parameters.Sizes.*` and
`Hacspec_ml_kem.Ind_cca.generate_keypair`.  Convert to pure-Rust.
Smallest blast radius (the Hacspec function's signature already lines
up with the libcrux const generics).

If this works, Pattern A is validated.  If it fails, capture the error
shape and decide whether to (a) try a different formulation, (b) request
a hax-lib feature, (c) accept that Pattern A doesn't work in this
codebase and use only B/C.

### 2. Validate Pattern B on `ind_cpa::serialize_vector` (line 140)

Smallest slice-output function.  Use the new
`serialize_secret_key_into::<K>(vector_to_spec(key), &mut expected[..])`
auxiliary-buffer ensures.  Re-extract; verify
`Libcrux_ml_kem.Ind_cpa.fst.checked` rebuilds (acknowledging the
`Ind_cca.fsti(165)` blocker downstream — the `.fst` body verification
may not reach if the .fsti has the blocker; verify what you can at
the .fst[i] level).

If this works, Pattern B is validated and applies to:
`serialize_public_key`, `serialize_public_key_mut`,
`compress_then_serialize_u`, `serialize_unpacked_secret_key` (all
slice-output).

### 3. Validate Pattern C on `ind_cca::unpacked::generate_keypair` (line 871)

Smallest unpacked-API function.  Use field-projection ensures.  If a
specific spec helper is genuinely needed (e.g. for the `A_transpose`
or `implicit_rejection_value` projections), add it to
`specs/ml-kem/src/ind_cca.rs` in a separate commit before doing the
impl-side conversion.

### 4. After all three patterns validated: migrate the rest

Apply the validated patterns to every other impl function with
`fstar!(...)` annotations.  Order suggestion (smallest-first):

  - `ind_cpa.rs`: `serialize_public_key`, `serialize_public_key_mut`,
    `serialize_vector`, `serialize_unpacked_secret_key`,
    `compress_then_serialize_u`, `deserialize_vector`,
    `build_unpacked_public_key`, `build_unpacked_public_key_mut`,
    `decrypt`, `decrypt_unpacked`, `encrypt`, `encrypt_unpacked`,
    `encrypt_c1`, `encrypt_c2`, `generate_keypair`,
    `generate_keypair_unpacked`, `sample_ring_element_cbd`,
    `sample_vector_cbd_then_ntt`.
  - `ind_cca.rs`: `validate_public_key`, `validate_private_key{,_only}`,
    `serialize_kem_secret_key{,_mut}`, `encapsulate`, `decapsulate`,
    `unpacked::*`.

For each, **commit per function** with `agent-mlkem:` prefix.  Cap at
4-5 functions per session; cap iteration at 20 min/attempt (R5).

### 5. Defer / out-of-scope

  - `Hacspec_ml_kem.Commute.Chunk.fst:1046` failure (separate sprint).
  - Bridge proofs for `i16_to_spec_fe`/`mont_i16_to_spec_fe` (still
    keep `fstar!` ensures per the documented exception in the prior
    prompt — see "fstar! escape hatch policy").
  - Audit row 16 (`deserialize_then_decompress_u_then_ntt` composed
    helper).  May or may not be needed depending on how Pattern B
    handles `deserialize_then_decompress_u`.  Add only if forced.
  - P5 unpacked-shape helpers (audit rows 5, 6, 10, 18, 34, 35, 37).
    Add per-function ONLY when Pattern C demonstrably fails for that
    function — don't speculate.

## Hard rules (R1-R11)

  R1  Branch `libcrux-ml-kem-proofs`.  Already pushed to
      `origin/libcrux-ml-kem-proofs`.  You MAY `git push` further
      commits.  DO NOT force-push, DO NOT push to `main`, and DO NOT
      open a PR without explicit user authorization.
  R2  No new admits beyond existing `lax` / `ADMIT_MODULES` carry-overs.
  R3  No new axioms.  If absolutely necessary, file as SIDEWAYS.
  R4  `--z3rlimit ≤ 800` HARD CAP; `≤ 400/query` under
      `--split_queries always`.  Default tier `--z3rlimit 200`.
  R5  Inner edit-check: `make check/<Mod>.fst` from
      `proofs/fstar/extraction/`.  Cap iteration at 20 min/attempt.
  R6  After `python3 hax.py extract`: snapshot SHAs and touch unchanged
      `.checked` files (per `feedback_touch_unchanged_checked`).
  R7  Trait FROZEN — `src/vector/traits.rs`'s `Operations` /
      `Repr` definitions not edited.  The `spec` submodule below
      it MAY be edited.
  R8  No `fstar-mcp` (per `feedback_use_fstar_mcp` and
      `feedback_fstar_mcp_session_dies_after_make`).
  R9  Commit prefix `agent-mlkem:`.  Commit Rust-spec changes
      separately from libcrux-side changes.
  R10 No wrappers.  No namespace-squatting.  No new F\* specs in
      `Hacspec_ml_kem.*` (per the FORBIDDEN section of the
      clean-restart prompt).
  R11 **No `fstar!` escape in `src/ind_cpa.rs` / `src/ind_cca.rs`
      annotations.**  This is the goal of this session.  The two
      documented exceptions (`i16_to_spec_fe`, `mont_i16_to_spec_fe`
      ensures) live in `src/vector/traits.rs` — they are NOT touched.
      If you find yourself wanting `fstar!` in an ensures, capture the
      reason and ask the user before shipping it.

### Loop-invariant lesson from the prior session (applies to your work)

The prior session learned that `_into`-style functions writing to
`&mut [u8]` need an explicit
`hax_lib::loop_invariant!(|_i| out.len() == EXPECTED_SIZE)` to
discharge per-iteration sub-slice index bounds when `out` is a slice
parameter (vs. a typed array).  Without it Z3 reports "incomplete
quantifiers" and refuses to prove `(i+1)*BLOCK <= out.len()`.  Same
pattern likely recurs in any libcrux-side function with a slice-output
loop.

### Bit-OR vs addition lesson

In bit-assembly loops, `coef |= 1u16 << j` resists Z3's bound proofs
("incomplete quantifiers" on subtype check).  Rewriting to
`coef += 1u16 << j` is semantically identical when the loop invariant
guarantees the new bit isn't already set, and Z3 discharges the
additive bound far more easily.  Watch for this pattern.

## Workflow

  1. **Verify state**: branch is `libcrux-ml-kem-proofs`, tip
     `8ebbce94a`, `make` from `proofs/fstar/extraction/` reproduces
     the `Ind_cca.fsti:165` blocker (or whatever the user's fix moved
     it to).
  2. **Pick ONE function** from the open-work list.  Smallest-coherent-
     unit principle.  Start with the three pattern-validation targets
     (items 1-3 above) before scaling.
  3. **Per-function migration**:
     a. Edit `src/<file>.rs` annotations to pure Rust.
     b. `python3 hax.py extract` from `libcrux-ml-kem/`.
     c. Snapshot SHAs, touch unchanged `.checked` files.
     d. `make` from `proofs/fstar/extraction/`.  Verify the
        target function's `.fst[i]` still loads and verifies.
     e. Verify spec modules still build (run
        `make /Users/karthik/libcrux-trait-opacify/.fstar-cache/checked/Hacspec_ml_kem.*.fst.checked`
        to confirm no regression).
     f. Commit with `agent-mlkem:` prefix.
  4. **Cap**: 4-5 functions or 4 hours per session, whichever first.

## End-of-session deliverable

Report at `proofs/agent-status/session-<date>-<suffix>.md`:

  - Functions migrated (file:line, before/after pre/post snippet,
    which Pattern (A/B/C) was used).
  - New content in `/specs/ml-kem/src/` (if any — should be rare;
    add only when forced).
  - F\* perf delta on affected modules (cold vs warm, max rlimit used).
  - Final commit SHA.
  - Pattern findings: did Pattern A/B/C work?  Any new gotchas?
  - **Self-audit (R10 + R11)**: did you create any wrapper, any
    `unfold let` alias over Spec.MLKEM, any new
    `Hacspec_ml_kem.<top-level>.fst` file, any new `fstar!` escape
    in ind_cpa/ind_cca annotations?  If yes: violated the rules,
    revert.

Push policy: see R1 (branch is already pushed; further pushes on
this branch are OK, force-pushes / PRs / pushes to main are not).
DO NOT touch `~/libcrux-ml-dsa-proofs` or `~/libcrux-sha3-focused`.
