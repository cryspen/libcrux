# Agent prompt — libcrux-ml-kem-proofs, post-cleanup-phase session

Paste this into a fresh Claude Code session opened in
`~/libcrux-trait-opacify/libcrux-ml-kem` (auto mode recommended).

You are a single-lane agent for the libcrux-ml-kem F\* verification effort.

## Read first (in order)

  1. `proofs/agent-status/AUDIT-2026-05-01.md` — audit of the
     2026-05-01 wrapper-namespace anti-pattern.  Establishes R10
     (no wrappers, no namespace squatting) which still applies.
  2. `proofs/agent-prompt-clean-restart.md` — the original clean-restart
     mandate.  Still authoritative.  Contains R1-R10, the
     Spec.MLKEM→Hacspec mapping table, and the workflow.
  3. `proofs/agent-status/session-2026-05-01-clean-restart.md` —
     session report through commit `098043966` (6 functions migrated,
     `cpa_ciphertext_size` + `rank_to_params` added to spec).
  4. The five cleanup commits' messages (`git log --format=full
     -p e8b51b409..142238341 -- libcrux-ml-kem/src/vector/`):
       - `e8b51b409` — spec helpers (`is_rank`, `FieldElement::from_i16`)
       - `9ffc850db` — `generate_keypair` migration (1st function-call ensures)
       - `60af8d332` — **lift functions: F* injection → Rust** (read this in detail)
       - `703037930` — commute lemmas adapted to new extracted signatures
       - `142238341` — documentation: why pure-Rust `to_int().rem_euclid()`
                        ensures doesn't bridge to F* `v x % q`

## Branch state at session start

```
$ git log --oneline -7
142238341 doc — why pure-Rust to_int().rem_euclid() ensures doesn't work
703037930 cleanup — adapt commute lemmas to Rust-extracted lift signatures
60af8d332 cleanup — promote impl→spec lift functions from F* injection to Rust
e8b51b409 specs/ml-kem — add is_rank + FieldElement::from_i16 helpers
098043966 update session report — 6th function (generate_keypair) migrated
9ffc850db migrate generate_keypair off Spec.MLKEM (6th function)
9dce36d6b specs/ml-kem — add rank_to_params adapter for Hacspec function calls
```

Branch: `libcrux-ml-kem-proofs`.  Tip: `142238341`.

## Architecture (key facts as of `142238341`)

### Spec helpers (`/specs/ml-kem/src/parameters.rs`)

  * `is_rank(rank: usize) -> bool` — `rank ∈ {2, 3, 4}`.
  * `rank_to_params(rank: usize) -> MlKemParams` — adapter for
    `MlKemParams`-shape Hacspec functions (e.g.
    `Hacspec_ml_kem.Ind_cca.generate_keypair`).
  * `cpa_ciphertext_size(rank: usize) -> usize` — rank-generic
    ciphertext size (`Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE` migration target).
  * `FieldElement::from_i16(v: i16) -> FieldElement` — Euclidean lift.

### Impl→spec lift functions (single source of truth, all Rust)

In **`libcrux-ml-kem/src/vector/traits.rs::spec`** (extracts to
`Libcrux_ml_kem.Vector.Traits.Spec`):

  * `i16_to_spec_fe(x: i16) -> FieldElement`  — plain-domain lift
  * `mont_i16_to_spec_fe(x: i16) -> FieldElement` — Montgomery lift
  * `i16_to_spec_array<const N>(x: &[i16; N]) -> [FE; N]`
  * `mont_i16_to_spec_array<const N>(x: &[i16; N]) -> [FE; N]`
  * `zetas_1(z0)`, `zetas_2(z0,z1)`, `zetas_4(z0..z3)` — extract as
    `zetas_1_`, `zetas_2_`, `zetas_4_` in F* (hax digit-suffix mangling).
    Commute lemmas already cite the trailing-`_` form.

In **`libcrux-ml-kem/src/vector.rs::spec`** (extracts to
`Libcrux_ml_kem.Vector.Spec`):

  * `poly_to_spec<V: Operations>(p: &PolynomialRingElement<V>) -> [FE; 256]`
  * `vector_to_spec<const RANK, V>` and `matrix_to_spec<const RANK, V>`

### Generic F* helpers

  * `Hacspec_ml_kem.Commute.ProofUtils.map_array` — pure F* generic
    array-map.  Marked `TODO(upstream-to-hax-lib)` in the file's header.

### `fstar!` escape hatch — current usage policy

The cleanup mandate says: **no `fstar!` escape hatch in
`src/ind_cpa.rs` or `src/ind_cca.rs` annotations** (the `requires` /
`ensures` attributes).  Replace with pure-Rust expressions citing
`hacspec_ml_kem::parameters::*` (`is_rank`, `rank_to_params(K)`,
`MlKemParams::*` methods, `cpa_ciphertext_size`),
`crate::vector::spec::*` (`poly_to_spec`, `vector_to_spec`,
`matrix_to_spec`), `crate::vector::traits::spec::*`
(`i16_to_spec_fe`, etc.), `crate::polynomial::spec::*`
(`is_bounded_poly`, etc.).

**Documented exception**: `i16_to_spec_fe` and `mont_i16_to_spec_fe`
themselves keep `hax_lib::ensures(fstar!(...))` because:

  - The semantics is `v r.f_val == v x % 3329` (F* native).
  - Pure-Rust `r.val.to_int() == x.to_int().rem_euclid(3329.to_int())`
    extracts to `Hax_lib.Int.t_Int` + `impl_Int__rem_euclid` calls.
  - Z3 doesn't auto-bridge those forms; commute bridges that
    previously had `()` proofs went from <1s to >100s/query and
    wedged the build.
  - Sticking with `fstar!` for these two ensures **is allowed**.
    Migrate only after the `Hax_lib.Int`-vs-native-int bridging is
    solved (probably via SMTPat lemmas in
    `Hacspec_ml_kem.Commute.ProofUtils`).

### Commute lemmas (in `specs/ml-kem/proofs/fstar/commute/`)

Adapted to the new Rust-extracted signatures (commit `703037930`):

  * `i16_to_spec_array (T.f_repr r)` → `i16_to_spec_array (sz 16) (T.f_repr r)`
    (~144 references; explicit positional `(v_N: usize)` from const-generic
    extraction).
  * Two generic-`n` lemmas (`lane_plain`, `lane_mont`, `mont_array_lane`
    in `Chunk.fst`) pass the local `n` instead of `(sz 16)`.
  * `zetas_1`/`zetas_2`/`zetas_4` → `zetas_1_`/`zetas_2_`/`zetas_4_` (~57 refs).

Don't re-rename or revert these — both directions break Rust extraction.

### Build state

```
$ cd libcrux-ml-kem/proofs/fstar/extraction
$ make
... 4 modules verify clean (Vector.Traits.Spec, Vector.Traits,
    Commute.Chunk, Commute.Bridges) plus the Hacspec dep closure.
... fails at Libcrux_ml_kem.Ind_cca.fsti(165):
    Module name Spec.MLKEM could not be resolved
    (encapsulate's `requires` cites Spec.MLKEM size constants).
```

This is a **pre-existing blocker** (predates this session's cleanup).
The user has indicated they'll fix it via "additional conditions" in
the .fsti requires/ensures rather than a full migration.  Don't
attempt a full migration of `encapsulate` unless the .fsti blocker
is still present after a `git pull` of the user's fix.

## Open work (priority order)

### 1. Verify the Ind_cca.fsti:165 blocker is still pending

```
cd libcrux-ml-kem/proofs/fstar/extraction
make 2>&1 | grep -E '\* Error' | head -3
```

If still fails at `Ind_cca.fsti(165)`: ask the user whether to
proceed with their planned fix, or pivot to one of the items below.

If it now passes: the next blocker will surface immediately
downstream.  Likely candidates: `decapsulate`, then libcrux's
`fstar!` escapes citing the old polynomial-lift names (item 2 below).

### 2. Migrate libcrux-side `fstar!` escapes off old polynomial-lift names

The lift-function cleanup (`60af8d332`) renamed the polynomial-level
lifts and moved them to a different F* module:

  * `Libcrux_ml_kem.Vector.to_spec_poly_t #_ p` → `Libcrux_ml_kem.Vector.Spec.poly_to_spec p`
  * `Libcrux_ml_kem.Vector.to_spec_vector_t #_ #_ v` → `Libcrux_ml_kem.Vector.Spec.vector_to_spec v`
  * `Libcrux_ml_kem.Vector.to_spec_matrix_t #_ #_ m` → `Libcrux_ml_kem.Vector.Spec.matrix_to_spec m`

These are cited in:

  * `libcrux-ml-kem/src/ind_cpa.rs` (~5 sites in `fstar!()` blocks)
  * `libcrux-ml-kem/src/ind_cca.rs` (~10 sites)
  * `libcrux-ml-kem/src/ntt.rs` (commented out — ignore)

Per the cleanup mandate, do these as part of the per-function
pure-Rust conversion (item 3) rather than as in-place text
replacements.  Each `fstar!()` block gets rewritten as a pure-Rust
expression that calls `crate::vector::spec::poly_to_spec(p)` etc.

### 3. Per-function pure-Rust annotation conversion of `ind_cpa.rs`

The original user mandate.  Pick ONE function at a time:

  - Convert `#[hax_lib::requires(fstar!(r#"..."#))]` to pure Rust.
  - Convert `#[hax_lib::ensures(...)]` similarly.
  - Convert any inline `hax_lib::fstar!(...)` body assertions in the
    function (these are harder; some may need to stay as `fstar!`
    if they cite F*-only constructs).

Mechanical patterns:

  ```
  Spec.MLKEM.is_rank $K           →  hacspec_ml_kem::parameters::is_rank(K)
  Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K
                                  →  hacspec_ml_kem::parameters::rank_to_params(K).ek_size()
  Spec.MLKEM.v_CCA_PRIVATE_KEY_SIZE $K
                                  →  hacspec_ml_kem::parameters::rank_to_params(K).dk_size()
  Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE $K
                                  →  hacspec_ml_kem::parameters::cpa_ciphertext_size(K)
  Spec.MLKEM.v_SHARED_SECRET_SIZE →  hacspec_ml_kem::parameters::hash_functions::H_DIGEST_SIZE
  Libcrux_ml_kem.Vector.to_spec_poly_t #$:Vector p
                                  →  crate::vector::spec::poly_to_spec(p)
  is_bounded_poly (sz 3328) p     →  crate::polynomial::spec::is_bounded_poly(3328, p)
  forall (i:nat). i < v $K ==> P
                                  →  hax_lib::forall(|i: usize| hax_lib::implies(i < K, P))
  ```

For functions whose ensures cites a function-call form (e.g.
`Spec.MLKEM.ind_cpa_encrypt`), use `rank_to_params(K)` to bridge to
the `MlKemParams`-shape Hacspec.  See `generate_keypair` in
`src/ind_cca.rs:200-247` (commit `9ffc850db`) for the pattern —
match-on-Result for the return-type reshape.

For symbols that don't have a Hacspec equivalent (e.g.
`v_T_AS_NTT_ENCODED_SIZE`, `v_C1_SIZE`, `v_C2_SIZE`,
`v_VECTOR_U_COMPRESSION_FACTOR`, `v_VECTOR_V_COMPRESSION_FACTOR`,
`v_C1_BLOCK_SIZE`, `v_ETA2`, `v_ETA2_RANDOMNESS_SIZE`), follow
**workflow step 4** from the clean-restart prompt: ADD the helper to
`/specs/ml-kem/src/parameters.rs`, re-extract, then migrate the
consumer.  Cap-friendly: ~8 such helpers cover the encapsulate
requires entirely.

### 4. Per-function pure-Rust annotation conversion of `ind_cca.rs`

Same recipe as item 3.  This file has the function-call ensures
patterns more often; expect to use `rank_to_params(K)` heavily.

### 5. Re-evaluate `Hacspec_ml_kem.Parameters.Sizes` removal

The audit-grandfathered exception.  Once items 3 + 4 are done, every
`Parameters.Sizes.*` consumer should be migrated to the canonical
`MlKemParams::*` methods or the new `/specs/ml-kem/src/parameters.rs`
free functions.  At that point: delete
`specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Parameters.Sizes.fst`.

### 6. Defer / out-of-scope

  - Bridge proofs in commute/ rewriting against `Hax_lib.Int.t_Int`
    form (would let us migrate `i16_to_spec_fe`/`mont_i16_to_spec_fe`
    ensures off `fstar!`).  Substantial refactor.
  - Upstreaming `map_array` from `Hacspec_ml_kem.Commute.ProofUtils`
    to hax-lib's F* proof-libs.  Requires hax-lib PR.

## Hard rules (R1-R11)

  R1  Branch `libcrux-ml-kem-proofs`.  Already pushed to
      `origin/libcrux-ml-kem-proofs` (set as upstream).  You MAY
      `git push` further commits on this branch, but DO NOT
      force-push, DO NOT push to `main`, and DO NOT open a PR
      without explicit user authorization.
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
      it MAY be edited (it's the lift-functions module).
  R8  No `fstar-mcp` (per `feedback_use_fstar_mcp` and
      `feedback_fstar_mcp_session_dies_after_make`).
  R9  Commit prefix `agent-mlkem:`.  Commit Rust-spec changes
      separately from libcrux-side changes (per the original
      workflow step 4).
  R10 No wrappers.  No namespace-squatting.  No new F* specs in
      `Hacspec_ml_kem.*` (per the FORBIDDEN section of the
      clean-restart prompt).
  R11 **Cleanup-phase**: no `fstar!` escape in `src/ind_cpa.rs` /
      `src/ind_cca.rs` annotations.  The `vector::traits::spec`
      lift-function ensures may keep `fstar!` until the Hax_lib.Int
      bridge is solved (see "fstar! escape hatch policy" above).

## Workflow

  1. **Verify state**: branch is `libcrux-ml-kem-proofs`, tip `142238341`,
     `make` from `proofs/fstar/extraction/` reproduces the
     `Ind_cca.fsti:165` blocker (or whatever the user's fix moved
     it to).
  2. **Pick ONE task** from the open-work list.  Smallest-coherent-
     unit principle.
  3. For **per-function migration**:
     a. Edit `src/<file>.rs` annotations to pure Rust.
     b. `python3 hax.py extract` from `libcrux-ml-kem/`.
     c. Snapshot SHAs, touch unchanged `.checked`.
     d. `make` from `proofs/fstar/extraction/`.  Verify the
        target function's `.fst[i]` still loads and verifies.
     e. Verify commute lemmas still build (run
        `make /Users/karthik/libcrux-trait-opacify/.fstar-cache/checked/Hacspec_ml_kem.Commute.Bridges.fst.checked`
        after re-extract; should re-replay hints fast).
     f. Commit with `agent-mlkem:` prefix.
  4. For **adding a `/specs/ml-kem/src/` helper** (workflow step 4):
     a. Edit `/specs/ml-kem/src/parameters.rs` (or other spec file).
     b. Commit Rust-spec change SEPARATELY from the consumer migration.
     c. Re-extract, verify the new symbol appears in the extracted
        `Hacspec_ml_kem.Parameters.fst`.
     d. Then do the consumer migration as item 3.
  5. **Cap**: 4-5 functions or 4 hours per session, whichever first.
  6. After EACH milestone: optionally update
     `proofs/agent-status/session-<date>.md` with a per-function
     before/after snippet.

## End-of-session deliverable

Report at `proofs/agent-status/session-<date>-<suffix>.md`:

  - Functions migrated (file:line, before/after pre/post snippet).
  - New content in `/specs/ml-kem/src/` (if any).
  - F* perf delta on affected modules (cold vs warm, max rlimit used).
  - Final commit SHA.
  - **Self-audit (R10 + R11)**: did you create any wrapper, any
    `unfold let` alias over Spec.MLKEM, any new
    `Hacspec_ml_kem.<top-level>.fst` file, any new `fstar!` escape
    in ind_cpa/ind_cca annotations?  If yes: violated the rules,
    revert.

Push policy: see R1 (branch is already pushed; further pushes on
this branch are OK, force-pushes / PRs / pushes to main are not).
DO NOT touch `~/libcrux-ml-dsa-proofs` or `~/libcrux-sha3-focused`.
