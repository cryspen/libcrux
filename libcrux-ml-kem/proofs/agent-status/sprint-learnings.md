# Sprint Learnings — synthesis of two parallel proof-progress audits

Two independent audits were performed today (2026-04-30) on the
libcrux proof state across ML-KEM (`trait-opacify`), ML-DSA
(`ml-dsa-proofs`), and SHA-3 (`sha3-proofs-focused`). This document
synthesizes both, calling out where they agree, where one filled a
gap the other missed, and where they disagreed.

These learnings are **load-bearing for the next sprint plan** and
are referenced from the per-crate agent prompts at
`proofs/agent-prompt-{ml-kem,ml-dsa,sha3}.md`.

## Agreement (4 learnings — both audits independently arrived at)

### A1. Extraction is the foundational gate

Both audits identified that the proof state is bottlenecked at the
**API surface**, not the math layer. The crypto cores are largely
verified — what's missing is the API extraction:

- SHA-3: `lib.rs` filtered out of hax → 6 top-level digest fns
  (sha224/256/384/512, shake128/256) show as Unverified despite
  `Hacspec_sha3.{Keccak_f, Sponge}` being fully proven below.
- ML-KEM: `mlkem.rs` filtered out → 19+ KEM API fns Unverified
  despite the entire crypto core being verified.
- ML-DSA: `lib.rs` enters the inventory as Unverified on the SHA-3
  branch.

**Sprint action**: fix hax extraction config for `lib.rs` /
`mlkem.rs` BEFORE any new spec/proof work. ~1 session per crate.
Highest LOC-of-impact-per-hour available.

### A2. Tier counts undercount when proofs live outside function-level ensures

The `generate_verification_status.py` script classifies fns by
inspecting their `#[ensures(...)]` text. It misses:

- SHA-3's `keccakf1600` permutation, proven equivalent to
  `Hacspec_sha3.Keccak_f.keccak_f` via separate
  `EquivImplSpec.Keccakf.{Portable, Avx2, ChiFold}.fst` lemmas
  (~6,848 LOC of equivalence proofs invisible to the script).
- ML-KEM's `invert_ntt_montgomery`, whose ensures cites
  `Hacspec_ml_kem.Invert_ntt.ntt_inverse_butterflies` — but body is
  admitted (USER-15). Script reports Lax, but the SPEC is correct;
  only the proof is the gap.
- ML-KEM's body-admit functions where the post is hacspec-shaped
  but the body has `--admit_smt_queries true`.

**Sprint action**: when designing new proofs, prefer **function-level
ensures over external `EquivImplSpec.*` lemmas** unless there's a
structural reason for the external form. Surface existing external
lemmas (e.g., SHA-3's keccakf equivalence) as function-level ensures
so the audit/reporting story matches reality (~1 session per fn).

### A3. Spec module design must precede ensures wiring

ML-DSA cannot be "proven correct vs hacspec" because
`Hacspec_ml_dsa.{Ntt, Encoding}.*` does not exist — there's nothing
to cite. The bounds-only ensures on ml-dsa NTT are not a proof gap;
they're a **spec gap**. Conversely, ML-KEM's progress was unblocked
by `Hacspec_ml_kem.Commute.{Bridges, Chunk}.fst` (3,504 LOC of
hand-written spec) being designed first.

**Sprint action**: dedicate the first ~1 sprint per ml-dsa milestone
*tier* to designing the spec module (`Hacspec_ml_dsa.Ntt.*`,
`Hacspec_ml_dsa.Encoding.*`). No ensures wiring on a function until
the spec it would cite exists.

### A4. `VERIFIED_MODULES` / `ADMIT_MODULES` discipline is undervalued

ML-DSA's audit found 119 functions sitting in admit-by-Makefile-
exclusion that already had proper ensures and just weren't on
`VERIFIED_MODULES`. ML-KEM still has `Ind_cpa.fst` with all 21 fns
Lax for the same reason (whole module on the admit list).

**Sprint action**: every sprint kickoff should audit
`ADMIT_MODULES` / `VERIFIED_MODULES` first. Often dozens of fns
become Verified by Makefile-discipline alone, no proof work needed.

## Complementary insights (each audit caught something the other missed)

### Audit 2 caught (incorporated into the prompts)

**B1. Forward NTT is THE next high-leverage trait-opacify application
(ML-KEM).** Bounds-only ensures already exist on `ntt_at_layer_*`;
the hacspec citations are commented out as TODO. Adding the citation
propagates through Portable + Avx2 backends for free, mirroring the
+27 / +23 hacspec gain the inverse direction got from the same
pattern. Audit 1 had this as priority #4 of many; Audit 2 elevates
it to *the* Week 2-3 deliverable.

**B2. Per-fn tier-transition reports** (lax→PF, PF→math, bounds→
hacspec, etc.). Current script's net deltas can show "Δ Bounds = −9"
when actually 9 fns moved Bounds→Hacspec — the upgrade looks like
regression in the per-tier net. Fix: instrument the script to
preserve per-fn matching across two snapshots and report
transitions, not just aggregated deltas.

**B3. Avoid big-axiom-bridge designs.** The
`Hacspec_ml_kem.Serialize.HacspecBridge` approach was abandoned
after 11 commits on `agent/phase-7c-serialize`. Wave-B took the
per-width `panic_free` strategy and that's what produced the actual
gains (USER-9a/b: widths 5+11 done). Lesson: when tempted to write
a "general" bridge axiom that connects layer N+1 to layer N for all
instances at once, don't. Pick one width / one instantiation, prove
that, generalize only after the second falls into the same shape.

**B4. Cross-pollination inflates per-branch metrics if you sum
naively.** ML-KEM branch's "hand-written F\* of 5,988 LOC" includes
~2,484 LOC of SHA-3 team's specs that landed via merges; ML-DSA
included 1,166 LOC of ML-KEM team's `Commute.Chunk`. Without
filtering, "lines I wrote" gets credited to whoever's branch was
rebased latest. Fix: attribute work by `path × branch-of-origin`,
or restrict the metric to `specs/<crate>/` and
`proofs/fstar/equivalence/` only.

### Audit 1 caught (incorporated into the prompts)

**C1. Rule SD4 — no GLOBAL `reveal_opaque (\`%P) (P)` in loop bodies.**
A single line in `invert_ntt_at_layer_2` caused a 153 s top-1 wall;
removing it dropped the verification to 2.1 s. Same fix on layer_3
dropped the rlimit from 800+context_pruning+split_queries to 400.
Pre-flight grep:
`grep -rn 'reveal_opaque.*%[^)]*) *([A-Z][A-Za-z_.]*) *)$' src/`

**C2. Hint-cache cascades on ensures upgrades.** Strengthening one
fn's ensures shifts line numbers and breaks downstream hint replay.
Saw this on layer_3 (rlimit 200 → 400 needed after layer_2's line
shift) and `Vector.Avx2.fst::impl_3` (had to delete the hint file
entirely). After every milestone closure that strengthens an ensures,
re-record hints for the module + at least one consumer.

**C3. Hax codegen fragility.** Three recurring issues that re-emerge
after every `python3 hax.py extract`:
- Duplicate `noeq` on `Vector.Neon.Vector_type.fsti` (gitignored;
  needs `sed -i '' '7,8d'`).
- Trailing `_` mangling on F\* segments whose Rust ident ends in a
  digit (`ml_dsa_44` → `Libcrux_ml_dsa.Ml_dsa_44_.fst`).
- Ancestor coverage when nested mods extract to multiple `.fst`.

Long-term: invest 1 session in a robust extraction post-processor.

**C4. Cross-crate parallelism is genuine.** Three independent
worktrees with no contention between branches; agents in parallel
sessions can run independently.

## Disagreements / different emphasis

| Topic | Audit 1 | Audit 2 | Resolution |
|---|---|---|---|
| **Sprint kickoff sequence** | Audit existing code (SD4 reveal_opaque sweep, codegen workarounds) | Extraction config first (lib.rs / mlkem.rs), THEN spec/proof work | **Audit 2 wins.** Extraction is foundational and ~1 session per crate; SD4 audit is incremental. Lead with extraction. |
| **"Hacspec = highest tier" is the right metric** | Yes, that's what the script tracks | Net per-tier counts can mask within-tier upgrades; need per-fn transitions | **Audit 2 wins.** Net deltas mislead — Bounds→Hacspec shows as "Δ Bounds = −1, Δ Hacspec = +1", looks like wash. Per-fn transition tracking is the real fix. |
| **Cheapest next milestone** | Layer_2 hacspec upgrade (closed today, commit `4672cc005`) | Surface SHA-3 EquivImplSpec lemmas as function-level ensures; mlkem.rs / lib.rs extraction | **Both right for different sessions.** Layer_2 was cheapest for ml-kem alone; Audit 2's are cheapest cross-crate. |
| **Big-axiom-bridge** | Documented `agent/phase-7c-serialize` as "abandoned" | Drew the forward-looking lesson | **Audit 2 wins.** Codify as an anti-pattern (AP-2 in the prompts). |

## Recommended next-sprint sequence (synthesized)

  - **Day 1**: VERIFIED_MODULES / ADMIT_MODULES audit on ML-KEM
    (Ind_cpa.fst) + ML-DSA. Cheap, mechanical.
  - **Day 2**: Extract `lib.rs` (sha3) and `mlkem.rs` (kem) — the
    biggest mechanical move available. Closes dozens of fns from
    Unverified to at-least-PF.
  - **Day 3-5**: Surface SHA-3's `EquivImplSpec.Keccakf.*.fst`
    lemmas as function-level ensures (3-5 functions). Audit picks up
    the real proof state.
  - **Week 2**: Design `Hacspec_ml_dsa.Ntt.*`. No ensures wiring on
    ML-DSA NTT until this lands.
  - **Week 2-3**: ML-KEM forward NTT trait-opacification (mirror the
    pattern that worked for inverse NTT layers 1, 3).
  - **Week 3**: Instrument `generate_verification_status.py` to
    report per-fn transitions (lax→PF, PF→math, bounds→hacspec)
    instead of just net-per-tier counts.

## Memory-store candidates from this synthesis

Two new feedback memories proposed:

  1. **`feedback_extraction_first`** — Always audit hax extraction
     config (`hax.py`/`hax.sh` `-i` rules) before any spec wiring
     sprint. Filtered-out modules (`lib.rs`, `mlkem.rs`,
     `ind_cca/incremental*.rs`) are worse than admitted modules —
     they have no proof of any kind, including panic-freedom. Fix
     extraction first; the API surface flips from Unverified to
     at-least-PF mechanically.

  2. **`feedback_hacspec_spec_first`** — `Hacspec_<crate>.<Layer>.*`
     spec module design MUST precede function-level ensures citing
     it. Bounds-only ensures are not a proof gap; they're a spec
     gap. Don't add `Hacspec_ml_dsa.Ntt.foo` citations to a function
     before the spec exists. Path: define spec → test it's well-formed
     → wire ensures → prove.

Existing memories that this audit confirmed are still load-bearing:
SD3/SD4, lane split, reveal_opaque targeting, fstar-mcp session
lifecycle, touch-unchanged-`.checked`, no-cache-nuke,
for-loop-param-unshadowing, drive-to-the-top spike.

---

## Cross-sprint deltas (appended 2026-04-30 from ml-dsa-proofs)

Source: `~/libcrux-ml-dsa-proofs/libcrux-ml-dsa/proofs/agent-status/cross-sprint-delta-2026-04-30.md`
(commit `c38294d8e` on `ml-dsa-proofs`).

### AP-4 (cross-sprint): `bits USIZE` opacity

The hax proof-libs `.fsti` keeps
`Rust_primitives.Integers.bits Rust_primitives.Integers.USIZE`
opaque. Z3 cannot derive `v x < bits USIZE` from `v x < 64` under
`fuel 0`, and `assert_norm` does not unfold it either.

**Affects ml-kem**: any `1 << shift_amount` on a usize. Spot
candidates: `compress.rs` width-`d` packing, `polynomial.rs` lane
indexing, `serialize.rs` bit-position math.

**Mitigation**: tighten the shift bound (`< 8`) so the obligation
falls into a different proof path; or admit the module rather than
detour into proof-libs.  **Do NOT** add
`assert_norm (bits USIZE == 64)` — it doesn't help.

First observed: ml-dsa `Shuffle_table` promotion attempt (`9da124ba5`).

### AP-5 (cross-sprint): `assert_norm` for arithmetic constant chains with subtraction

When a constant extracts to F* via a chain that includes a
subtraction step, plain `assert (v $C == K)` fails under `fuel 0`
even though Z3 can compute the value. Use `assert_norm`.

**Affects ml-kem**: candidates include `BYTES_PER_RING_ELEMENT`
(`COEFFICIENTS_IN_RING_ELEMENT * d / 8`),
`RANKED_BYTES_PER_RING_ELEMENT`, the `C1_SIZE` /
`C1_BLOCK_SIZE` family in `mlkem*.rs`. When a "Z3 can't prove
`v $CONST == K`" failure shows up on a known constant, swap to
`assert_norm` first.

First observed: ml-dsa
`Encoding.Verification_key.generate_serialized` (`5d32e16df`).

### Makefile structure: ML-KEM already on ADMIT-allowlist

ML-DSA flipped from `VERIFIED_MODULES` denylist to ML-KEM-style
`ADMIT_MODULES` allowlist (`74922609a`). **No action for ml-kem** —
already on the allowlist pattern. Today's milestone #0 added 8 new
entries with explicit one-line reasons, consistent with the pattern.

### Agent-prompt freshness — recommended audit pass

ml-dsa's prompt had a factually wrong "design Hacspec_ml_dsa.Ntt
from scratch" claim when 4318 lines of `Hacspec_ml_dsa.*` already
existed. Fixed in `2420f7555`. **For ml-kem**: run the same 5-step
audit on `proofs/agent-prompt-ml-kem.md` (~30 min):

  1. Grep for "design", "create", "scaffold" + spec-module names;
     check whether the spec already exists.
  2. Add an "Existing spec inventory" near the top (file paths +
     line counts of `specs/ml-kem/proofs/fstar/extraction/Hacspec_ml_kem.*`
     and `specs/ml-kem/proofs/fstar/commute/`).
  3. Add a "Recently closed (do not redo)" section — recent commits
     and what they accomplished.
  4. Replace any "rebuild from scratch" guidance with "grep first,
     design only if missing".
  5. Drop tip-SHAs from prompts; point at a maintained handoff doc.

### Encoding-wrapper closure recipe (transferable to ml-kem)

Pattern from ml-dsa `Verification_key.generate_serialized` (`5d32e16df`):

```rust
pub(crate) fn serialize<...>(input: &[T], ..., output: &mut [u8]) {
    output[0..PREFIX_SIZE].copy_from_slice(prefix);
    for i in 0..input.len() {
        let offset = PREFIX_SIZE + i * CHUNK_SIZE;
        callee::serialize(&input[i], &mut output[offset..offset + CHUNK_SIZE]);
    }
}
```

Closure recipe:
  1. Hoist `input.len()` to a nameable binding so it can appear in
     `loop_invariant!`.
  2. `loop_invariant!` carries `v i <= input_len`,
     `input_len <= MAX`, length identity on `output`, and the
     per-element forall from the function's `requires`.
  3. `assert_norm (v $CHUNK_SIZE == <literal>)` if the constant
     extracts via a subtraction chain (AP-5).
  4. Offset-arithmetic asserts: `v i < v $input_len`,
     `v i * <chunk> <= (MAX - 1) * <chunk>`,
     `(v i + 1) * <chunk> <= v $input_len * <chunk>`.
  5. `--z3rlimit 400 --split_queries always --fuel 0 --ifuel 1`.

**ML-KEM application targets** (proof_milestones.md):
  - Row 11 `compress_then_serialize_message`
  - Row 15 `compress_then_serialize_ring_element_u/v`
  - Row 16 `deserialize_then_decompress_ring_element_u/v`
  - Row 17 `compress_d`/`decompress_d` chunk wrappers (USER-13's
    walled portion)

Variable to watch: whether the per-element forall is opaque-predicate
style (easier) vs expanded triple-forall (harder; more rlimit).

### Optional: shared anti-pattern catalog

AP-N text is currently inlined in each per-sprint agent prompt;
drift is real (AP-2 in three places = three update sites). Optional
move: top-level `anti-patterns.md` as the single source, per-sprint
prompts cite by number + first-observed-in commit. Minor maintenance
win; defer until AP-N count grows past 6.

---

## ML-KEM-side learnings to mirror back (2026-04-30, milestone #0)

These emerged from today's `incremental` cargo-feature extraction
work (commit `86c48def7`). Generalizable to ml-dsa / sha3 if they
hit similar feature-gated submodules.

### Hax `-i` filters don't bind cited-but-excluded submodules

Filter `-libcrux_ml_kem::ind_cca::incremental::multiplexing::alloc::**`
did NOT prevent `Libcrux_ml_kem.Ind_cca.Incremental.Multiplexing.Alloc.fst`
from being written, because the parent `multiplexing.rs` cites
`alloc::*` symbols. Hax extracts a stub of the excluded module to
satisfy the citation.

**Fallback**: post-extraction `os.remove()` of the offending files,
added to `hax.py` after the patch-apply step. Coupled with a
`Makefile` admit if the parent module survives.

### `Rand_core.f_try_fill_bytes` lacks an F* model

The hax proof-libs F* model for `rand_core::RngCore` only binds
`f_fill_bytes` (infallible variant). Code calling
`rng.try_fill_bytes(...)` extracts to `Rand_core.f_try_fill_bytes`
which is undefined → Error 72. The `.Incremental.Rand` modules
delete-after-extract is the workaround until the proof-lib gains
the binding.

If ml-dsa or sha3 add randomness wrappers, prefer `fill_bytes`
over `try_fill_bytes` for any code path that hax extracts.

### `not(hax)` mirroring at use-sites

When a `mod foo { ... }` is gated `cfg(all(feature = "X", not(hax)))`,
ALL `use foo::...` statements at consumers must mirror the same
`not(hax)`, with a fallback path under `cfg(hax)`. Otherwise the
hax build fails E0432 unresolved import. Today's fix:
`src/ind_cca/incremental/multiplexing.rs` lines 17, 19, 45, 47.

**Audit candidate for ml-dsa / sha3**: grep for
`#\[cfg(all(.*not(hax).*))\] *mod` and verify all `use <that-mod>::`
sites have a parallel guard. ~5 min per crate.

### Verification-status script: macro-defined fns under-counted

The `mlkem.rs` macros (`impl_incr_key_size!`, `impl_incr_platform!`)
extract as `Mlkem*.Incremental.fst` files (per-variant macro
expansions), not `Libcrux_ml_kem.Mlkem.fst`. The script's `mlkem*`
group still reports 36 macro-defs as `Unv: 36` because no
`.Mlkem.fst` exists. The actual fns are extracted, just under
variant paths.

**Future scope** for the verification-status script:
follow-macro-instantiation logic, or a config-side
"`mlkem.rs` instantiates into Mlkem512.Incremental + ..." mapping.
Affects any crate that uses macro-based per-variant code generation.

### Inverse → forward NTT pattern transfer is empirically robust

Three forward NTT layers (1, 2, 3) closed first-try in one session
(commits `c32653051`, `744b15937`, `0ea02c19e`) by mirroring the
inverse-direction commits (`8358b1093`, `b7b49c358`+`4672cc005`,
`fa2151ea8`+`43c9d45d5`) component-by-component.

**Invariants** that hold across the inverse → forward transfer:
  - **Lane assignment per branch is identical**: forward and
    inverse layer-N trait `branch_post`s share the same
    base/off/i1/j1/i2/j2 indexing.  Per-branch lane bridges port
    over directly; only the per-lane FE equation differs.
  - **Bridge structure is identical**: per-lane unfold helper +
    per-branch-or-direct lane bridge + per-vector wrapper with
    `Classical.forall_intro` + `Seq.lemma_eq_intro`.
  - **Trait branch_post predicates already exist** at `traits.rs`
    for layers 1, 2, 3 (both directions).  No need to author new
    branch posts.

**The single material divergence**: forward butterfly
`(a + z*b, a - z*b)` requires asymmetric multiplication, vs
inverse `inv_butterfly (a + b, (a - b) * z)`.  Empirically this
needed `--z3rlimit 800 --split_queries always` on the per-lane
**wrapper** for forward layer 2 (vs 400 for inverse).  Other
positions (per-branch helpers, per-vector bridge) verified at the
same rlimit.

**Where the transfer breaks down (still open as of 2026-04-30)**:
  - **Layer 4_plus**: multi-step (4 calls in
    `ntt_binomially_sampled_ring_element`).  Inverse counterpart's
    body itself is admitted (USER-14).  Bridge would need
    `lemma_ntt_layer_int_vec_step_to_hacspec` mirroring
    `lemma_inv_ntt_layer_int_vec_step_reduce_to_hacspec` at
    `Bridges.fst:745`.  But strengthening
    `ntt_layer_int_vec_step`'s post and chaining 16 per-chunk-pair
    uses to a poly-level claim is the same gap that USER-14 is
    tracking for inverse.
  - **Layer 7**: between-chunk butterfly.  Single zeta in
    Montgomery form (-1600 in the impl); no
    `f_ntt_layer_7_step` trait function exists (the impl uses
    `multiply_by_constant_bounded` + `add_bounded`/`sub_bounded`
    directly, skipping the trait).  Bridge would need to identify
    `mont_lift(-1600) == zeta(1)` and chain 8 chunk-pair operations
    to a poly-level layer-7 claim.  Novel design.

**Recommendation**: layers 4_plus and 7 are NOT one-session tasks.
Treat them as separate USER-N items. Inverse 4_plus (USER-14) is
the unblocking work — solving it gives a template for forward
4_plus directly.
