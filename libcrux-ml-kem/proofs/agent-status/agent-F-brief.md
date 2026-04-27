---
agent: F
phase: 7b — NTT/Inv-NTT layers + INTT-Mont post strengthening
branch: agent/phase-7b-ntt
parent: trait-opacify (post-E2 merge)
worktree: yes
cap: 180 min total, 30 min hard cap on target #1, 45 min hard cap on the INTT-form post
---

# Agent F brief — Phase 7b NTT/Inv-NTT layers + INTT-Mont post

You are a focused F* proof specialist for libcrux-ml-kem.  Your job is
Phase 7b: above-trait NTT and Inv-NTT layers 1-3, **plus** strengthening
`invert_ntt_montgomery`'s post to expose the deferred FIPS-203 finalization
scaling that 3 of Phase 7a's held reduce functions consume.

## Context — what the audit established

The reference Kyber `pq-crystals/kyber/ref/ntt.c` line 106 documents
the constant `1441 = mont²/128` (i.e., `R² · 128⁻¹ mod q`).  The
reference's `invntt_tomont` applies a final pass `r[j] = fqmul(r[j], 1441)`
that fuses two operations: the FIPS-203 INTT's mandatory `· 128⁻¹ mod q`
finalization (Algorithm 9 line `f ← f · 3303 mod q`) AND the Mont-domain
adjustment.

**libcrux's `invert_ntt_montgomery` deliberately omits this final pass.**
After 7 layers of butterflies, output coefficients are in form
`f_real · 128 · R⁻¹ mod q`.  The `· 1441` mont_mul that the reference
applies as a final loop is instead fused into the next per-element
operation at each call site:

- `Polynomial::subtract_reduce`, `Polynomial::add_error_reduce`,
  `Polynomial::add_message_error_reduce` each begin with
  `mont_mul(b, 1441)`.  This applies the missing finalization AND
  converts to plain in one fused pass over the coefficients.
- `Polynomial::add_standard_error_reduce` uses `to_standard_domain
  (mont_mul by 1353 = R²)` instead, because its input doesn't come
  from INTT — it's a freshly-sampled binomial in `f · R⁻¹` form, no
  128 factor.

Phase 7a closed 2/6 above-trait Polynomial targets but had to
SKIP-WITH-COMMENT 4/6 because **`invert_ntt_montgomery`'s post today
is bounds-only**.  Without the post exposing the `f_real · 128 · R⁻¹`
input form, the 3 reduce functions can't prove their `mont_mul(b, 1441)`
recovers `f_real`.  This brief fixes that.

## Mission

Two intertwined deliverables:

### Deliverable A — INTT-Mont form post on `invert_ntt_montgomery`

**Critical: preserve opacity.**  The whole point of trait-opacify
(Phases 1-5) is that above-trait posts expose `forall_N (fun i -> opaque_lane_post v.[i] r.[i])`
shape — never naked mod arithmetic.  Adding raw `v r * R ≡ ... (mod q)`
conjuncts in `invert_ntt_montgomery`'s post would flood SMT context at
every above-INTT call site (just like `barrett_reduce_post`'s
opacity-wrapped body would do if exposed).  Match the existing
`barrett_reduce_post` / `add_post` style.

#### A1 — Opaque per-lane predicate (in `src/vector/traits.rs::spec` or a hand-written F* helper file)

```fstar
[@@ "opaque_to_smt"]
let intt_mont_form_lane (input_lane: i16) (hacspec_butterflies_lane: P.t_FieldElement) : prop =
  (v input_lane * R) % 3329 == ((P.f_val hacspec_butterflies_lane) * 128) % 3329
```

`hacspec_butterflies_lane` is the lane of the FIPS-203 INTT result
**before** the `· 3303` finalization (i.e., what
`pq-crystals/kyber/ref/ntt.c`'s butterflies-only stage produces; see
R10 about adding this helper to canonical hacspec).

The opaque body holds the raw mod arithmetic; the predicate name is
all callers see.

#### A2 — Per-chunk wrap (matches `forall16` pattern in trait posts)

```fstar
let intt_mont_form_chunk
    (input_chunk: t_Array i16 16)
    (hacspec_butterflies_chunk: t_Array P.t_FieldElement 16) : prop =
  Spec.Utils.forall16 (fun (i: nat {i < 16}) ->
    intt_mont_form_lane (Seq.index input_chunk i) (Seq.index hacspec_butterflies_chunk i))
```

`forall16` is `unfold let`, so this inlines to a 16-conjunction of
opaque atoms — exactly the per-chunk shape that `barrett_reduce_post`
and friends use today.

#### A3 — Strengthen `invert_ntt_montgomery`'s ensures

In `libcrux-ml-kem/src/invert_ntt.rs`, add ONE conjunct (poly-level
hacspec equation, no mod arithmetic visible):

```rust
#[hax_lib::ensures(|_|
    spec::is_bounded_poly(3328, &future(re))
    && fstar!(r#"
        let hacspec_butt = Hacspec_ml_kem.Invert_ntt.ntt_inverse_butterflies
                              (Hacspec_ml_kem.<some lift>(${input_re_snapshot})) in
        forall (k: nat). k < 16 ==>
          intt_mont_form_chunk
            (T.f_repr (Seq.index ${re}_future.f_coefficients k))
            (<chunk projection of hacspec_butt at k>)
    "#))]
```

Caller sites see `forall (k: nat). k < 16 ==> intt_mont_form_chunk ...`
— a structural `forall` over 16 opaque chunk predicates.  No raw mod
arithmetic above the trait boundary.

#### A4 — Reveal-on-demand inside Tier-2 lemmas

The Tier-2 commute lemmas in `Hacspec_ml_kem.Commute.Chunk.fst` and
the per-element commute lemmas in Phase 7a-finish can `reveal_opaque
(\`%intt_mont_form_lane)` when they need the mod equation.  Use
named-intro lemmas with dual-trigger `SMTPat`s where appropriate
(see `proof-style-guide.md` §3.2).

#### A5 — Loop-invariant strengthening across the 7 layer calls

Each of `invert_ntt_at_layer_1`, `_2`, `_3`, and the 4 calls to
`invert_ntt_at_layer_4_plus` carries forward partial INTT-Mont form
state.  Express each layer's post as an opaque-wrapped predicate of
the same shape.  The cumulative form at the end of all 7 layers is
what Deliverable A3 exposes.

If structuring the per-layer opaque predicates is non-trivial, factor
through a single intermediate predicate that names the cumulative
state, then introduce it once at the end via a named lemma.

### Deliverable B — Above-trait NTT/Inv-NTT layer post-strengthening

8 functions, 4 forward + 4 inverse:

Forward NTT (`src/ntt.rs`):
1. `ntt_at_layer_1` — calls `Vector::ntt_layer_1_step` 16x with 4 zetas/group
2. `ntt_at_layer_2` — calls `Vector::ntt_layer_2_step` 16x with 2 zetas/group
3. `ntt_at_layer_3` — calls `Vector::ntt_layer_3_step` 16x with 1 zeta/group
4. `ntt_at_layer_7` — final layer (single butterfly group)

Inverse NTT (`src/invert_ntt.rs`):
5. `invert_ntt_at_layer_1` — calls `Vector::inv_ntt_layer_1_step` 16x
6. `invert_ntt_at_layer_2` — calls `Vector::inv_ntt_layer_2_step` 16x
7. `invert_ntt_at_layer_3` — calls `Vector::inv_ntt_layer_3_step` 16x
8. `invert_ntt_at_layer_4_plus` — variable-step loop; if hard, skip-with-comment

Each function gets a strengthened post citing
`Hacspec_ml_kem.Ntt.ntt_layer_n` / `Hacspec_ml_kem.Invert_ntt.ntt_inverse_layer_n`
(check exact hacspec function names; see `specs/ml-kem/src/{ntt.rs,invert_ntt.rs}`).

## First target — `ntt_at_layer_1` (30-min cap)

Why first: forward direction has no Mont scaling drift (zetas are
plain in libcrux; but per the audit, each butterfly's `o1 = mont_mul(b - a, zeta) =
(b - a) · zeta · R⁻¹` introduces R⁻¹).  However, for FORWARD `ntt_at_layer_n`,
the per-element commute lemma `lemma_ntt_layer_n_butterfly_to_fe`
(see `Hacspec_ml_kem.Commute.Chunk.fst:1108`) and existing
`lemma_ntt_layer_n_step_chunk_commutes` (lines 1198, 1208, 1218) likely
cover the per-vector arithmetic.  The Tier-2 lift is
`Classical.forall_intro` over 16 chunks.

Recipe (matches Phase 7a target #1 pattern):
- Use `to_spec_poly_plain` / `to_spec_poly_mont` (defined by E2 in
  `Hacspec_ml_kem.Commute.Chunk.fst`) to lift impl polys.
- `Classical.forall_intro` over the 16 chunks; per-chunk uses the existing
  per-vector chunk-commute lemma.
- `Seq.lemma_eq_intro` for poly-array equality.
- Final `createi_lemma` to match the hacspec `createi` form.

If the per-vector chunk-commute lemma is missing for some layer,
adding it is in scope (composes per-pair `lemma_butterfly_pair_commute`).

## Stop conditions for target #1

- ✅ `make Libcrux_ml_kem.Ntt.fst.checked` PASSES with new ensures conjunct, no admits.
- ❌ 30 min, target #1 not closed → ABORT with report.

## Then — Deliverable A (45-min cap on INTT post strengthening)

After ntt_at_layer_1 closes, attack `invert_ntt_montgomery`'s post:

### Tier-0 numeric identity

Add to `Hacspec_ml_kem.Commute.Chunk.fst`:
```fstar
let lemma_1441_eq_RR_div_128 : Lemma ((128 * 1441) % 3329 == (R_VAL * R_VAL) % 3329)
  = assert_norm ((128 * 1441) % 3329 == 1353)  (* 1353 = R² mod q *)
  (* if R_VAL is defined; otherwise inline the value 1353 *)
```

Or simpler:
```fstar
let lemma_1441_finalization_id : Lemma ((128 * 1441 * 169) % 3329 == 2285 % 3329)
  = assert_norm _
  (* equivalently: (128 * 1441) % 3329 == 1353 (= R² mod q) *)
```

This is the structural identity from the pq-crystals reference comment
`1441 = mont^2/128`.  Use whichever phrasing the downstream lemmas need.

### Per-element INTT-Mont form lemma

Add to `Hacspec_ml_kem.Commute.Chunk.fst`:
```fstar
val lemma_intt_mont_form_post (b r b_real: i16) : Lemma
  (requires
    v b * R ≡ v b_real * 128 (mod 3329)   (* INTT-Mont form precondition *)
    /\ v r % 3329 == (v b * 1441 * 169) % 3329)  (* trait post for mont_mul(b, 1441) *)
  (ensures v r % 3329 == v b_real % 3329)
  (* proof: chain via lemma_1441_eq_RR_div_128 *)
```

### Strengthen `invert_ntt_montgomery`'s post

The semantic conjunct: post-INTT, each impl coefficient stored as i16
relates to the FIPS-203 INTT (without final · 3303) by the form
`v re_out.[i] * R ≡ ntt_inverse_butterflies(input).[i] * 128 (mod q)`,
or equivalently `v re_out.[i] ≡ ntt_inverse_butterflies(input).[i] * 128 / R (mod q)`.

Express via a hacspec helper — likely `Hacspec_ml_kem.Invert_ntt.<some fn>`
that captures the butterflies-only form.  If the hacspec doesn't have
exactly this function, you may add a derived helper in
`specs/ml-kem/src/invert_ntt.rs` (or in a hand-written F* helper file)
**with the user's approval to extend the canonical hacspec**.  Default
to the latter if uncertain.

Loop invariants for layer_1, layer_2, layer_3, layer_4_plus must each
carry one piece of the cumulative INTT form across iterations.  This is
where the structural F* work lives.

## Concurrency caveat

Phase 7a-finish (Wave 4) and Phase 7d (Wave 3) will edit the same
`Hacspec_ml_kem.Commute.Chunk.fst`.  Add your contributions in
clearly-labeled sections:

```
(*** Phase 7b Tier-2 commute lemmas — NTT/Inv-NTT ***)

(* INTT-Mont finalization lemmas *)
let lemma_1441_eq_RR_div_128 ...
let lemma_intt_mont_form_post ...

(* Tier-2 lemmas for forward NTT *)
let lemma_ntt_at_layer_1_commute ...
let lemma_ntt_at_layer_2_commute ...
let lemma_ntt_at_layer_3_commute ...
let lemma_ntt_at_layer_7_commute ...

(* Tier-2 lemmas for inverse NTT *)
let lemma_invert_ntt_at_layer_1_commute ...
let lemma_invert_ntt_at_layer_2_commute ...
let lemma_invert_ntt_at_layer_3_commute ...
let lemma_invert_ntt_at_layer_4_plus_commute ...
```

## R1-R9 hard rules (do not relearn — see agent-E2-brief.md)

R1. Admit-driven scaffolding = unacceptable.  Skip-with-comment AFTER a
    real attempt is OK.
R2. Trait posts in `src/vector/traits.rs::spec` deliver per-lane FE
    equations via opaque predicates.  Use them directly.
R3. 30-min cap on target #1 (`ntt_at_layer_1`); abort with report if
    not closed.  45-min cap on Deliverable A (INTT-form post).
R4. EXISTING pre-trait-opacify proofs are reference-only.
R4a. REPLACE `Spec.MLKEM` cite with `Hacspec_ml_kem.{Ntt,Invert_ntt}`
     cite in-place; preserve bounds preconditions.
R5. Body assumes are unacceptable.
R6. ulimit -v 8388608, --z3cliopt smt.memory_max_size=8000, F* rlimit ≤ 800.
R7. Default to plain `make`; fstar-mcp only when iterating ≥5x on the
    same hand-written F* file.
R8. Eager-commit log to `proofs/agent-status/agent-F.md` on this branch.
R9. Don't redesign trait spec; minor loop-invariant strengthening OK.

**R10 (new for this brief)**: If the existing `Hacspec_ml_kem.Invert_ntt.*`
module doesn't have a function exposing the "butterflies-only INTT
without final · 3303" form, you may add one in
`specs/ml-kem/src/invert_ntt.rs` named `ntt_inverse_butterflies` (or
similar).  This is hacspec extension, not redesign — the canonical
hacspec module gains a reference function that matches the impl's
intermediate form.  This is allowed because:
- The existing `ntt_inverse` (with the `· 3303`) is preserved as the
  fully-finalized form.
- The new helper is the natural "missing intermediate" of the FIPS-203
  algorithm.
- It enables clean impl-spec correspondence without contorting the
  impl-side post.

## Verification cadence

```bash
cd libcrux-ml-kem/proofs/fstar/extraction
ulimit -v 8388608
make Libcrux_ml_kem.Ntt.fst.checked Libcrux_ml_kem.Invert_ntt.fst.checked
make Hacspec_ml_kem.Commute.Chunk.fst.checked  # for Tier-2 lemmas
```

Re-extract via `python3 hax.py extract` if you change `ntt.rs`/`invert_ntt.rs`.

## Stop conditions

- 30-min cap on target #1 (`ntt_at_layer_1`).
- 45-min cap on Deliverable A (INTT post).
- 22-min cap per remaining target (5 forward/inverse layer functions).
- 180-min total cap.

## Final deliverable

Commits on `agent/phase-7b-ntt`:
1. `Hacspec_ml_kem.Commute.Chunk.fst` — Tier-0 finalization identity +
   per-element INTT-Mont lemma + Tier-2 commute lemmas (real bodies).
2. `src/ntt.rs`, `src/invert_ntt.rs` — strengthened posts.
3. `specs/ml-kem/src/invert_ntt.rs` — possibly new `ntt_inverse_butterflies`
   helper exposing the no-128⁻¹ form.
4. `proofs/agent-status/agent-F.md` log.
5. Final commit: `agent-F: Phase 7b — N/8 NTT layer fns proved + INTT-Mont
   post on invert_ntt_montgomery`.

DO NOT push.  DO NOT merge.  Parent reviews and merges; subsequent
Phase 7a-finish agent picks up off your branch tip.
