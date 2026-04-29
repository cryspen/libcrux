# Inter-wave protocol — Wave-A / Wave-B / Wave-C

This document defines how the three coordinator sessions hand off
work without stepping on each other's toes.  Each wave has its own
prompt file:

  - `wave-A-prompt.md` — Phase 2 (below-trait).
  - `wave-B-prompt.md` — Phase 3 parallel lanes (A1/A2/A3/A5).
  - `wave-C-prompt.md` — Phase 3 critical chain (A6 → A7 → A8).
    (Skeletal; recalibrated at end of Wave-B.)

---

## Worktree assignment

Each wave operates in its own worktree to avoid `.checked` cache
contention and to enforce surface-level isolation.

| Wave | Worktree | Surface owned |
|---|---|---|
| Wave-A | `/Users/karthik/libcrux-trait-opacify/` (existing) | `src/vector/{portable,avx2}.*`, `src/vector/{portable,avx2}/...`, `Hacspec_ml_kem.Commute.Chunk.fst` (B6 only), `Hacspec_ml_kem.Commute.Bridges.fst` (B4 only) |
| Wave-B | `~/libcrux-ml-kem-above-trait/` (NEW; create at Wave-A end) | `src/serialize.rs`, `src/sampling.rs`, `src/polynomial.rs`, `src/invert_ntt.rs`, `Hacspec_ml_kem.Commute.Chunk.fst` (A1/A3/A5 sections), `Hacspec_ml_kem.Commute.Bridges.fst` (A5 only) |
| Wave-C | `~/libcrux-ml-kem-above-trait/` (continues from Wave-B HEAD; same worktree) | `src/matrix.rs`, `src/ind_cpa.rs`, `src/ind_cca.rs`, `proofs/fstar/extraction/Makefile`, `Hacspec_ml_kem.Commute.Chunk.fst` (A6 sections only) |

**No wave touches `src/vector/traits.rs`.**  Trait is FROZEN at end
of Phase 1.  Trait gaps go to "Open findings" in
`lane-split-protocol.md`.

---

## ADMIT_MODULES protocol — what each wave admits

Each wave's local `proofs/fstar/extraction/Makefile` keeps OTHER
WAVES' modules in `ADMIT_MODULES`.  This is **lane isolation**, not
new admits — the modules are already either verified or admitted
upstream; the local Makefile just ensures the wave doesn't try to
re-verify what isn't its responsibility.

### Wave-A's local Makefile keeps admitted:

(All above-trait modules — already in ADMIT_MODULES at Wave-A start
unless a previous Phase removed them.)

  - `Libcrux_ml_kem.Polynomial.fst`
  - `Libcrux_ml_kem.Ntt.fst` (if currently admitted)
  - `Libcrux_ml_kem.Invert_ntt.fst` (if currently admitted)
  - `Libcrux_ml_kem.Matrix.fst`
  - `Libcrux_ml_kem.Serialize.fst` (if currently admitted)
  - `Libcrux_ml_kem.Sampling.fst` (if currently admitted)
  - `Libcrux_ml_kem.Compress.fst` (if currently admitted)
  - `Libcrux_ml_kem.Ind_cpa{,.Unpacked}.fst`
  - `Libcrux_ml_kem.Ind_cca{,.Unpacked,.Multiplexing,.Instantiations.*}.fst`
  - `Libcrux_ml_kem.Mlkem*.fst`

Note: per the existing Makefile (committed at `08dedde99` and prior),
several of these are already admitted.  Wave-A does NOT remove any
above-trait module from `ADMIT_MODULES`.

### Wave-B's local Makefile keeps admitted:

(All below-trait modules — Wave-A has finished them but they live in
the OTHER worktree; Wave-B's local check just admits them.)

  - `Libcrux_ml_kem.Vector.Portable.fst`
  - `Libcrux_ml_kem.Vector.Portable.Arithmetic.fst`
  - `Libcrux_ml_kem.Vector.Portable.Compress.fst`
  - `Libcrux_ml_kem.Vector.Portable.Ntt.fst`
  - `Libcrux_ml_kem.Vector.Portable.Sampling.fst`
  - `Libcrux_ml_kem.Vector.Portable.Serialize.fst`
  - `Libcrux_ml_kem.Vector.Portable.Vector_type.fst`
  - `Libcrux_ml_kem.Vector.Avx2.fst`
  - `Libcrux_ml_kem.Vector.Avx2.{Arithmetic,Compress,Ntt,Sampling,Serialize}.fst`

PLUS Wave-C's modules (A6/A7/A8 surface):

  - `Libcrux_ml_kem.Matrix.fst`
  - `Libcrux_ml_kem.Ind_cpa.fst`
  - `Libcrux_ml_kem.Ind_cca{,.Unpacked,.Multiplexing,.Instantiations.*}.fst`
  - `Libcrux_ml_kem.Mlkem*.fst`

REMOVED from ADMIT_MODULES (Wave-B unadmits as A-lanes land):

  - `Libcrux_ml_kem.Polynomial.fst` (post-A3 + A5)
  - `Libcrux_ml_kem.Invert_ntt.fst` (post-A5)
  - `Libcrux_ml_kem.Serialize.fst` (post-A1)
  - `Libcrux_ml_kem.Sampling.fst` (post-A2)

### Wave-C's local Makefile keeps admitted:

  - All Wave-A's below-trait modules (same list as Wave-B).
  - Any Wave-B module NOT YET MERGED at Wave-C start (should be
    none if handoff is clean).

REMOVED from ADMIT_MODULES (Wave-C unadmits sequentially):

  - `Libcrux_ml_kem.Matrix.fst` (post-A6)
  - `Libcrux_ml_kem.Ind_cpa.fst` (post-A7)
  - `Libcrux_ml_kem.Ind_cca*.fst` (post-A8)

---

## Handoff sequencing

```
Phase 1 done  →  Wave-A starts (below-trait)
Wave-A done   →  cherry-pick gate to Wave-B worktree, Wave-B starts
Wave-B done   →  Wave-C continues in same worktree, recalibrate scope
Wave-C done   →  sprint complete; merge above-trait worktree back to trait-opacify
```

### Wave-A → Wave-B handoff

1. Wave-A merges all B-lane commits to `trait-opacify`.
2. Wave-A coordinator updates `wave-B-prompt.md` with Wave-A's
   final commit SHA + admit-count baseline + any findings.
3. Wave-B coordinator clones / fetches the above-trait worktree
   from `trait-opacify` HEAD.
4. Wave-B edits its local Makefile to add below-trait modules to
   `ADMIT_MODULES`.
5. Wave-B verifies clean (`make` from `proofs/fstar/extraction/`
   exits 0 with the local admit list).

### Wave-B → Wave-C handoff

1. Wave-B merges all A1/A2/A3/A5 commits to `trait-opacify`.
2. Wave-B coordinator updates `wave-C-prompt.md` with:
   - Final commit SHA.
   - Recalibrated lane briefs (A6/A7/A8).
   - Findings from Wave-B (especially A3's Chunk additions, A5's
     Bridges additions, A4 outcome).
   - Net admit-count delta.
3. Wave-C coordinator continues in the SAME above-trait worktree
   (same `~/libcrux-ml-kem-above-trait/`), pulls latest from
   `trait-opacify`.
4. Wave-C edits Makefile to UNADMIT Polynomial / Invert_ntt /
   Serialize / Sampling (now verified by Wave-B).

---

## Hot-file conventions across waves

`Hacspec_ml_kem.Commute.Chunk.fst` is touched by **multiple lanes
across all three waves**.  It is the single most heavily-shared file
in the sprint.

**Discipline (enforced by every wave):**
  - Each lane appends to a clearly-marked section, e.g.
    `(* Phase 7c / lane A1 additions *)` or
    `(* Phase 2 / B6 additions *)`.
  - Section markers are stable across wave merges.  Wave-B's lanes
    add their own sections WITHOUT editing Wave-A's B6 section.
    Wave-C's A6 adds its own section WITHOUT editing Wave-A or
    Wave-B sections.
  - Existing lemma BODIES are never edited.  If a lemma needs a
    bug-fix, log it under "Open findings" and the original-section
    owner (or USER-lane) does the fix.
  - Cherry-pick frequency: when Wave-B is in progress, the wave-B
    worktree should pull `trait-opacify` HEAD whenever Wave-A merges
    a new B-lane commit — this picks up Chunk.fst additions for
    free (no manual cherry-pick needed since both worktrees fetch
    the same upstream branch).

`Hacspec_ml_kem.Commute.Bridges.fst`:
  - Wave-A: B4 only (and only if B4 doesn't descope).
  - Wave-B: A5 only.
  - Wave-C: untouched.
  Sequence: A5 (Wave-B) goes after B4 (Wave-A) if both run.

`proofs/fstar/extraction/Makefile`:
  - Wave-A: edits its OWN local Makefile only (do not push Makefile
    edits to `trait-opacify`).
  - Wave-B: same.
  - Wave-C: A7 then A8 push Makefile edits (UNADMIT) to
    `trait-opacify`.  These are the FIRST Makefile commits to
    upstream from any wave.
  - Phase 1 already touched the Makefile commentary; pre-existing
    edits stay.

---

## Cross-wave findings — where they go

If a wave discovers a problem in another wave's committed surface:

  - **Wave-B finds a Wave-A regression** (e.g., `Vector.Portable.fst`
    fails after Wave-B's local makefile edit): file under "Open
    findings" in `lane-split-protocol.md` with reproducer.
    Wave-B coordinator pings Wave-A coordinator (via `agent-trackA.md`
    entry); the back-port goes through a `agent/regression-fix-N`
    branch and merges to `trait-opacify`.

  - **Wave-C finds a Wave-A or Wave-B regression**: same protocol.

  - **Any wave finds a trait gap** (something in `traits.rs`
    needs strengthening): "Open findings" in
    `lane-split-protocol.md`.  Trait edits remain frozen until the
    sprint's coordinator decides whether to rerun Phase 1 partial.

---

## Sprint-wide admit-count tracking

Each wave reports a delta:
  - PROGRESS: admits removed (proofs closed for real).
  - SIDEWAYS: admits relocated to NEW admitted lemmas.
  - FAIR GAME: NEW small scoped admits handed to USER-N.

Running totals live in `MLKEM_STATUS.md` "Admit count" section
(Wave-A coordinator creates this section if it doesn't exist).

End of sprint (after Wave-C):
  - Sprint summary in `proofs/agent-status/sprint-summary.md` (NEW).
  - Net admit delta vs Phase 1 baseline.
  - USER-lane backlog.
  - Recommended next sprint.

---

## What if a wave fails to complete?

If Wave-A can't close all 6 lanes (e.g., B4 descopes, B6 stalls):

  - Mark the lane as USER-N in MLKEM_STATUS with the best-known
    blocker.  Wave-A still hands off to Wave-B IF B6 lands (since
    B6 gates Wave-B); if B6 doesn't land, the entire above-trait
    Phase 3 is gated and the sprint stalls.  Wave-A coordinator
    flags this in the deliverable.

If Wave-B can't close A5 (the critical path):
  - Wave-C cannot proceed (A5 → A6 dependency).  Wave-B coordinator
    flags + files as USER-6 with detailed Z3-saturation diagnostic.
    Sprint stalls until A5 unblocks.

If Wave-C stalls on A7 or A8:
  - These are the hardest lanes (Z3 walls on `compute_message`,
    `decapsulate`).  If 2 sessions per lane don't close, file as
    USER-N and either leave admitted (sprint partial close) or
    extend with another wave (Wave-D for ind_cca specifically).
