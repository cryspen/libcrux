# Trust-ledger tooling (`trust_scan.py` + `trust_ledger.py`)

A mechanically-computed, git-tracked ledger of the **unproven trust surface** of
the hax-verified crates (`libcrux-ml-kem`, `libcrux-ml-dsa`, `crates/algorithms/sha3`),
with a CI regression gate. It is the ground-truth side of the trust-annotation
campaign: the reported surface is computed **only** from build artifacts, so no
source marker can shrink it.

## What it measures — four observed planes

| Plane | What | Source |
|---|---|---|
| `fstar` | unproven obligations: `admit ()`, `magic ()`, bare `assume`, `assume val`, `--admit_smt_queries true` | scan of extracted `.fst`/`.fsti` + hand-written `spec/` companions |
| `extraction` | the set of extracted F\* modules (coverage) | `proofs/fstar/extraction/*.fst{,i}` matching the crate prefix |
| `makefile` | `SLOW_MODULES` / `ADMIT_MODULES` — modules verified-on-cadence or admitted in the default build | the F\* extraction `Makefile` |
| `patches` | post-extraction `*.patch` files (count + sha256) | `proofs/fstar/**/*.patch` |

`trust_scan.py` plane 1 reproduces the `fstar_admits` MCP tool **exactly** (validated
per-file for both large crates: ml-dsa 103, ml-kem 63) but with zero proxy/`make`
dependency, so it runs in plain CI.

## Usage

```bash
python3 scripts/trust_ledger.py --check            # observed vs baseline; exit 1 on regression
python3 scripts/trust_ledger.py --update-baseline  # rebaseline (deliberate, reviewed)
python3 scripts/trust_ledger.py --json             # dump the raw observed surface
python3 scripts/trust_ledger.py --crate ml-dsa --check
```

Baselines live at `<crate>/proofs/trust-ledger.baseline.json` (git-tracked,
auto-generated — do not hand-edit).

## The regression gate

`--check` fails (exit 1) when the trust surface **grows**:
- a new/increased F\* obligation in any module (a new *trusted assumption*),
- a new obligation *kind*,
- a baseline-extracted module that stopped extracting (silent coverage loss),
- `ADMIT_MODULES` grew (the ratchet target is empty) or `SLOW_MODULES` grew,
- a new post-extraction patch.

Surface *reductions* are reported as notes ("rebaseline to lock the win"), never
failures. So the ledger is monotonically non-increasing by construction — proving
an obligation away and rebaselining is the only way the numbers move down, and
nothing can move them up without a red CI.

## The gate runs AFTER extraction (CI-only)

Most obligations live in the *generated* F\* tree — the extracted `.fst`/`.fsti` are
gitignored (`*.fst` + `!`-exceptions for the hand-written companions), so ~94% of the
ml-dsa surface and most of ml-kem's are not present in a plain checkout. The plan's
V7 model therefore runs this **in CI, immediately after `hax extract`**, against a
clean generated tree. The committed baselines are that canonical post-extract surface:

| Crate | Baseline obligations | Note |
|---|---|---|
| ml-dsa | 103 | matches `fstar_admits`; `.fst` gitignored, 6 in tracked `spec/` companions |
| ml-kem | 63 | matches `fstar_admits` |
| sha3 | 6 | all `assume_val` — hax derive/trait stubs (trusted base); 0 actionable admits |

Consequence: **do not read a `--check` diff on a worktree that hasn't been freshly
re-extracted.** Stale leftover `.fst` from an older extraction (e.g. pre-relocation
module names) show up as spurious regressions — that is a "dirty tree", not a real
surface change. Re-extract, then check. The three baselines above were captured from
one consistent re-extraction of all three crates.

## Extension point — marker reconciliation (campaign G1+)

Today the gate is observed-side only (there are no `#[trusted(kind, "reason")]` markers
yet). When those land, `trust_ledger.reconcile()` gains a second direction, keyed on
hax's deterministic decl-name mangling:
1. **soundness** — every observed obligation must map to a matching-*kind* marker /
   F\* `[@@ "trusted: ..."]` tag / trusted-base allowlist entry; anything else is a
   hard fail (an unlabelled trusted assumption).
2. **no stale claims** — every marker must map forward to an observed obligation;
   orphans fail in strict mode.

Until then, markers only *annotate* the observed entries with categories/reasons —
they can never shrink the reported surface.
