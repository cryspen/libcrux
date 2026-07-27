# SIMD intrinsics trust-base plan

Authoritative reference for the SIMD-intrinsics trust-base sprint. Defines the
trust ladder (`L0..L4`), the `D6.*` coverage sub-metrics, the `T1/T2/T3` sets,
the cross-validation protocol (Step 5), and the invariants the tooling and CI
enforce. Scripts and source comments point here as the single source of truth:

- `scripts/intrinsics-audit.py` — regenerates `proofs/intrinsics-trust-index.{md,csv}`.
- `scripts/cross-validate.py` — Step 5 cross-validation (feeds `D6.4`).
- `scripts/classify-nospec.py` — classifies spec-free wrappers by caller status.
- `scripts/check-intrinsics-parity.sh` — CI gate over the metrics below.
- `src/core_arch/{arm,x86}.rs` and `src/core_arch/arm/neon.rs` — the opacity rule.

## The three sets

- **T1** — the libcrux **intrinsic wrappers**: every `pub fn` in
  `crates/utils/intrinsics/src/avx2.rs` (`T1_avx2`) and
  `crates/utils/intrinsics/src/arm64.rs` (`T1_arm64`). This is the surface the
  higher crates (ml-kem, ml-dsa, sha-3, aes, …) actually call, and the surface
  whose correctness the trust base must cover. Each wrapper resolves to one or
  more **underlying** `core::arch` intrinsics.
- **T2** — the intrinsics **modeled in core-models** (`src/core_arch/{x86,arm}`):
  a bit-vector-layer stub plus an integer-vector-layer computational body.
- **T3** — the SMTPat **lemmas in `libcrux-ml-dsa/proofs/fstar/spec/Spec.Intrinsics.fsti`**
  (the hand-written F\* lane-form specifications).

The audit reports the difference sets `T1\T2`, `T2\T1`, `T3\T1` so gaps and
dead entries are visible.

## Trust ladder (`L0..L4`)

Each T1 wrapper is assigned the highest level it qualifies for. The level is a
pure function of the boolean columns in `intrinsics-trust-index.csv` (see
`T1Entry.trust_level` in `intrinsics-audit.py`):

| Level | Meaning | Condition |
|---|---|---|
| **L0-nospec** | No model, no spec | no core-models body **and** no F\* spec |
| **L0** | Spec only | no core-models body, but an F\* spec exists (`ensures` or a `Spec.Intrinsics` lemma) |
| **L1** | Model, untested | a real core-models body exists, but no `mk!` differential test |
| **L2** | Model + differential test | body **and** a `mk!` randomized test against the real CPU, but not yet cross-validated |
| **L3** | + audit-consistent | L2 **and** the F\* spec cross-validates against the model (`audit_consistent = true`) |
| **L4** | + machine-proven | L3 **and** the F\* spec is discharged by F\* (`fstar_proven = true`) — **deferred this sprint** |

A wrapper is `has_body` only if *every* underlying intrinsic it calls has a
non-`unimplemented!()` body (one missing leaf drops the whole wrapper). A
wrapper is `has_mk_test` only if `has_body` and at least one underlying leaf has
a `mk!(...)` test (testing an undefined model is meaningless).

## `D6.*` sub-metrics (percentages over `|T1|`)

The audit emits, as its stable last stdout line:

```
D6.1=NN.N% D6.2=NN.N% D6.3=NN.N% D6.4=NN.N% D6.5=NN.N% T1=NNN
```

| Metric | Name | Numerator (over T1) |
|---|---|---|
| **D6.1** | Rust-model coverage | wrappers with `has_body` |
| **D6.2** | Test coverage | wrappers with `has_mk_test` |
| **D6.3** | F\* spec coverage | wrappers with a spec (`has_extract_ensures` or `has_specintrinsics_lemma`) |
| **D6.4** | Audit consistency | wrappers with `audit_consistent = true` (cross-validation passed) |
| **D6.5** | F\* spec proven | wrappers with `fstar_proven = true` (deferred → 0% by design) |

`D6.4` is `null`/0% until `cross-validate.py --audit-feed` populates the
`audit_consistent` column; the audit preserves that column across regenerations
(`preserve_audit_consistent_from_csv`) so a plain `intrinsics-audit.py` run does
not zero it.

## Step 5 — cross-validation protocol (`cross-validate.py`)

For every T1 intrinsic that has either an `#[hax_lib::ensures]` in `_extract.rs`
**or** a SMTPat lemma in `Spec.Intrinsics.fsti`, the script:

1. Generates `--samples` random inputs (default 10000), seeded by `--seed`.
2. Computes the intrinsic via a Python ground-truth lane operator mirroring the
   core-models `int_vec` body.
3. Parses the F\* spec predicate into a Python evaluator and asserts `LHS == RHS`
   on each sample.
4. Records `(intrinsic, input, expected, got)` on mismatch.
5. Emits a per-intrinsic verdict and the global findings markdown, then (with
   `--audit-feed`) writes each wrapper's pass/fail into the CSV's
   `audit_consistent` column, which drives `D6.4`.

**Soundness anchor.** The L2 precondition guarantees the core-models `int_vec`
body has already been differentially tested against the real CPU via `mk!`. So
the Python ground truth is anchored transitively: if it matches the `int_vec`
body, it matches the CPU. The cross-validation therefore surfaces
**F\*-spec ↔ ground-truth** mismatches — i.e. spec bugs, not CPU-model bugs.

**Supported lane-form patterns.** The F\*-spec parser understands a small
sub-language of lane-form predicates (`vecN_as_iKxM` / `get_lane*` views,
`map`/`map2`/`create`, per-lane arithmetic and shifts, `bit_vec_of_int_t_array`
decompositions). Specs whose predicate falls outside this sub-language are
reported as **OUT-OF-SCOPE-PATTERN** rather than silently passing; extending the
parser one pattern at a time is the natural follow-up. Out-of-scope specs do not
count toward `D6.4`.

## The opacity rule (bit-vector layer)

Every function in the bit-vector layer (`src/core_arch/arm/neon.rs`,
`src/core_arch/x86.rs` bit-vector stubs) is `#[hax_lib::opaque]` with an
`unimplemented!()` body. **This opacity is load-bearing** and must be preserved.

The computational content lives one layer down, in
`interpretations::int_vec`, connected to the bit-vector layer by
`mk_lift_lemma!` and validated by `mk!` differential tests. Downstream F\*
proofs reason about each intrinsic through its **`ensures` axiom only**, treating
the wrapper as an uninterpreted atom; the panicking `unimplemented!()` body is
never extracted into the proof context.

**Dropping `#[hax_lib::opaque]` on a bit-vector-layer function is forbidden
unless all three justification clauses hold:**

1. **Real body.** The function has a genuine, extractable body (not
   `unimplemented!()`), so exposing it to F\* is meaningful rather than an
   extraction of `False`.
2. **Validated at ≥ L3.** That body is `has_mk_test` *and* `audit_consistent`
   (differentially tested against the CPU and cross-validated against its F\*
   spec) — i.e. the wrapper sits at L3 or above in the ladder above.
3. **No consumer regression.** No downstream F\* proof depends on the intrinsic
   remaining an uninterpreted, `ensures`-only atom; this is confirmed by
   re-running the ml-kem / ml-dsa / sha-3 proofs after the change (a transparent
   body can flood Z3 or change quantifier behaviour even when value-identical).

## `BitVec<N>` const-generic convention

The bit-vector model uses `BitVec<N>` with the width const-generic reconciled
from the upstream `verify-rust-std/testable-simd-models` `u32` to **`u64`**
(the libcrux core-models convention). Keep new models on `u64` widths.

## CI gate (`check-intrinsics-parity.sh`)

The gate re-runs the audit and asserts, by exact integer comparison:

- `T1`, `T1_avx2`, `T1_arm64` **equal** the committed `EXPECT_T1*` constants — a
  new `pub fn` in `intrinsics/src/{avx2,arm64}.rs` grows `T1` and fails the
  check, forcing the contributor to model+test it (and bump the constant) or
  remove it.
- `D6.1`/`D6.2` (total and per-arch) are **≥** the committed `THRESHOLD_*`
  constants — coverage may not regress.

It then runs `cargo test -p core-models` (host), and — on a macOS host with the
`x86_64-apple-darwin` target installed — the AVX2 `mk!` pass via
`--target x86_64-apple-darwin`.

**Threshold-bump protocol.** When a wrapper legitimately gains body+test (or a
new wrapper is added and modeled), re-run the script; it fails with the new
counts. Bump the matching `EXPECT_*` / `THRESHOLD_*` constants **in the same
commit**. The gate then forbids regression below the new point.
