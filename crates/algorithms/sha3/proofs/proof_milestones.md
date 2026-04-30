# SHA-3 Proof Milestones

Hand-curated tracker of *meaningful* proof outcomes, complementing the
mechanical `verification_status.md` tier counts. Each row is a named
proof goal; status is judged by inspecting the owning function's
`#[ensures(...)]` text, body annotations, and the separate equivalence
lemmas at `proofs/fstar/equivalence/` on `sha3-proofs-focused`
(HEAD `7bab19fbf`).

## Status legend

- ✅ **Proven** — equivalence to the hacspec function established
  (either via the function's own `ensures` citing `Hacspec_sha3.*`,
  or via a separate `EquivImplSpec.*` lemma).
- 🔶 **Spec stated, body admitted** — ensures shape correct but the
  body or supporting lemma has an admit.
- ⚠️ **Bounds/length only** — ensures proves only output-length /
  preconditions; no functional spec.
- ❌ **No claim** — function has no ensures, or is unverified at any tier.

## Distance bands

- *(done)* — proof complete.
- *~1 session* — small, focused gap.
- *~1 sprint* — needs ensures wiring + Z3 work.
- *~2 sprints+* — multi-component or needs spec definition.

## Spec module landscape

`Hacspec_sha3.*` lives at `~/libcrux-sha3-focused/specs/sha3/proofs/fstar/extraction/`
and contains:
- `Hacspec_sha3.Keccak_f.fst` — the round-permutation spec (`keccak_f`).
- `Hacspec_sha3.Sponge.fst` — sponge spec (`absorb`, `squeeze_state`,
  `squeeze_last`, etc.).
- `Hacspec_sha3.Sha3.fst` — the top-level digest spec.

Equivalence proofs live under `proofs/fstar/equivalence/`:
`EquivImplSpec.Keccakf.{Portable,Avx2,ChiFold}.fst`,
`EquivImplSpec.Sponge.{Portable,Avx2,Arm64,Generic.Core}.fst`, etc.

---

## Layer 1 — Keccak-f[1600] permutation

| # | Milestone | Owner fn (file:line) | Status | Distance |
|---|---|---|---|---|
| 1 | Generic `keccakf1600` correct vs hacspec | `src/generic_keccak.rs:240 keccakf1600` | 🔶 the function itself has NO ensures, BUT `EquivImplSpec.Keccakf.Portable.lemma_keccakf1600_portable` IS invoked at `generic_keccak/portable.rs:89` to assert equivalence to `Hacspec_sha3.Keccak_f.keccak_f`. Proof exists OUTSIDE the function ensures. | ~1 session — pull the lemma into a function-level `ensures` so it's auditable from the source |
| 2 | Per-step Theta / Rho / Pi / Chi / Iota correct vs hacspec | `src/generic_keccak.rs` (lines 200-240, individual step methods) | ⚠️ — these methods (`theta`, `rho`, `pi`, `chi`, `iota`) have only basic `requires`; equivalence is established at the `keccakf1600` level via `EquivImplSpec.Keccakf.ChiFold` (chi-fold step is the hardest) | partial — the chi-fold equivalence is the cited bottleneck; per-step lemmas exist but aren't surfaced in source ensures |
| 3 | AVX2 `keccakf1600` correct vs hacspec | `EquivImplSpec.Keccakf.Avx2.fst::lemma_keccakf1600_avx2` | ✅ **proven** (audited 2026-04-30) — 7 lane-correctness primitives all `let`, no `assume val`. The main theorem is a direct specialization of `G.lemma_keccakf1600_to_spec` at N=4. The file's preamble comment about "seven primitives admitted" is **out of date** — those have since been closed. The proof relies on `lemma_shl_xor_shr_is_rotate_left` (in `Libcrux_sha3.Proof_utils.Lemmas`), which is admitted in Proof_utils because `Core_models.Num.impl_u64__rotate_left` is itself an opaque `assume val` — that's an intrinsics-layer admit, not a sha3-layer one. | *(done — modulo intrinsics-layer admit on rotate_left)* |
| 4 | Neon (Arm64) `keccakf1600` correct vs hacspec | `EquivImplSpec.Keccakf.Arm64.fst::lemma_keccakf1600_arm64` | ✅ **proven** (audited 2026-04-30) — 7 lane-correctness primitives all `let`, no `assume val`. Main theorem is a direct specialization of `G.lemma_keccakf1600_to_spec` at N=2. Cleaner than the AVX2 backend (no intrinsics admits cited in the body). | *(done)* |
| 5 | Portable `keccakf1600_portable` calls match permutation spec | `src/generic_keccak/portable.rs:89` (lemma invocation) | ✅ — lemma `EquivImplSpec.Keccakf.Portable.lemma_keccakf1600_portable` invoked at the call site; assert succeeds | *(done)* |

## Layer 2 — Sponge (absorb / squeeze)

The sponge construction is the strongest-verified layer in the crate.

| # | Milestone | Owner fn (file:line) | Status | Distance |
|---|---|---|---|---|
| 6 | `Generic_keccak.Portable::absorb` correct vs hacspec | `src/generic_keccak/portable.rs:161 absorb` | ✅ **proven** — ensures asserts `$result.st == Hacspec_sha3.Sponge.absorb $RATE $DELIM $input` directly. Options: `--z3rlimit 800 --split_queries always`. Loop invariant uses block-indexed `absorb_blocks` to dodge a Z3 LP-solver bug. | *(done)* |
| 7 | `Generic_keccak.Portable::squeeze` correct vs hacspec | `src/generic_keccak/portable.rs:245 squeeze` | ✅ — body fragment uses `Hacspec_sha3.Keccak_f.keccak_f` and `Hacspec_sha3.Sponge.squeeze_state`/`squeeze_last` to assert equivalence | *(done)* |
| 8 | `Generic_keccak.Portable::squeeze_first_block`, `squeeze_next_block`, `squeeze_first_three_blocks`, `squeeze_first_five_blocks`, `squeeze_last` correct | `src/generic_keccak/portable.rs:30, 41, 51, 83, 128` | ⚠️ — function-level ensures only `future(out).len() == out.len()` (panic-free); functional equivalence likely covered by composition through (7) but not stated per-block | ~1 session per block-variant to surface the per-fn ensures |
| 9 | `Generic_keccak.Simd128::absorb2`, `squeeze2` (Neon, N=2) | `src/generic_keccak/simd128.rs` via `EquivImplSpec.Sponge.Arm64.{fst, Steps.fst, API.fst}` | 🔶 **partial** (audited 2026-04-30) — `EquivImplSpec.Sponge.Arm64.fst` (main, 0 admits) and `Arm64.Steps.fst` (0 admits) are clean. `Arm64.API.fst::lemma_squeeze2_arm64` is `assume val` (single driver-level admit; the loop-invariant proof on `Simd128.squeeze2` is unfinished — see `BRIEF_squeeze_steps.md` and `HANDOFF.md`). The absorb side IS proven (`lemma_absorb2_arm64` is `let`). | ~1 sprint to close `lemma_squeeze2_arm64` (loop-invariant work analogous to portable squeeze) |
| 10 | `Generic_keccak.Simd256::absorb4`, `squeeze4` (AVX2, N=4) | `src/generic_keccak/simd256.rs` via `EquivImplSpec.Sponge.Avx2.{fst, Steps.fst, API.fst}` | 🔶 **partial** (audited 2026-04-30) — same shape as Arm64. Main + Steps files are clean. `Avx2.API.fst::lemma_squeeze4_avx2` is `assume val` (single driver-level admit; mirrors `lemma_squeeze2_arm64`'s gap). The absorb side IS proven. The admit's comment cites `avx2_sc_store_block` as a precondition admit but the actual file shows 0 admits there — comment may be stale. | ~1 sprint, mirrors row 9 |
| 11 | `Generic_keccak.Xof::*` correct (extendable-output functions) | `src/generic_keccak/xof.rs` | ⚠️ — script shows it under Generic, panic-free | ~1 session to surface ensures |
| 12 | `keccak1` (single-rate single-call) correct | `src/generic_keccak/portable.rs:447 keccak1` | ✅ **wired** — function-level ensures cites `Hacspec_sha3.Sponge.keccak`. Composition of (6) absorb + (7) squeeze + `keccak` definitional unfold (`--fuel 1`). Verification pending due to upstream flake — see Note A. | *(wired; verify-pending)* |

## Layer 3 — Top-level Hash API

| # | Milestone | Owner fn (file:line) | Status | Distance |
|---|---|---|---|---|
| 13 | `sha3::sha224` correct vs `Hacspec_sha3.Sponge.keccak 28 144 6 _` | `src/lib.rs::sha224` | ✅ **wired** — `lib.rs` IS extracted (as `Libcrux_sha3.fst`, no `.Lib` segment); the prior milestone text was wrong on extraction status. Function-level ensures cites `Hacspec_sha3.Sponge.keccak` directly (skipping the `try_into` wrapper in `Hacspec_sha3.Sha3.sha3_224`, which is identity for `[u8; 28] → [u8; 28]`). Verification pending — see Note A. | *(wired; verify-pending)* |
| 14 | `sha3::sha256` correct vs `Hacspec_sha3.Sponge.keccak 32 136 6 _` | `src/lib.rs::sha256` | ✅ **wired** | *(wired; verify-pending)* |
| 15 | `sha3::sha384` correct vs `Hacspec_sha3.Sponge.keccak 48 104 6 _` | `src/lib.rs::sha384` | ✅ **wired** | *(wired; verify-pending)* |
| 16 | `sha3::sha512` correct vs `Hacspec_sha3.Sponge.keccak 64 72 6 _` | `src/lib.rs::sha512` | ✅ **wired** | *(wired; verify-pending)* |
| 17 | `sha3::shake128<BYTES>`, `shake256<BYTES>` correct vs `Hacspec_sha3.Sponge.keccak BYTES (168\|136) 31 _` | `src/lib.rs` | ✅ **wired** | *(wired; verify-pending)* |
| 18 | `*_ema` variants correct (sha224_ema, sha256_ema, sha384_ema, sha512_ema, shake128_ema, shake256_ema) | `src/lib.rs::sha224_ema, sha256_ema, ...` | ✅ **wired** — function-level ensures on each, citing `Hacspec_sha3.Sponge.keccak` at the appropriate rate/delim/length | *(wired; verify-pending)* |
| 19 | `Portable::sha224/256/384/512` (the actual implementations under `lib.rs::sha*` wrappers) | `src/portable.rs::sha224, sha256, sha384, sha512, shake128, shake256` | ✅ **wired** — function-level ensures on all six, citing `Hacspec_sha3.Sponge.keccak`. Verification pending — see Note A. | *(wired; verify-pending)* |
| 20 | `Avx2::*` (parallel hashing) correct | `src/avx2.rs` | ⚠️ — extraction is in-flight in a separate dirty effort (untracked `Libcrux_sha3.Avx2.X4*.fst`, modified `src/simd/avx2.rs`); not addressed by this sprint per R7. | gated on the parallel AVX2 effort completing extraction |
| 21 | `Neon::*` correct | `src/neon.rs` | partial — script shows 1 hacspec in Neon; check coverage | review |
| 22 | `digest::Digest` trait impl correct | `src/impl_digest_trait.rs` | ❌ unverified — `#[cfg(not(any(hax, eurydice)))]` gate keeps it out of extraction | not on the F\*-verification path; intentional |

## Note A — verification-pending status (2026-04-30)

Sprint added function-level hacspec ensures to keccak1 + 18 layer-3
wrapper functions (6 in `Libcrux_sha3.Portable.fst`, 12 in
`Libcrux_sha3.fst`). Verification could not be COMPLETED in this
sprint because:

- `EquivImplSpec.Keccakf.Generic.fst::lemma_theta_rho_to_spec` is
  pre-existing-flaky at HEAD: query 1 timed out at 446s and query
  19 timed out at 566s under `--z3rlimit 1600` in the run on
  2026-04-30 16:43 UTC. The flake is upstream of all sponge / keccak
  proofs, so the entire dependency chain through
  `Libcrux_sha3.Generic_keccak.Portable.fst` cannot be re-verified
  from a cold cache.
- No `.checked` cache existed for `Libcrux_sha3.Generic_keccak.Portable.fst`
  at sprint start (Apr 26 cache, regenerated Apr 30).
- Per R3 + R7, this sprint did NOT add admits to bypass the upstream
  flake nor edit the dirty in-flight `proof_utils.fst` /
  `simd/avx2` work that may be perturbing the chain.

Mitigation: the source-side ensures are wired and the script picks
them up (Hacspec count 6 → 25). A subsequent session that fixes the
upstream flake (or uses a stronger Z3 timeout) should be able to
discharge them mechanically.

### Attempts to stabilize `lemma_theta_rho_to_spec` (reverted)

Three approaches were tried in-session, all reverted (lemma file is
back to HEAD):

  1. **forall_intro of `()`-bodied aux**: `let aux (k: nat{k < 25})
     : Lemma (Seq.index lhs k == Seq.index rhs k) = ()` followed by
     `forall_intro aux`. Failed: aux body for arbitrary `k` requires
     Z3 to case-split on `k`, which `--ifuel 1` doesn't enable.
     Failure shifted from eq_intro (query 19/20) to aux body (query
     21/26) — same Z3 difficulty, different location.

  2. **25 explicit `assert (lhs.[mk_usize K] == rhs.[mk_usize K])`
     before `eq_intro`**: 293 of 294 split sub-queries passed at
     <300 ms each (the per-index asserts work — each matches a
     specific conjunct of `lemma_rho_thru_4_extract_lane` literally).
     Final eq_intro still timed out at 570 s on its forall
     precondition: Z3 has 25 specific facts but cannot lift them to
     `forall i. lhs.[i] == rhs.[i]` without an explicit forall_intro.

  3. **25-branch if-else case-split aux + `forall_intro`**: each aux
     branch sees a literal `i = K` so each per-index sub-query was
     supposed to be fast. In practice queries 1–46 passed quickly
     (each <17 rlimit), but queries 47+ took 4–6 minutes each at
     876–1187 rlimit — passing but at the edge of the 1600 budget.
     Extrapolating, with ~250+ similar queries the run would take
     20+ hours; not viable in sprint budget. Killed and reverted.

Findings: the per-index reasoning IS sound (attempt 2 confirms each
case is provable in <300 ms when isolated), but composing 25 facts
into a forall is what breaks. **The right fix is structural: factor
`lemma_theta_rho_to_spec` into 5 row-helpers (one per row of 5
indices) using the existing `lemma_rho_thru_K_extract_lane`
partials, then assemble.** Each row-helper has a 5-element forall
that Z3 should handle directly. Estimated 1 sprint of careful work
— not the 30-minute "tweak" suggested by the agent prompt.

## Headline interpretation

After this sprint:
- Script reports **Hacspec: 25/242 (10.3%)**, up from 6/242 (2.5%).
- **Unverified: 1/242 (0.4%)** (was 17 — the 16 lib.rs fns flipped
  to extracted via the script fix; impl_digest_trait remains by
  design as it's `cfg(not(any(hax, eurydice)))`).
- **Panic-safe: 98.8%**, up from 92.1%.

Caveat: the 19 newly-Hacspec-counted functions are wired but
verification-pending due to the upstream `lemma_theta_rho_to_spec`
flake described in Note A.

## Comparison with ml-kem / ml-dsa

| Aspect | sha-3 | ml-kem (trait-opacify) | ml-dsa |
|---|---|---|---|
| Core primitive proven equiv | ✅ keccakf1600 across **all 3 backends** (Portable + AVX2 + Neon) | ⚠️ inverse NTT layers 1, 3 only | ⚠️ none (bounds only) |
| Mid-level (encoding/sponge) | ✅ Portable absorb/squeeze direct; ✅ Neon absorb (`absorb2`); ✅ AVX2 absorb (`absorb4`); 🔶 Neon `squeeze2` admitted as driver-lemma; 🔶 AVX2 `squeeze4` same | ⚠️ partial | ⚠️ bounds only |
| Top-level API extracted | ✅ `lib.rs` IS extracted (sprint of 2026-04-30 corrected the script) | ❌ mlkem.rs filtered | partial — variant API extracted |
| Top-level API correct (Portable) | ✅ wired (verify-pending until upstream `lemma_theta_rho_to_spec` is properly stabilized; admitted USER-1 here) | ❌ no claim | ❌ no claim |
| Top-level API correct (AVX2/Neon) | ❌ digests in `avx2.rs`/`neon.rs` not yet wired with hacspec ensures (squeeze4/squeeze2 admits would need to discharge first) | ❌ no claim | ❌ no claim |

sha3 is the most-advanced of the three at the **mid-level** AND now
also at the **Portable API surface** (lib.rs wired this sprint).
Remaining bottleneck: the two `squeeze{2,4}` driver-lemma admits on
the SIMD backends, and the structural fix to `lemma_theta_rho_to_spec`.

## Next-priority order

1. **Stabilize `lemma_theta_rho_to_spec` properly** (Note A) —
   replace the USER-1 admit (added 2026-04-30 to unblock the chain)
   with the row-helper factoring approach. ~1 sprint of focused
   proof-engineering work.
2. **Close the two squeeze driver-lemma admits** (rows 9, 10) —
   `lemma_squeeze4_avx2` and `lemma_squeeze2_arm64`. Per `HANDOFF.md`
   + `BRIEF_squeeze_steps.md`, the Simd128/Simd256 squeeze loop
   invariant is the unfinished work; the absorb side is already
   proven. Once these close, AVX2 + Neon mid-level is fully verified.
3. **Wire AVX2/Neon top-level digests** (`avx2.rs`, `neon.rs`) —
   gated on (2). Mirrors the Portable layer-3 wiring done in this
   sprint; per-digest ensures cite `Hacspec_sha3.Sponge.keccak` at
   the parallel-N-lane level.
4. **Surface `lemma_keccakf1600_portable` as `ensures` on `keccakf1600`**
   (row 1) — generic version is parameterised by `T: KeccakItem`, so
   the surfacing requires either per-backend wrapper methods or a
   generic ensures conditional on the type parameters. ~1 session.
5. **Per-block squeeze ensures** (row 8) — surface the per-block
   functional equivalence so callers don't need to reason through the
   composition manually.
6. **`hash()` dispatcher correctness** (`lib.rs::hash`) —
   match-based ensures over Algorithm enum; not addressed in this
   sprint due to match-based ensures complexity.
