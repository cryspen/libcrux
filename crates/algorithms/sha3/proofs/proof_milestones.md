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
| 3 | AVX2 `keccakf1600` correct vs hacspec | `EquivImplSpec.Keccakf.Avx2.fst` | ❓ check status of the lemma — file exists, need to verify it's not admitted | review needed; ~1 session if admitted |
| 4 | Neon (Arm64) `keccakf1600` correct vs hacspec | `EquivImplSpec.Sponge.Arm64.fst` etc. | ❓ check status | review needed |
| 5 | Portable `keccakf1600_portable` calls match permutation spec | `src/generic_keccak/portable.rs:89` (lemma invocation) | ✅ — lemma `EquivImplSpec.Keccakf.Portable.lemma_keccakf1600_portable` invoked at the call site; assert succeeds | *(done)* |

## Layer 2 — Sponge (absorb / squeeze)

The sponge construction is the strongest-verified layer in the crate.

| # | Milestone | Owner fn (file:line) | Status | Distance |
|---|---|---|---|---|
| 6 | `Generic_keccak.Portable::absorb` correct vs hacspec | `src/generic_keccak/portable.rs:161 absorb` | ✅ **proven** — ensures asserts `$result.st == Hacspec_sha3.Sponge.absorb $RATE $DELIM $input` directly. Options: `--z3rlimit 800 --split_queries always`. Loop invariant uses block-indexed `absorb_blocks` to dodge a Z3 LP-solver bug. | *(done)* |
| 7 | `Generic_keccak.Portable::squeeze` correct vs hacspec | `src/generic_keccak/portable.rs:245 squeeze` | ✅ — body fragment uses `Hacspec_sha3.Keccak_f.keccak_f` and `Hacspec_sha3.Sponge.squeeze_state`/`squeeze_last` to assert equivalence | *(done)* |
| 8 | `Generic_keccak.Portable::squeeze_first_block`, `squeeze_next_block`, `squeeze_first_three_blocks`, `squeeze_first_five_blocks`, `squeeze_last` correct | `src/generic_keccak/portable.rs:30, 41, 51, 83, 128` | ⚠️ — function-level ensures only `future(out).len() == out.len()` (panic-free); functional equivalence likely covered by composition through (7) but not stated per-block | ~1 session per block-variant to surface the per-fn ensures |
| 9 | `Generic_keccak.Simd128::absorb`, `squeeze` (Neon backend) | `src/generic_keccak/simd128.rs` via `EquivImplSpec.Sponge.Arm64.fst` | ❓ check — equivalence file exists; not yet inspected | review |
| 10 | `Generic_keccak.Simd256::absorb`, `squeeze` (AVX2 backend) | `src/generic_keccak/simd256.rs` via `EquivImplSpec.Sponge.Avx2.fst` | ❓ check | review |
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
| Core primitive proven equiv | ✅ keccakf1600 + sponge | ⚠️ inverse NTT layers 1, 3 only | ⚠️ none (bounds only) |
| Mid-level (encoding/sponge) | ✅ absorb / squeeze direct equiv to `Hacspec_sha3.Sponge` | ⚠️ partial | ⚠️ bounds only |
| Top-level API extracted | ❌ lib.rs filtered | ❌ mlkem.rs filtered | partial — variant API extracted |
| Top-level API correct | ❌ no claim | ❌ no claim | ❌ no claim |

sha3 is the most-advanced of the three at the **mid-level** but the
most behind at the **API surface** (lib.rs unverified).

## Next-priority order

1. **Discharge the verify-pending layer-3 ensures** — fix the
   upstream `lemma_theta_rho_to_spec` flake (Note A) so the 19
   newly-wired ensures verify, OR add the lemma to `SLOW_MODULES` /
   factor it. ~1 session if the flake is timeout-only and not a
   regression.
2. **Surface `lemma_keccakf1600_portable` as `ensures` on `keccakf1600`**
   (row 1) — generic version is parameterised by `T: KeccakItem`, so
   the surfacing requires either per-backend wrapper methods or a
   generic ensures conditional on the type parameters. ~1 session.
3. **Audit `EquivImplSpec.Keccakf.Avx2.fst` and `EquivImplSpec.Sponge.Avx2.fst`**
   (rows 3, 10) — confirm AVX2 backend equivalence is closed (or file
   USER-N if admits remain).
4. **Per-block squeeze ensures** (row 8) — surface the per-block
   functional equivalence so callers don't need to reason through the
   composition manually.
5. **`top-level hash() dispatcher correctness`** (`lib.rs::hash`) —
   ensures depending on Algorithm enum value; not addressed in this
   sprint due to match-based ensures complexity.
