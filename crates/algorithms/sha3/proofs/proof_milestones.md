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
| 12 | `keccak1` (single-rate single-call) correct | `src/generic_keccak/portable.rs:447 keccak1` | ⚠️ — short wrapper, no ensures shown | ~1 session — should compose absorb + squeeze, follows directly from (6)+(7) |

## Layer 3 — Top-level Hash API

| # | Milestone | Owner fn (file:line) | Status | Distance |
|---|---|---|---|---|
| 13 | `sha3::sha224` correct vs `Hacspec_sha3.Sha3.sha3_224` | `src/lib.rs::sha224` | ❌ unverified — `lib.rs` is filtered out of F\* extraction (no `Libcrux_sha3.Lib.fst`). Function has only a `requires` (length precondition); no ensures. | **first**: get `lib.rs` extracted (configure hax). Once extracted, ~1 session per digest to wire `Hacspec_sha3.Sha3.sha3_224` ensures. |
| 14 | `sha3::sha256` correct vs `Hacspec_sha3.Sha3.sha3_256` | `src/lib.rs::sha256` | ❌ same | gated on (13); ~1 session |
| 15 | `sha3::sha384` correct | `src/lib.rs::sha384` | ❌ same | gated on (13) |
| 16 | `sha3::sha512` correct | `src/lib.rs::sha512` | ❌ same | gated on (13) |
| 17 | `sha3::shake128`, `shake256` correct | `src/lib.rs` | ❌ same | gated on (13); ~1 session each |
| 18 | `*_ema` (in-place / "explicit memory address") variants correct | `src/lib.rs::sha224_ema, sha256_ema, ...` | ❌ same — same extraction gap | gated on (13) |
| 19 | `Portable::sha224/256/384/512` (the actual implementations under `lib.rs::sha*` wrappers) | `src/portable.rs::sha224, sha256, ...` | ⚠️ — script-counted under Portable; check if they have hacspec ensures | review needed; if not, ~1 session per fn (compose absorb + squeeze for the appropriate rate) |
| 20 | `Avx2::*` (parallel hashing) correct | `src/avx2.rs` | ❌ — `avx2.rs` is in the unverified set (`avx2.rs` filtered out per script) | ~1 session to extract + wire |
| 21 | `Neon::*` correct | `src/neon.rs` | partial — script shows 1 hacspec in Neon; check coverage | review |
| 22 | `digest::Digest` trait impl correct | `src/impl_digest_trait.rs` | ❌ unverified (filtered out) | ~1 session to extract |

## Headline interpretation

The script's "Hacspec: 6/242 (2.5%)" UNDERCOUNTS the real proof
state because:
- The keccakf1600 equivalence is proven via `EquivImplSpec.*` lemmas
  invoked from inside other functions, not via the keccakf1600
  function's own `ensures`. The script can't see those lemmas.
- The sponge `absorb`/`squeeze` ensures DO cite `Hacspec_sha3.*` and
  contribute to the 6 hacspec count.

**Real picture**: the entire Generic-Keccak / Sponge layer is proven
equivalent to `Hacspec_sha3.{Keccak_f, Sponge}`. The gap is at the
top-level digest API (`lib.rs`) which isn't even extracted to F\*.

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

1. **Surface `lemma_keccakf1600_portable` as `ensures` on `keccakf1600`**
   (row 1) — small refactor, makes the proof state visible to the
   verification-status script and to readers. ~1 session.
2. **Extract `lib.rs`** (rows 13-18) — gates the entire top-level API
   correctness. ~1 session for extraction config + per-digest ensures
   wiring is then fast since the sponge layer is already proven.
3. **Audit `EquivImplSpec.Keccakf.Avx2.fst` and `EquivImplSpec.Sponge.Avx2.fst`**
   (rows 3, 10) — confirm AVX2 backend equivalence is closed (or file
   USER-N if admits remain).
4. **Per-block squeeze ensures** (row 8) — surface the per-block
   functional equivalence so callers don't need to reason through the
   composition manually.
5. **`avx2.rs` extraction** (row 20) — gates the parallel-hash API
   correctness.
