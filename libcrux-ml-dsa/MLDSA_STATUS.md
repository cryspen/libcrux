# MLDSA Verification Status

**Branch**: `ml-dsa-proofs`
**Sprint plan**: [`proofs/sprint-plan.md`](proofs/sprint-plan.md)
**Style guide**: [`proofs/proof-style-guide.md`](proofs/proof-style-guide.md)
**Outstanding admits**: [`proofs/outstanding-admits.md`](proofs/outstanding-admits.md)

## Spec hierarchy (DO NOT FORGET)

- ✅ **Canonical**: `Hacspec_ml_dsa.*` — in
  `specs/ml-dsa/proofs/fstar/extraction/Hacspec_ml_dsa.*.fst`. ALL new
  proofs and post-conditions cite this.
- ⚠️ **Obsolete (scheduled for deletion)**: `Spec.MLDSA.Math`,
  `Spec.MLDSA.Ntt`, `Spec.Intrinsics`. Cited only by
  `montgomery_multiply` post and AVX2 NTT. Banner-marked. Removed in
  Phase 4.
- 🔄 **Temporary scaffolding**: `Spec.Utils.*` — shared with ML-KEM via
  `proofs/fstar/extraction/Makefile:36`. Pieces we use will move to a
  future `Proof_utils.*` module.

## Quick links

- [Sprint plan](proofs/sprint-plan.md) — phase structure, parallelism, 20-min rule
- [ML-KEM proof-style guide](../libcrux-ml-kem/proofs/proof-style-guide.md) — original methodology
- [ML-KEM status](../libcrux-ml-kem/MLKEM_STATUS.md) — sister-effort tracker

## 20-minute proof rule

Every proof attempt has a hard wall-clock budget of **20 minutes**. If a
proof does not close in that window:

1. Mark the function as admitted using one of:
   - `#[hax_lib::fstar::verification_status::panic_free]` on the Rust function, OR
   - `hax_lib::fstar!("admit()")` at the top of the function body
2. Document in `proofs/outstanding-admits.md` (file:line, diagnosis, suggested mitigation).
3. Move on.

Goal: maximum easy-proof coverage in the sprint window. Hard proofs go
to the USER lane (math-heavy or Z3-blocked) for human follow-up.

## Phase status

| Phase | Description | Status | Owner / branch |
|---|---|---|---|
| **0** | Hardening + scaffolding (FIPS fixes, cross-spec tests, mirror docs, hacspec extensions) | in progress | `ml-dsa-proofs` (this session) |
| **1** | Strengthen Operations trait posts | pending | handoff |
| **2** | Portable Operations proofs (waves 2A–2G) | pending | handoff |
| **3** | AVX2 Operations proofs (waves 3A–3E) | pending | handoff |
| **4** | Spec migration & integration (waves 4A–4D) | pending | handoff |

## Operations trait method status

The 21 methods of `Operations` in `src/simd/traits.rs:36-176`. Status
columns: pre/post strength after Phase 1 (T), portable proof (P), AVX2
proof (A). Legend: ✅ done, 🟡 admit/bounds-only, ⏳ pending.

| Method | T | P | A | Spec anchor | Notes |
|---|---|---|---|---|---|
| `zero` | ⏳ | ⏳ | ⏳ | trivial (`repr() == [0;8]`) | already strong |
| `from_coefficient_array` | ⏳ | ⏳ | ⏳ | trivial | already strong |
| `to_coefficient_array` | ⏳ | ⏳ | ⏳ | trivial | already strong |
| `add` | ⏳ | ⏳ | ⏳ | `Polynomial.poly_add` | bounds-only post exists |
| `subtract` | ⏳ | ⏳ | ⏳ | `Polynomial.poly_sub` | bounds-only post exists |
| `infinity_norm_exceeds` | ⏳ | ⏳ | ⏳ | `Polynomial.poly_infinity_norm` | F15: switch to constant-time mask in Phase 0A |
| `decompose` | ⏳ | ⏳ | ⏳ | `Arithmetic.decompose` × 8 lanes | gamma2 ∈ {95232, 261888} |
| `compute_hint` | ⏳ | ⏳ | ⏳ | `Arithmetic.make_hint` × 8 + popcount | returns 0/1 not bool |
| `use_hint` | ⏳ | ⏳ | ⏳ | `Arithmetic.uuse_hint` × 8 lanes | spec name has typo `uuse_hint` |
| `montgomery_multiply` | ⏳ | ⏳ | ⏳ | per-lane `mod_q(a·b·R⁻¹)` | uses `Arithmetic.mod_q` after Phase 4A |
| `shift_left_then_reduce` | ⏳ | ⏳ | ⏳ | `Arithmetic.shift_left_then_reduce` | helper added in Phase 0D |
| `power2round` | ⏳ | ⏳ | ⏳ | `Arithmetic.power2round` | helper exists |
| `rejection_sample_<_field_modulus` | ⏳ | ⏳ | ⏳ | `Encoding.coeff_from_three_bytes` | per-byte step |
| `rejection_sample_<_eta_2` | ⏳ | ⏳ | ⏳ | `Encoding.coeff_from_half_byte` | η=2 |
| `rejection_sample_<_eta_4` | ⏳ | ⏳ | ⏳ | `Encoding.coeff_from_half_byte` | η=4 |
| `gamma1_serialize` | ⏳ | ⏳ | ⏳ | `Encoding.bit_pack` width γ₁_exp+1 | bitvec |
| `gamma1_deserialize` | ⏳ | ⏳ | ⏳ | `Encoding.bit_unpack` width γ₁_exp+1 | bitvec |
| `commitment_serialize` | ⏳ | ⏳ | ⏳ | `Encoding.simple_bit_pack` width 4 or 6 | per gamma2 |
| `error_serialize` | ⏳ | ⏳ | ⏳ | `Encoding.bit_pack` width 3 or 4 | per eta |
| `error_deserialize` | ⏳ | ⏳ | ⏳ | `Encoding.bit_unpack` width 3 or 4 | per eta |
| `t0_serialize` | ⏳ | ⏳ | ⏳ | `Encoding.bit_pack` width 13 | signed |
| `t0_deserialize` | ⏳ | ⏳ | ⏳ | `Encoding.bit_unpack` width 13 | signed |
| `t1_serialize` | ⏳ | ⏳ | ⏳ | `Encoding.simple_bit_pack` width 10 | unsigned |
| `t1_deserialize` | ⏳ | ⏳ | ⏳ | `Encoding.simple_bit_unpack` width 10 | unsigned |
| `ntt` | ⏳ | ⏳ | ⏳ | `Ntt.ntt` flat-256 | per-poly via `forall32` |
| `invert_ntt_montgomery` | ⏳ | ⏳ | ⏳ | `Ntt.intt` flat-256 | post-INTT in standard domain |
| `reduce` | ⏳ | ⏳ | ⏳ | per-lane `mod_q` ∧ `\|x\| < q` | Barrett |

## Pre-budgeted admits

Going in we expect the following will land as admits (worth listing
upfront so a session doesn't burn the 20-min budget on them):

- AVX2 NTT layers 1–2 — Z3-blocked on 4-zeta parallel SIMD wall (ML-KEM USER-4 analog).
- AVX2 INVNTT layers 1–2 — analogous.
- Full NTT composition (Tier-3 chain across 8 layers with BitRev₈ zeta indexing) — likely USER-2 analog.
- `compute_ciphertext_coefficient`-style Barrett-exactness enumerations — USER-1 analog.

## FIPS 204 audit

Read-only audit dated 2026-04-27 produced 33 findings (no Critical, 4
High, 12 Medium, 16 Low/cosmetic). Implementation conforms in all
correctness-critical respects (interop-tested against PQ-Crystals
KATs).

Items being acted on in Phase 0A (proof simplification benefit):

| ID | Sev | Location | Status |
|---|---|---|---|
| F4 | High | `src/encoding/signature.rs:33-49` (HintBitPack zero-pad) | ✅ Phase 0A |
| F3 | High | `src/ml_dsa_generic.rs:359-399` (verify_internal length asserts) | ✅ Phase 0A |
| F5 | High | `src/encoding/signature.rs:90-130` (HintBitUnpack Err semantics) | ✅ Phase 0A |
| F2 | High annotation | `src/pre_hash.rs:26`, `src/ml_dsa_generic.rs:699` (OID DER comment) | ✅ Phase 0A |
| F15 | Med | `src/simd/portable/arithmetic.rs:380-420` (constant-time mask: `\|\|` → `\|`) | ✅ Phase 0A |
| F13 | Med | `src/matrix.rs::vector_times_ring_element` + 3 callers in `ml_dsa_generic.rs` | **Deferred** to Phase 2+ — refactor to `(out, lhs, rhs)` signature is bigger than the 20-min Phase-0 budget and the "clone preserves equivalence" lemma it would eliminate is not blocking until sign-loop proofs land |

Items F1, F6–F12, F14, F16–F33 are conformance-confirmations or
cosmetic/perf with no proof impact — deferred past the sprint.

## Documentation cadence

This file MUST be kept in sync after each meaningful step (new
commit or wave complete). The session may close at any time — this
file plus `proofs/outstanding-admits.md` are the resume point.
