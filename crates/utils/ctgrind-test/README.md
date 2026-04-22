# ctgrind-test

Constant-time (CT) tests using [Valgrind memcheck](https://valgrind.org/docs/manual/mc-manual.html).

Each binary marks secret data as "undefined" with `crabgrind::memcheck::mark_memory`, runs a
cryptographic operation, then unpoisons the output. Valgrind flags any conditional branch or
memory access whose value flows from a poisoned (secret) byte — indicating a CT violation.

## Binaries

| Binary         | What is tested                                       | Expected result                   |
| -------------- | ---------------------------------------------------- | --------------------------------- |
| `ctgrind-test` | Insecure vs. secure byte comparison (demo)           | Insecure comparison flagged       |
| `sha3`         | SHA-256, SHA-512, SHAKE-256 over a secret message    | Clean                             |
| `mlkem`        | ML-KEM-512 `decapsulate` with a poisoned private key | Clean                             |
| `mldsa`        | ML-DSA-44 `sign` with a poisoned signing key         | Violations (expected — see below) |

## Running with Docker

_Required on MacOS (arm)_

Build the image once from the repo root:

```sh
docker build -t valgrind crates/utils/ctgrind-test/
```

Then run each binary from the **repo root**:

```sh
# SHA-3
docker run --rm -v "$PWD":/app -w /app valgrind bash -c \
  "CARGO_PROFILE_RELEASE_DEBUG=true cargo build -p ctgrind-test --release && valgrind --error-exitcode=1 ./target/release/sha3"

# ML-KEM
docker run --rm -v "$PWD":/app -w /app valgrind bash -c \
  "CARGO_PROFILE_RELEASE_DEBUG=true cargo build -p ctgrind-test --release && valgrind --error-exitcode=1 ./target/release/mlkem"

# ML-DSA
docker run --rm -v "$PWD":/app -w /app valgrind bash -c \
  "CARGO_PROFILE_RELEASE_DEBUG=true cargo build -p ctgrind-test --release && valgrind --error-exitcode=1 ./target/release/mldsa"
```

Run all three in one go:

```sh
docker run --rm -v "$PWD":/app -w /app valgrind bash -c "
  CARGO_PROFILE_RELEASE_DEBUG=true cargo build -p ctgrind-test --release &&
  echo '--- SHA3 ---'  && valgrind --error-exitcode=1 ./target/release/sha3 &&
  echo '--- ML-KEM ---' && valgrind --error-exitcode=1 ./target/release/mlkem &&
  echo '--- ML-DSA ---' && valgrind --error-exitcode=1 ./target/release/mldsa
"
```

> **Why Docker?**  
> Valgrind on macOS/Apple Silicon does not support all Apple-proprietary ARM64 system registers
> and aborts with `disInstr: unhandled instruction`. The Docker image runs a Linux environment
> where Valgrind works correctly.

## What is and isn't poisoned

Only the genuinely secret bytes are poisoned. Public data embedded in key structs must stay
clean or Valgrind produces false positives in public sampling routines.

**ML-KEM private key** (`[cpa_sk | pk | H(pk) | z]`, 1632 bytes for ML-KEM-512):
- Poisoned: `cpa_sk` (first 768 bytes) and `z` (last 32 bytes)
- Not poisoned: embedded public key and `H(pk)` — these are used in the FO re-encryption
  step to reconstruct matrix A from the public seed ρ

**ML-DSA signing key** (`[ρ | K | tr | s₁, s₂, t₀]`, 2560 bytes for ML-DSA-44):
- Poisoned: `K` (bytes 32–64) and `s₁, s₂, t₀` (bytes 128–end)
- Not poisoned: `ρ` (public seed for matrix A) and `tr` (hash of verification key)

## ML-DSA findings

The `mldsa` binary intentionally produces Valgrind errors. Two violation classes are found in
`ml_dsa_44::sign`:

1. **`infinity_norm_exceeds`** (`ml_dsa_generic.rs:284`)  
   The Fiat-Shamir-with-aborts rejection check `||z||∞ ≥ γ₁ − β` where `z = y + c·s₁`.
   Since `z` depends on the secret `s₁`, this branch is inherently key-dependent. This is a
   known and expected property of the Dilithium/ML-DSA algorithm.

2. **`inside_out_shuffle`** (`sample.rs:450`) in `sample_challenge_ring_element`  
   The Fisher-Yates shuffle that builds the sparse challenge polynomial `c`. The challenge
   input `c̃ = H(μ ‖ w₁)` is public, but tainted values from `z` (computed in a previous
   loop iteration) appear to spill into scratch memory reused by the shuffle on subsequent
   retries.
