# hpke-rs-wasm

A minimal [HPKE](https://www.rfc-editor.org/rfc/rfc9180.html) API compiled to
WebAssembly with [`wasm-bindgen`](https://rustwasm.github.io/wasm-bindgen/).

It exposes single-shot **key generation**, **seal**, and **open** in HPKE Base
mode (no PSK, no sender authentication). The ciphersuite is chosen by the caller
via `HpkeConfig` using the RFC 9180 code points, so it is not hard-coded.

All functions panic on any error.

## API

- `new HpkeConfig(mode, kem, kdf, aead)` — the ciphersuite, as RFC 9180 code
  points. For example `new HpkeConfig(0x00, 0x0020, 0x0001, 0x0003)` selects
  Base / DHKEM(X25519, HKDF-SHA256) / HKDF-SHA256 / ChaCha20Poly1305.
- `hpke_key_gen(config) -> KeyPair` with `.sk` and `.pk` getters (raw bytes).
- `hpke_seal(config, pk_r, info, aad, pt) -> Ciphertext` with `.enc` and `.ct`
  getters.
- `hpke_open(config, enc, sk_r, info, aad, ct) -> Uint8Array` (the plaintext).

## Building

Randomness on `wasm32-unknown-unknown` uses the `getrandom` `wasm_js` backend,
which requires the `getrandom_backend` cfg flag at build time. Build with
[`wasm-pack`](https://rustwasm.github.io/wasm-pack/):

```sh
RUSTFLAGS='--cfg getrandom_backend="wasm_js"' \
    wasm-pack build --target web
```

Use `--target web`, `--target bundler`, or `--target nodejs` depending on how
you consume the module. The generated package is written to `pkg/`.

The generated wasm uses bulk-memory operations (e.g. `memory.fill`), which the
`wasm-opt` step run by `wasm-pack` rejects unless the feature is enabled. This
is handled by the `[package.metadata.wasm-pack.profile.*]` entries in
`Cargo.toml`, which pass `--enable-bulk-memory` to `wasm-opt`.

## Example (JavaScript)

```js
import init, { HpkeConfig, hpke_key_gen, hpke_seal, hpke_open } from "./pkg/hpke_rs_wasm.js";

await init();

// Base / DHKEM(X25519, HKDF-SHA256) / HKDF-SHA256 / ChaCha20Poly1305.
const config = new HpkeConfig(0x00, 0x0020, 0x0001, 0x0003);

const kp = hpke_key_gen(config);

const info = new TextEncoder().encode("HPKE demo info");
const aad = new TextEncoder().encode("HPKE demo aad");
const plaintext = new TextEncoder().encode("HPKE demo plain text");

const ciphertext = hpke_seal(config, kp.pk, info, aad, plaintext);
const recovered = hpke_open(config, ciphertext.enc, kp.sk, info, aad, ciphertext.ct);

console.log(new TextDecoder().decode(recovered)); // "HPKE demo plain text"
```

## Testing

The round-trip logic is covered by a native unit test (no wasm toolchain
required):

```sh
cargo test -p hpke-rs-wasm
```
