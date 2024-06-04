#include <cstring>
#include <stdlib.h>

#include <openssl/bytestring.h>
#include <openssl/experimental/kyber.h>

#include <benchmark/benchmark.h>

static void BM_KeyGeneration(benchmark::State &state) {
  KYBER_private_key priv;
  bssl::ScopedCBB priv_cbb;

  uint8_t encoded_public_key[KYBER_PUBLIC_KEY_BYTES];

  if (CBB_init(priv_cbb.get(), KYBER_PRIVATE_KEY_BYTES) != 1) {
    state.SkipWithError("Error: CBB_init");
  }

  for (auto _ : state) {
    KYBER_generate_key(encoded_public_key, &priv);

    if (KYBER_marshal_private_key(priv_cbb.get(), &priv) != 1) {
      state.SkipWithError("Error: KYBER_marshal_private_key");
    }
    const uint8_t *encoded_private_key = CBB_data(priv_cbb.get());
    if (encoded_private_key == nullptr) {
      state.SkipWithError("Error: CBB_data");
    }
  }
}

static void BM_Encapsulation(benchmark::State &state) {
  KYBER_public_key pub;
  KYBER_private_key priv;

  uint8_t encoded_public_key[KYBER_PUBLIC_KEY_BYTES];

  KYBER_generate_key(encoded_public_key, &priv);

  uint8_t ciphertext[KYBER_CIPHERTEXT_BYTES];
  uint8_t shared_secret[32];

  for (auto _ : state) {
    CBS encoded_public_key_cbs;
    CBS_init(&encoded_public_key_cbs, encoded_public_key,
             sizeof(encoded_public_key));
    if (KYBER_parse_public_key(&pub, &encoded_public_key_cbs) != 1) {
      state.SkipWithError("Error: KYBER_parse_public_key");
    }

    KYBER_encap(ciphertext, shared_secret, &pub);
  }
}

static void BM_Decapsulation(benchmark::State &state) {
  KYBER_private_key priv;
  uint8_t encoded_public_key[KYBER_PUBLIC_KEY_BYTES];

  KYBER_generate_key(encoded_public_key, &priv);

  bssl::ScopedCBB priv_cbb;
  if (CBB_init(priv_cbb.get(), KYBER_PRIVATE_KEY_BYTES) != 1) {
    state.SkipWithError("Error: CBB_init");
  }

  if (KYBER_marshal_private_key(priv_cbb.get(), &priv) != 1) {
    state.SkipWithError("Error: KYBER_marshal_private_key()");
  }

  const uint8_t *encoded_private_key = CBB_data(priv_cbb.get());
  if (encoded_private_key == nullptr) {
    state.SkipWithError("Error: CBB_data()");
  }

  // This ciphertext is nonsense, but Kyber decap is constant-time so, for the
  // purposes of timing, it's fine.
  uint8_t ciphertext[KYBER_CIPHERTEXT_BYTES];
  memset(ciphertext, 42, sizeof(ciphertext));

  uint8_t shared_secret[32];

  for (auto _ : state) {
    CBS encoded_private_key_cbs;
    CBS_init(&encoded_private_key_cbs, encoded_private_key,
             KYBER_PRIVATE_KEY_BYTES);
    if (!KYBER_parse_private_key(&priv, &encoded_private_key_cbs)) {
      state.SkipWithError("Error: KYBER_parse_private_key()");
    }

    KYBER_decap(shared_secret, ciphertext, &priv);
  }
}

BENCHMARK(BM_KeyGeneration);
BENCHMARK(BM_Encapsulation);
BENCHMARK(BM_Decapsulation);

BENCHMARK_MAIN();
