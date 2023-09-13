/* Copyright (c) 2014, Google Inc.
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
 * OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
 * CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE. */

#include <string>

#include <stdlib.h>

#include <openssl/bytestring.h>
#include <openssl/kyber.h>

#if defined(_WIN32)
#include <windows.h>
#elif defined(__APPLE__)
#include <sys/time.h>
#else
#include <time.h>
#endif

static const uint64_t SECONDS_TO_MEASURE_FOR = 1;

// TimeResults represents the results of benchmarking a function.
struct TimeResults {
  // num_calls is the number of function calls done in the time period.
  uint64_t num_calls;
  // us is the number of microseconds that elapsed in the time period.
  uint64_t us;

  void Print(const std::string &description) const {
    printf("Each %s operation took %f microseconds.\n", description.c_str(),
           static_cast<double>(us) / static_cast<double>(num_calls));
  }
};

#if defined(_WIN32)
static uint64_t time_now() { return GetTickCount64() * 1000; }
#elif defined(__APPLE__)
static uint64_t time_now() {
  struct timeval tv;
  uint64_t ret;

  gettimeofday(&tv, NULL);
  ret = tv.tv_sec;
  ret *= 1000000;
  ret += tv.tv_usec;
  return ret;
}
#else
static uint64_t time_now() {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);

  uint64_t ret = ts.tv_sec;
  ret *= 1000000;
  ret += ts.tv_nsec / 1000;
  return ret;
}
#endif


// IterationsBetweenTimeChecks returns the number of iterations of |func| to run
// in between checking the time, or zero on error.
static uint32_t IterationsBetweenTimeChecks(std::function<bool()> func) {
  uint64_t start = time_now();
  if (!func()) {
    return 0;
  }
  uint64_t delta = time_now() - start;
  if (delta == 0) {
    return 250;
  }

  // Aim for about 100ms between time checks.
  uint32_t ret = static_cast<double>(100000) / static_cast<double>(delta);
  if (ret > 1000) {
    ret = 1000;
  } else if (ret < 1) {
    ret = 1;
  }
  return ret;
}

static bool TimeFunctionImpl(TimeResults *results, std::function<bool()> func,
                             uint32_t iterations_between_time_checks) {
  // total_us is the total amount of time that we'll aim to measure a function
  // for.
  const uint64_t total_us = SECONDS_TO_MEASURE_FOR * 1000000;
  uint64_t start = time_now(), now;
  uint64_t done = 0;
  for (;;) {
    for (uint32_t i = 0; i < iterations_between_time_checks; i++) {
      if (!func()) {
        return false;
      }
      done++;
    }

    now = time_now();
    if (now - start > total_us) {
      break;
    }
  }

  results->us = now - start;
  results->num_calls = done;
  return true;
}

static bool TimeFunction(TimeResults *results, std::function<bool()> func) {
  uint32_t iterations_between_time_checks = IterationsBetweenTimeChecks(func);
  if (iterations_between_time_checks == 0) {
    return false;
  }

  return TimeFunctionImpl(results, std::move(func),
                          iterations_between_time_checks);
}

// N.B.: The libcrux Kyber API expects serialized byte arrays as input, and
// outputs serialized byte arrays. In order for the BoringSSL code being
// benchmarked to correspond to the libcrux code, we've included serialization
// and de-serialization code as part of the benchmarking where-ever appropriate.

static int benchmark_key_generation(void) {
  KYBER_private_key priv;
  bssl::ScopedCBB priv_cbb;

  uint8_t encoded_public_key[KYBER_PUBLIC_KEY_BYTES];

  if (CBB_init(priv_cbb.get(), KYBER_PRIVATE_KEY_BYTES) != 1) {
    fprintf(stderr, "Line %d: CBB_init failed.", __LINE__);
    return 1;
  }

  TimeResults results;
  if (!TimeFunction(&results, [&]() -> bool {
        KYBER_generate_key(encoded_public_key, &priv);

        if (KYBER_marshal_private_key(priv_cbb.get(), &priv) != 1) {
          return false;
        }
        const uint8_t *encoded_private_key = CBB_data(priv_cbb.get());
        if (encoded_private_key == nullptr) {
          return false;
        }

        return true;
      })) {
    fprintf(stderr, "Failed to time key generation.\n");
    return 1;
  }

  results.Print("Key-generation");

  return 0;
}

static int benchmark_encapsulation(void) {
  KYBER_public_key pub;

  KYBER_private_key priv;
  uint8_t encoded_public_key[KYBER_PUBLIC_KEY_BYTES];
  KYBER_generate_key(encoded_public_key, &priv);

  // This ciphertext is nonsense, but Kyber encap is constant-time so, for the
  // purposes of timing, it's fine.
  uint8_t ciphertext[KYBER_CIPHERTEXT_BYTES];
  memset(ciphertext, 42, sizeof(ciphertext));

  uint8_t shared_secret[32];

  TimeResults results;
  if (!TimeFunction(&results, [&]() -> bool {
        CBS encoded_public_key_cbs;
        CBS_init(&encoded_public_key_cbs, encoded_public_key,
                 sizeof(encoded_public_key));
        if (KYBER_parse_public_key(&pub, &encoded_public_key_cbs) != 1) {
          return 1;
        }

        KYBER_encap(ciphertext, shared_secret, sizeof(shared_secret), &pub);
        return true;
      })) {
    fprintf(stderr, "Failed to time encapsulation.\n");
    return 1;
  }

  results.Print("Encapsulation");

  return 0;
}

static int benchmark_decapsulation(void) {
  KYBER_private_key priv;
  uint8_t encoded_public_key[KYBER_PUBLIC_KEY_BYTES];
  KYBER_generate_key(encoded_public_key, &priv);

  bssl::ScopedCBB priv_cbb;
  if (CBB_init(priv_cbb.get(), KYBER_PRIVATE_KEY_BYTES) != 1) {
    fprintf(stderr, "Line %d: CBB_init failed.", __LINE__);
    return 1;
  }
  if (KYBER_marshal_private_key(priv_cbb.get(), &priv) != 1) {
    fprintf(stderr, "Line %d: KYBER_marshal_private_key() failed.\n", __LINE__);
    return 1;
  }
  const uint8_t *encoded_private_key = CBB_data(priv_cbb.get());
  if (encoded_private_key == nullptr) {
    fprintf(stderr, "Line %d: encoded_private_key is null.", __LINE__);
    return 1;
  }

  // This ciphertext is nonsense, but Kyber decap is constant-time so, for the
  // purposes of timing, it's fine.
  uint8_t ciphertext[KYBER_CIPHERTEXT_BYTES];
  memset(ciphertext, 42, sizeof(ciphertext));

  uint8_t shared_secret[32];

  TimeResults results;
  if (!TimeFunction(&results, [&]() -> bool {
        CBS encoded_private_key_cbs;
        CBS_init(&encoded_private_key_cbs, encoded_private_key,
                 KYBER_PRIVATE_KEY_BYTES);
        if (!KYBER_parse_private_key(&priv, &encoded_private_key_cbs)) {
          return 1;
        }

        KYBER_decap(shared_secret, sizeof(shared_secret), ciphertext, &priv);
        return true;
      })) {
    fprintf(stderr, "Failed to time decapsulation.\n");
    return 1;
  }
  results.Print("Decapsulation");

  return 0;
}

int main(void) {
  int rv = benchmark_key_generation();
  if (rv != 0) {
    return EXIT_FAILURE;
  }

  rv = benchmark_encapsulation();
  if (rv != 0) {
    return EXIT_FAILURE;
  }

  rv = benchmark_decapsulation();
  if (rv != 0) {
    return EXIT_FAILURE;
  }

  return EXIT_SUCCESS;
}
