
#include <gtest/gtest.h>
#include <nlohmann/json.hpp>

#include "libcrux_sha3_portable.h"

using namespace std;

typedef vector<uint8_t> bytes;

vector<uint8_t>
from_hex(const string &hex)
{
  if (hex.length() % 2 == 1)
  {
    throw invalid_argument("Odd-length hex string");
  }

  int len = static_cast<int>(hex.length()) / 2;
  vector<uint8_t> out(len);
  for (int i = 0; i < len; i += 1)
  {
    string byte = hex.substr(2 * i, 2);
    out[i] = static_cast<uint8_t>(strtol(byte.c_str(), nullptr, 16));
  }

  return out;
}

string
bytes_to_hex(const vector<uint8_t> &data)
{
  stringstream hex(ios_base::out);
  hex.flags(ios::hex);
  for (const auto &byte : data)
  {
    hex << setw(2) << setfill('0') << int(byte);
  }
  return hex.str();
}

TEST(Sha3Test, ConsistencyTest)
{
  const char *message = "Hello, World!";
  uint32_t message_size = strlen(message);

  {
    uint8_t digest[32];
    Eurydice_slice input;
    input.ptr = (void *)message;
    input.len = message_size;

    libcrux_sha3_sha256(input, digest);

    bytes expected_digest = from_hex(
        "1af17a664e3fa8e419b8ba05c2a173169df76162a5a286e0c405b460d478f7ef");

    EXPECT_EQ(strncmp((char *)digest,
                      (char *)expected_digest.data(),
                      32),
              0);
  }

  {
    uint8_t digest[64];
    Eurydice_slice input;
    input.ptr = (void *)message;
    input.len = message_size;

    libcrux_sha3_sha512(input, digest);

    bytes expected_digest = from_hex(
        "38e05c33d7b067127f217d8c856e554fcff09c9320b8a5979ce2ff5d95dd27ba35d1fba50c562dfd1d6cc48bc9c5baa4390894418cc942d968f97bcb659419ed");

    EXPECT_EQ(strncmp((char *)digest,
                      (char *)expected_digest.data(),
                      64),
              0);
  }

  {
    uint8_t digest[64];
    Eurydice_slice digest_slice;
    digest_slice.ptr = digest;
    digest_slice.len = 64;
    Eurydice_slice input;
    input.ptr = (void *)message;
    input.len = message_size;

    libcrux_sha3_portable_shake128(digest_slice, input);

    bytes expected_digest = from_hex(
        "2bf5e6dee6079fad604f573194ba8426bd4d30eb13e8ba2edae70e529b570cbdd588f2c5dd4e465dfbafaa7c5634249c8929dc04165a9edb26be19ce036196d1");

    EXPECT_EQ(strncmp((char *)digest,
                      (char *)expected_digest.data(),
                      64),
              0);

    libcrux_sha3_generic_keccak_KeccakState_17 state = libcrux_sha3_portable_incremental_shake128_init();
    libcrux_sha3_portable_incremental_shake128_absorb_final(&state, input);

    uint8_t randomness0[504U];
    Eurydice_slice randomness;
    randomness.ptr = randomness0;
    randomness.len = 64;
    libcrux_sha3_portable_incremental_shake128_squeeze_first_three_blocks(
        &state, randomness);

    EXPECT_EQ(strncmp((char *)randomness0,
                      (char *)expected_digest.data(),
                      64),
              0);
  }

  {
    uint8_t digest[64];
    Eurydice_slice digest_slice;
    digest_slice.ptr = digest;
    digest_slice.len = 64;
    Eurydice_slice input;
    input.ptr = (void *)message;
    input.len = message_size;

    libcrux_sha3_portable_shake256(digest_slice, input);

    bytes expected_digest = from_hex(
        "b3be97bfd978833a65588ceae8a34cf59e95585af62063e6b89d0789f372424e8b0d1be4f21b40ce5a83a438473271e0661854f02d431db74e6904d6c347d757");

    EXPECT_EQ(strncmp((char *)digest,
                      (char *)expected_digest.data(),
                      64),
              0);
  }
}
