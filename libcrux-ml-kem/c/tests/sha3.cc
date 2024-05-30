
#include <gtest/gtest.h>
#include <nlohmann/json.hpp>

#include "libcrux_sha3.h"
#include "libcrux_mlkem768.h"

using namespace std;

typedef vector<uint8_t> bytes;

vector<uint8_t>
from_hex(const string& hex)
{
  if (hex.length() % 2 == 1) {
    throw invalid_argument("Odd-length hex string");
  }

  int len = static_cast<int>(hex.length()) / 2;
  vector<uint8_t> out(len);
  for (int i = 0; i < len; i += 1) {
    string byte = hex.substr(2 * i, 2);
    out[i] = static_cast<uint8_t>(strtol(byte.c_str(), nullptr, 16));
  }

  return out;
}

string
bytes_to_hex(const vector<uint8_t>& data)
{
  stringstream hex(ios_base::out);
  hex.flags(ios::hex);
  for (const auto& byte : data) {
    hex << setw(2) << setfill('0') << int(byte);
  }
  return hex.str();
}

TEST(Sha3Test, ConsistencyTest)
{
    const char* message = "Hello, World!";
    uint32_t message_size = strlen(message);

    uint8_t digest[32];
    Eurydice_slice input;
    input.ptr = (void*) message;
    input.len = message_size;

    libcrux_sha3_sha256(input,digest);

    bytes expected_digest = from_hex(
      "1af17a664e3fa8e419b8ba05c2a173169df76162a5a286e0c405b460d478f7ef");

    EXPECT_EQ(strncmp((char*)digest,
                      (char*)expected_digest.data(),
                      32),
              0);
}

#define KYBER768_SECRETKEYBYTES 2400
#define KYBER768_PUBLICKEYBYTES 1184
#define KYBER768_CIPHERTEXTBYTES 1088
#define KYBER768_SHAREDSECRETBYTES 32

TEST(Kyber768Test, ConsistencyTest)
{
  uint8_t randomness[64] = { 0 };
  uint8_t publicKey[KYBER768_PUBLICKEYBYTES];
  uint8_t secretKey[KYBER768_SECRETKEYBYTES];

  libcrux_ml_kem_types_MlKemKeyPair____2400size_t__1184size_t kp =
    libcrux_ml_kem_mlkem768_generate_key_pair(randomness);

  uint8_t ciphertext[KYBER768_CIPHERTEXTBYTES];
  K___libcrux_ml_kem_types_MlKemCiphertext___1088size_t___uint8_t_32size_t_ cipher_and_shared_secret =
  libcrux_ml_kem_mlkem768_encapsulate(&kp.pk, randomness);

  uint8_t sharedSecret2[KYBER768_SHAREDSECRETBYTES];
  libcrux_ml_kem_mlkem768_decapsulate(&kp.sk, &cipher_and_shared_secret.fst, sharedSecret2);

  EXPECT_EQ(0, memcmp(cipher_and_shared_secret.snd, sharedSecret2, KYBER768_SHAREDSECRETBYTES));
}

