
#include <gtest/gtest.h>
#include <nlohmann/json.hpp>

#include "libcrux_sha3.h"
#include "libcrux_sha3_avx2.h"

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

TEST(Shake256X4Test, ConsistencyTest)
{
    const char* message = "Hello, World!";
    uint32_t message_size = strlen(message);

    uint8_t digest0[32];
    uint8_t digest1[32];
    uint8_t digest2[32];
    uint8_t digest3[32];


    Eurydice_slice input;
    input.ptr = (void*) message;
    input.len = message_size;

    Eurydice_slice output0;
    output0.ptr = (void*) digest0;
    output0.len = 32;

    Eurydice_slice output1;
    output1.ptr = (void*) digest1;
    output1.len = 32;

    Eurydice_slice output2;
    output2.ptr = (void*) digest2;
    output2.len = 32;

    Eurydice_slice output3;
    output3.ptr = (void*) digest3;
    output3.len = 32;

    libcrux_sha3_avx2_x4_shake256(input,input,input,input,
				  output0,output1,output2,output3);

    bytes expected_digest = from_hex(
      "b3be97bfd978833a65588ceae8a34cf59e95585af62063e6b89d0789f372424e");

    EXPECT_EQ(strncmp((char*)digest0,
                      (char*)expected_digest.data(),
                      32),
              0);
    EXPECT_EQ(strncmp((char*)digest1,
                      (char*)expected_digest.data(),
                      32),
              0);
    EXPECT_EQ(strncmp((char*)digest2,
                      (char*)expected_digest.data(),
                      32),
              0);
    EXPECT_EQ(strncmp((char*)digest3,
                      (char*)expected_digest.data(),
                      32),
              0);
}
