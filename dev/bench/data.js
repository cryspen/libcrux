window.BENCHMARK_DATA = {
  "lastUpdate": 1724685950020,
  "repoUrl": "https://github.com/cryspen/libcrux",
  "entries": {
    "ML-KEM Benchmark": [
      {
        "commit": {
          "author": {
            "name": "Jan Winkelmann",
            "username": "keks",
            "email": "146678+keks@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "ab901d247e24a7f42b4ba6c791d33856fe1f2ab6",
          "message": "Merge pull request #525 from cryspen/keks/towards-merge-queue-and-bench-graphs\n\nRework Actions to work well with Merge Queues and Enable Benchmarks in there",
          "timestamp": "2024-08-26T14:46:40Z",
          "url": "https://github.com/cryspen/libcrux/commit/ab901d247e24a7f42b4ba6c791d33856fe1f2ab6"
        },
        "date": 1724685504156,
        "tool": "cargo",
        "benches": [
          {
            "name": "ChaCha20Poly1305 Encrypt/libcrux/10 MB",
            "value": 14372104,
            "range": "± 611298",
            "unit": "ns/iter"
          },
          {
            "name": "ChaCha20Poly1305 Encrypt/Ring/10 MB",
            "value": 7138020,
            "range": "± 1457118",
            "unit": "ns/iter"
          },
          {
            "name": "ChaCha20Poly1305 Encrypt/RustCrypto/10 MB",
            "value": 35960917,
            "range": "± 2049725",
            "unit": "ns/iter"
          },
          {
            "name": "ChaCha20Poly1305 Encrypt/OpenSSL/10 MB",
            "value": 6901916,
            "range": "± 255227",
            "unit": "ns/iter"
          },
          {
            "name": "ChaCha20Poly1305 Decrypt/libcrux/10 MB",
            "value": 14047645,
            "range": "± 1001736",
            "unit": "ns/iter"
          },
          {
            "name": "ChaCha20Poly1305 Decrypt/Ring/10 MB",
            "value": 9194041,
            "range": "± 1658643",
            "unit": "ns/iter"
          },
          {
            "name": "ChaCha20Poly1305 Decrypt/RustCrypto/10 MB",
            "value": 43128292,
            "range": "± 7923733",
            "unit": "ns/iter"
          },
          {
            "name": "ChaCha20Poly1305 Decrypt/OpenSSL/10 MB",
            "value": 7155500,
            "range": "± 1066619",
            "unit": "ns/iter"
          },
          {
            "name": "Drbg/libcrux Sha256",
            "value": 4099,
            "range": "± 162",
            "unit": "ns/iter"
          },
          {
            "name": "Drbg/libcrux Sha256 #2",
            "value": 2515,
            "range": "± 88",
            "unit": "ns/iter"
          },
          {
            "name": "Drbg/Ring",
            "value": 367,
            "range": "± 26",
            "unit": "ns/iter"
          },
          {
            "name": "Drbg/RustCrypto",
            "value": 408,
            "range": "± 55",
            "unit": "ns/iter"
          },
          {
            "name": "Drbg/OpenSSL",
            "value": 224,
            "range": "± 8",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 PK Validation/libcrux portable",
            "value": 349,
            "range": "± 108",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Key Generation/libcrux portable (external random)",
            "value": 16881,
            "range": "± 1591",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Key Generation/libcrux portable (HACL-DRBG)",
            "value": 23672,
            "range": "± 513",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Key Generation/libcrux portable (OsRng)",
            "value": 20875,
            "range": "± 897",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Key Generation/pqclean reference implementation",
            "value": 7782,
            "range": "± 179",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Encapsulation/libcrux portable (external random)",
            "value": 22856,
            "range": "± 1012",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Encapsulation/libcrux portable",
            "value": 23925,
            "range": "± 751",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Encapsulation/libcrux portable OsRng",
            "value": 21934,
            "range": "± 654",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Encapsulation/pqclean reference implementation",
            "value": 8836,
            "range": "± 226",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Decapsulation/libcrux portable",
            "value": 24477,
            "range": "± 876",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Decapsulation/pqclean reference implementation",
            "value": 12000,
            "range": "± 1055",
            "unit": "ns/iter"
          },
          {
            "name": "P256 derive/libcrux",
            "value": 111690,
            "range": "± 1721",
            "unit": "ns/iter"
          },
          {
            "name": "P256 derive/Ring",
            "value": 39691,
            "range": "± 1212",
            "unit": "ns/iter"
          },
          {
            "name": "P256 derive/RustCrypto",
            "value": 103687,
            "range": "± 2209",
            "unit": "ns/iter"
          },
          {
            "name": "P256 secret to public/libcrux",
            "value": 51345,
            "range": "± 1637",
            "unit": "ns/iter"
          },
          {
            "name": "P256 secret to public/Ring",
            "value": 10146,
            "range": "± 325",
            "unit": "ns/iter"
          },
          {
            "name": "P256 secret to public/RustCrypto",
            "value": 109533,
            "range": "± 7431",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/libcrux/100",
            "value": 445,
            "range": "± 37",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/RustCrypto/100",
            "value": 421,
            "range": "± 20",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/OpenSSL/100",
            "value": 257,
            "range": "± 11",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/libcrux/1 KB",
            "value": 3591,
            "range": "± 109",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/RustCrypto/1 KB",
            "value": 3306,
            "range": "± 62",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/OpenSSL/1 KB",
            "value": 643,
            "range": "± 17",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/libcrux/2 KB",
            "value": 6971,
            "range": "± 398",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/RustCrypto/2 KB",
            "value": 6360,
            "range": "± 95",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/OpenSSL/2 KB",
            "value": 1082,
            "range": "± 42",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/libcrux/4 KB",
            "value": 14269,
            "range": "± 425",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/RustCrypto/4 KB",
            "value": 13275,
            "range": "± 566",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/OpenSSL/4 KB",
            "value": 1974,
            "range": "± 150",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/libcrux/8 KB",
            "value": 25460,
            "range": "± 805",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/RustCrypto/8 KB",
            "value": 23930,
            "range": "± 586",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/OpenSSL/8 KB",
            "value": 3563,
            "range": "± 105",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/libcrux/100",
            "value": 413,
            "range": "± 23",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/Ring/100",
            "value": 69,
            "range": "± 4",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/RustCrypto/100",
            "value": 397,
            "range": "± 10",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/OpenSSL/100",
            "value": 249,
            "range": "± 10",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/libcrux/1 KB",
            "value": 3384,
            "range": "± 114",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/Ring/1 KB",
            "value": 474,
            "range": "± 10",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/RustCrypto/1 KB",
            "value": 3228,
            "range": "± 94",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/OpenSSL/1 KB",
            "value": 631,
            "range": "± 12",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/libcrux/2 KB",
            "value": 6743,
            "range": "± 186",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/Ring/2 KB",
            "value": 890,
            "range": "± 18",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/RustCrypto/2 KB",
            "value": 6076,
            "range": "± 167",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/OpenSSL/2 KB",
            "value": 1084,
            "range": "± 35",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/libcrux/4 KB",
            "value": 12823,
            "range": "± 266",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/Ring/4 KB",
            "value": 1757,
            "range": "± 94",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/RustCrypto/4 KB",
            "value": 11925,
            "range": "± 295",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/OpenSSL/4 KB",
            "value": 1892,
            "range": "± 51",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/libcrux/8 KB",
            "value": 25454,
            "range": "± 595",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/Ring/8 KB",
            "value": 3394,
            "range": "± 69",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/RustCrypto/8 KB",
            "value": 24430,
            "range": "± 1581",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/OpenSSL/8 KB",
            "value": 3555,
            "range": "± 107",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/libcrux/100",
            "value": 258,
            "range": "± 7",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/Ring/100",
            "value": 228,
            "range": "± 5",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/RustCrypto/100",
            "value": 246,
            "range": "± 6",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/OpenSSL/100",
            "value": 327,
            "range": "± 22",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/libcrux/1 KB",
            "value": 2423,
            "range": "± 174",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/Ring/1 KB",
            "value": 2074,
            "range": "± 366",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/RustCrypto/1 KB",
            "value": 2341,
            "range": "± 249",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/OpenSSL/1 KB",
            "value": 1131,
            "range": "± 78",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/libcrux/2 KB",
            "value": 4776,
            "range": "± 683",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/Ring/2 KB",
            "value": 3846,
            "range": "± 239",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/RustCrypto/2 KB",
            "value": 4393,
            "range": "± 211",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/OpenSSL/2 KB",
            "value": 1937,
            "range": "± 102",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/libcrux/4 KB",
            "value": 8729,
            "range": "± 1171",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/Ring/4 KB",
            "value": 7335,
            "range": "± 543",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/RustCrypto/4 KB",
            "value": 7848,
            "range": "± 329",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/OpenSSL/4 KB",
            "value": 3317,
            "range": "± 249",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/libcrux/8 KB",
            "value": 16651,
            "range": "± 513",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/Ring/8 KB",
            "value": 14391,
            "range": "± 407",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/RustCrypto/8 KB",
            "value": 15862,
            "range": "± 130",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/OpenSSL/8 KB",
            "value": 6436,
            "range": "± 78",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/libcrux/100",
            "value": 276,
            "range": "± 7",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/Ring/100",
            "value": 251,
            "range": "± 12",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/RustCrypto/100",
            "value": 259,
            "range": "± 16",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/OpenSSL/100",
            "value": 342,
            "range": "± 15",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/libcrux/1 KB",
            "value": 2431,
            "range": "± 197",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/Ring/1 KB",
            "value": 2123,
            "range": "± 388",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/RustCrypto/1 KB",
            "value": 2832,
            "range": "± 560",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/OpenSSL/1 KB",
            "value": 1208,
            "range": "± 147",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/libcrux/2 KB",
            "value": 4741,
            "range": "± 645",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/Ring/2 KB",
            "value": 3972,
            "range": "± 457",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/RustCrypto/2 KB",
            "value": 5617,
            "range": "± 1245",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/OpenSSL/2 KB",
            "value": 1998,
            "range": "± 355",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/libcrux/4 KB",
            "value": 9544,
            "range": "± 1613",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/Ring/4 KB",
            "value": 7680,
            "range": "± 1404",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/RustCrypto/4 KB",
            "value": 8380,
            "range": "± 391",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/OpenSSL/4 KB",
            "value": 3740,
            "range": "± 740",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/libcrux/8 KB",
            "value": 17652,
            "range": "± 1549",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/Ring/8 KB",
            "value": 14388,
            "range": "± 924",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/RustCrypto/8 KB",
            "value": 15418,
            "range": "± 540",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/OpenSSL/8 KB",
            "value": 6015,
            "range": "± 343",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 224/libcrux/10 MB",
            "value": 18079666,
            "range": "± 739972",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 224/RustCrypto/10 MB",
            "value": 16346531,
            "range": "± 390639",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 224/OpenSSL/10 MB",
            "value": 11328739,
            "range": "± 320186",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 256/libcrux/10 MB",
            "value": 19571072,
            "range": "± 492991",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 256/RustCrypto/10 MB",
            "value": 17541198,
            "range": "± 450162",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 256/OpenSSL/10 MB",
            "value": 11841333,
            "range": "± 303833",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 384/libcrux/10 MB",
            "value": 25415874,
            "range": "± 1152168",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 384/RustCrypto/10 MB",
            "value": 22954312,
            "range": "± 582786",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 384/OpenSSL/10 MB",
            "value": 15172417,
            "range": "± 529369",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 512/libcrux/10 MB",
            "value": 36210479,
            "range": "± 1095792",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 512/RustCrypto/10 MB",
            "value": 32374708,
            "range": "± 833077",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 512/OpenSSL/10 MB",
            "value": 21986781,
            "range": "± 418728",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/derive/libcrux",
            "value": 31522,
            "range": "± 1559",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/derive/Ring",
            "value": 30546,
            "range": "± 957",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/derive/OpenSSL",
            "value": 31048,
            "range": "± 903",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/derive/Dalek",
            "value": 34644,
            "range": "± 567",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/derive/Dalek Ristretto",
            "value": 30181,
            "range": "± 1375",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/secret to public/libcrux",
            "value": 30959,
            "range": "± 441",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/secret to public/Ring",
            "value": 11837,
            "range": "± 181",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/secret to public/OpenSSL",
            "value": 31554,
            "range": "± 648",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/secret to public/Dalek",
            "value": 11862,
            "range": "± 375",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/secret to public/Dalek Ristretto",
            "value": 8596,
            "range": "± 223",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox create/libcrux",
            "value": 262766,
            "range": "± 19396",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox create/Ring",
            "value": 181932,
            "range": "± 6731",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox create/OpenSSL",
            "value": 269259,
            "range": "± 15650",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox create/Dalek",
            "value": 203760,
            "range": "± 11178",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox create/Dalek Ristretto",
            "value": 169166,
            "range": "± 9775",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox process/libcrux",
            "value": 33870,
            "range": "± 1123",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox process/Ring",
            "value": 33200,
            "range": "± 1694",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox process/OpenSSL",
            "value": 33085,
            "range": "± 1443",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox process/Dalek",
            "value": 37411,
            "range": "± 1525",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox process/Dalek Ristretto",
            "value": 30823,
            "range": "± 2788",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx create/libcrux",
            "value": 258668,
            "range": "± 10454",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx create/Ring",
            "value": 172564,
            "range": "± 9616",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx create/OpenSSL",
            "value": 253279,
            "range": "± 9398",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx create/Dalek",
            "value": 192119,
            "range": "± 4944",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx create/Dalek Ristretto",
            "value": 176172,
            "range": "± 2939",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx process/libcrux",
            "value": 66339,
            "range": "± 1962",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx process/Ring",
            "value": 65035,
            "range": "± 1425",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx process/OpenSSL",
            "value": 65389,
            "range": "± 1164",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx process/Dalek",
            "value": 76136,
            "range": "± 5684",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx process/Dalek Ristretto",
            "value": 64257,
            "range": "± 2575",
            "unit": "ns/iter"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Jan Winkelmann",
            "username": "keks",
            "email": "146678+keks@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "ab901d247e24a7f42b4ba6c791d33856fe1f2ab6",
          "message": "Merge pull request #525 from cryspen/keks/towards-merge-queue-and-bench-graphs\n\nRework Actions to work well with Merge Queues and Enable Benchmarks in there",
          "timestamp": "2024-08-26T14:46:40Z",
          "url": "https://github.com/cryspen/libcrux/commit/ab901d247e24a7f42b4ba6c791d33856fe1f2ab6"
        },
        "date": 1724685631262,
        "tool": "cargo",
        "benches": [
          {
            "name": "ChaCha20Poly1305 Encrypt/libcrux/10 MB",
            "value": 5235177,
            "range": "± 14366",
            "unit": "ns/iter"
          },
          {
            "name": "ChaCha20Poly1305 Encrypt/Ring/10 MB",
            "value": 4276120,
            "range": "± 145322",
            "unit": "ns/iter"
          },
          {
            "name": "ChaCha20Poly1305 Encrypt/RustCrypto/10 MB",
            "value": 7971730,
            "range": "± 205745",
            "unit": "ns/iter"
          },
          {
            "name": "ChaCha20Poly1305 Encrypt/OpenSSL/10 MB",
            "value": 5212665,
            "range": "± 108646",
            "unit": "ns/iter"
          },
          {
            "name": "ChaCha20Poly1305 Decrypt/libcrux/10 MB",
            "value": 5277406,
            "range": "± 67148",
            "unit": "ns/iter"
          },
          {
            "name": "ChaCha20Poly1305 Decrypt/Ring/10 MB",
            "value": 4307235,
            "range": "± 131449",
            "unit": "ns/iter"
          },
          {
            "name": "ChaCha20Poly1305 Decrypt/RustCrypto/10 MB",
            "value": 7973813,
            "range": "± 181941",
            "unit": "ns/iter"
          },
          {
            "name": "ChaCha20Poly1305 Decrypt/OpenSSL/10 MB",
            "value": 5193208,
            "range": "± 186359",
            "unit": "ns/iter"
          },
          {
            "name": "Drbg/libcrux Sha256",
            "value": 5357,
            "range": "± 27",
            "unit": "ns/iter"
          },
          {
            "name": "Drbg/libcrux Sha256 #2",
            "value": 3186,
            "range": "± 213",
            "unit": "ns/iter"
          },
          {
            "name": "Drbg/Ring",
            "value": 491,
            "range": "± 21",
            "unit": "ns/iter"
          },
          {
            "name": "Drbg/RustCrypto",
            "value": 522,
            "range": "± 11",
            "unit": "ns/iter"
          },
          {
            "name": "Drbg/OpenSSL",
            "value": 937,
            "range": "± 2",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 PK Validation/libcrux portable",
            "value": 478,
            "range": "± 36",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Key Generation/libcrux portable (external random)",
            "value": 23575,
            "range": "± 480",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Key Generation/libcrux portable (HACL-DRBG)",
            "value": 32077,
            "range": "± 171",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Key Generation/libcrux portable (OsRng)",
            "value": 28626,
            "range": "± 334",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Key Generation/pqclean reference implementation",
            "value": 13934,
            "range": "± 45",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Key Generation/libjade kyber avx2",
            "value": 12198,
            "range": "± 30",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Encapsulation/libcrux portable (external random)",
            "value": 25202,
            "range": "± 576",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Encapsulation/libcrux portable",
            "value": 32688,
            "range": "± 324",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Encapsulation/libcrux portable OsRng",
            "value": 29942,
            "range": "± 1302",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Encapsulation/pqclean reference implementation",
            "value": 13872,
            "range": "± 118",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Encapsulation/libjade kyber avx2",
            "value": 16426,
            "range": "± 42",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Decapsulation/libcrux portable",
            "value": 32945,
            "range": "± 656",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Decapsulation/pqclean reference implementation",
            "value": 14850,
            "range": "± 199",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Decapsulation/libjade kyber avx2",
            "value": 14333,
            "range": "± 277",
            "unit": "ns/iter"
          },
          {
            "name": "P256 derive/libcrux",
            "value": 383488,
            "range": "± 10827",
            "unit": "ns/iter"
          },
          {
            "name": "P256 derive/Ring",
            "value": 50962,
            "range": "± 1427",
            "unit": "ns/iter"
          },
          {
            "name": "P256 derive/RustCrypto",
            "value": 134600,
            "range": "± 3097",
            "unit": "ns/iter"
          },
          {
            "name": "P256 secret to public/libcrux",
            "value": 158128,
            "range": "± 196",
            "unit": "ns/iter"
          },
          {
            "name": "P256 secret to public/Ring",
            "value": 11979,
            "range": "± 40",
            "unit": "ns/iter"
          },
          {
            "name": "P256 secret to public/RustCrypto",
            "value": 134272,
            "range": "± 167",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/libcrux/100",
            "value": 538,
            "range": "± 3",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/RustCrypto/100",
            "value": 68,
            "range": "± 4",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/OpenSSL/100",
            "value": 386,
            "range": "± 5",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/libcrux/1 KB",
            "value": 4278,
            "range": "± 234",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/RustCrypto/1 KB",
            "value": 668,
            "range": "± 28",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/OpenSSL/1 KB",
            "value": 992,
            "range": "± 5",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/libcrux/2 KB",
            "value": 8258,
            "range": "± 39",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/RustCrypto/2 KB",
            "value": 1305,
            "range": "± 6",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/OpenSSL/2 KB",
            "value": 1634,
            "range": "± 12",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/libcrux/4 KB",
            "value": 16215,
            "range": "± 130",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/RustCrypto/4 KB",
            "value": 2585,
            "range": "± 18",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/OpenSSL/4 KB",
            "value": 2920,
            "range": "± 12",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/libcrux/8 KB",
            "value": 32145,
            "range": "± 255",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/RustCrypto/8 KB",
            "value": 5142,
            "range": "± 58",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/OpenSSL/8 KB",
            "value": 5494,
            "range": "± 22",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/libcrux/100",
            "value": 541,
            "range": "± 8",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/Ring/100",
            "value": 119,
            "range": "± 3",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/RustCrypto/100",
            "value": 66,
            "range": "± 3",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/OpenSSL/100",
            "value": 394,
            "range": "± 4",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/libcrux/1 KB",
            "value": 4275,
            "range": "± 11",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/Ring/1 KB",
            "value": 732,
            "range": "± 2",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/RustCrypto/1 KB",
            "value": 667,
            "range": "± 3",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/OpenSSL/1 KB",
            "value": 1004,
            "range": "± 13",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/libcrux/2 KB",
            "value": 8258,
            "range": "± 258",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/Ring/2 KB",
            "value": 1377,
            "range": "± 4",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/RustCrypto/2 KB",
            "value": 1309,
            "range": "± 9",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/OpenSSL/2 KB",
            "value": 1648,
            "range": "± 9",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/libcrux/4 KB",
            "value": 16228,
            "range": "± 90",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/Ring/4 KB",
            "value": 2655,
            "range": "± 9",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/RustCrypto/4 KB",
            "value": 2586,
            "range": "± 22",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/OpenSSL/4 KB",
            "value": 2939,
            "range": "± 17",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/libcrux/8 KB",
            "value": 32133,
            "range": "± 56",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/Ring/8 KB",
            "value": 5215,
            "range": "± 17",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/RustCrypto/8 KB",
            "value": 5148,
            "range": "± 29",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/OpenSSL/8 KB",
            "value": 5505,
            "range": "± 76",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/libcrux/100",
            "value": 386,
            "range": "± 3",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/Ring/100",
            "value": 278,
            "range": "± 10",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/RustCrypto/100",
            "value": 238,
            "range": "± 3",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/OpenSSL/100",
            "value": 549,
            "range": "± 4",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/libcrux/1 KB",
            "value": 3076,
            "range": "± 18",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/Ring/1 KB",
            "value": 2179,
            "range": "± 13",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/RustCrypto/1 KB",
            "value": 1864,
            "range": "± 149",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/OpenSSL/1 KB",
            "value": 1896,
            "range": "± 20",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/libcrux/2 KB",
            "value": 5699,
            "range": "± 39",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/Ring/2 KB",
            "value": 4071,
            "range": "± 29",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/RustCrypto/2 KB",
            "value": 3446,
            "range": "± 134",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/OpenSSL/2 KB",
            "value": 3239,
            "range": "± 140",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/libcrux/4 KB",
            "value": 10941,
            "range": "± 721",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/Ring/4 KB",
            "value": 7862,
            "range": "± 29",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/RustCrypto/4 KB",
            "value": 6626,
            "range": "± 151",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/OpenSSL/4 KB",
            "value": 5930,
            "range": "± 60",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/libcrux/8 KB",
            "value": 21393,
            "range": "± 194",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/Ring/8 KB",
            "value": 15430,
            "range": "± 33",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/RustCrypto/8 KB",
            "value": 12959,
            "range": "± 32",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/OpenSSL/8 KB",
            "value": 11305,
            "range": "± 103",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/libcrux/100",
            "value": 378,
            "range": "± 9",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/Ring/100",
            "value": 278,
            "range": "± 3",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/RustCrypto/100",
            "value": 237,
            "range": "± 7",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/OpenSSL/100",
            "value": 562,
            "range": "± 11",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/libcrux/1 KB",
            "value": 3062,
            "range": "± 32",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/Ring/1 KB",
            "value": 2177,
            "range": "± 33",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/RustCrypto/1 KB",
            "value": 1857,
            "range": "± 53",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/OpenSSL/1 KB",
            "value": 1917,
            "range": "± 24",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/libcrux/2 KB",
            "value": 5675,
            "range": "± 26",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/Ring/2 KB",
            "value": 4067,
            "range": "± 47",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/RustCrypto/2 KB",
            "value": 3437,
            "range": "± 16",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/OpenSSL/2 KB",
            "value": 3257,
            "range": "± 23",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/libcrux/4 KB",
            "value": 10896,
            "range": "± 87",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/Ring/4 KB",
            "value": 7856,
            "range": "± 31",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/RustCrypto/4 KB",
            "value": 6613,
            "range": "± 27",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/OpenSSL/4 KB",
            "value": 5954,
            "range": "± 58",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/libcrux/8 KB",
            "value": 21362,
            "range": "± 177",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/Ring/8 KB",
            "value": 15426,
            "range": "± 71",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/RustCrypto/8 KB",
            "value": 12943,
            "range": "± 91",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/OpenSSL/8 KB",
            "value": 11315,
            "range": "± 301",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 224/libcrux/10 MB",
            "value": 57491616,
            "range": "± 372921",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 224/RustCrypto/10 MB",
            "value": 24116576,
            "range": "± 159661",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 224/OpenSSL/10 MB",
            "value": 23285280,
            "range": "± 696959",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 256/libcrux/10 MB",
            "value": 61016866,
            "range": "± 2453098",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 256/RustCrypto/10 MB",
            "value": 25525711,
            "range": "± 237219",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 256/OpenSSL/10 MB",
            "value": 24636683,
            "range": "± 68247",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 384/libcrux/10 MB",
            "value": 79371964,
            "range": "± 526479",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 384/RustCrypto/10 MB",
            "value": 33282688,
            "range": "± 227589",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 384/OpenSSL/10 MB",
            "value": 29994562,
            "range": "± 208443",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 512/libcrux/10 MB",
            "value": 112497296,
            "range": "± 2237596",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 512/RustCrypto/10 MB",
            "value": 48157765,
            "range": "± 1649010",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 512/OpenSSL/10 MB",
            "value": 43166531,
            "range": "± 891285",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/derive/libcrux",
            "value": 37375,
            "range": "± 760",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/derive/Ring",
            "value": 42713,
            "range": "± 341",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/derive/OpenSSL",
            "value": 37919,
            "range": "± 282",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/derive/Dalek",
            "value": 53802,
            "range": "± 254",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/derive/Dalek Ristretto",
            "value": 28039,
            "range": "± 173",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/secret to public/libcrux",
            "value": 37336,
            "range": "± 944",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/secret to public/Ring",
            "value": 38003,
            "range": "± 715",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/secret to public/OpenSSL",
            "value": 47016,
            "range": "± 297",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/secret to public/Dalek",
            "value": 16228,
            "range": "± 64",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/secret to public/Dalek Ristretto",
            "value": 12110,
            "range": "± 327",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox create/libcrux",
            "value": 299071,
            "range": "± 1126",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox create/Ring",
            "value": 323859,
            "range": "± 12578",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox create/OpenSSL",
            "value": 330148,
            "range": "± 2174",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox create/Dalek",
            "value": 281463,
            "range": "± 5201",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox create/Dalek Ristretto",
            "value": 154822,
            "range": "± 1018",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox process/libcrux",
            "value": 37382,
            "range": "± 116",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox process/Ring",
            "value": 42707,
            "range": "± 1031",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox process/OpenSSL",
            "value": 37960,
            "range": "± 862",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox process/Dalek",
            "value": 53812,
            "range": "± 232",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox process/Dalek Ristretto",
            "value": 28042,
            "range": "± 95",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx create/libcrux",
            "value": 298860,
            "range": "± 558",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx create/Ring",
            "value": 322940,
            "range": "± 2281",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx create/OpenSSL",
            "value": 330199,
            "range": "± 2574",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx create/Dalek",
            "value": 283206,
            "range": "± 1356",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx create/Dalek Ristretto",
            "value": 169104,
            "range": "± 3573",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx process/libcrux",
            "value": 74806,
            "range": "± 1449",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx process/Ring",
            "value": 85482,
            "range": "± 3625",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx process/OpenSSL",
            "value": 75842,
            "range": "± 4507",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx process/Dalek",
            "value": 107872,
            "range": "± 679",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx process/Dalek Ristretto",
            "value": 52537,
            "range": "± 304",
            "unit": "ns/iter"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Jan Winkelmann",
            "username": "keks",
            "email": "146678+keks@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "ab901d247e24a7f42b4ba6c791d33856fe1f2ab6",
          "message": "Merge pull request #525 from cryspen/keks/towards-merge-queue-and-bench-graphs\n\nRework Actions to work well with Merge Queues and Enable Benchmarks in there",
          "timestamp": "2024-08-26T14:46:40Z",
          "url": "https://github.com/cryspen/libcrux/commit/ab901d247e24a7f42b4ba6c791d33856fe1f2ab6"
        },
        "date": 1724685698487,
        "tool": "cargo",
        "benches": [
          {
            "name": "ChaCha20Poly1305 Encrypt/libcrux/10 MB",
            "value": 53002794,
            "range": "± 378073",
            "unit": "ns/iter"
          },
          {
            "name": "ChaCha20Poly1305 Encrypt/Ring/10 MB",
            "value": 25921985,
            "range": "± 151598",
            "unit": "ns/iter"
          },
          {
            "name": "ChaCha20Poly1305 Encrypt/RustCrypto/10 MB",
            "value": 10686172,
            "range": "± 28461",
            "unit": "ns/iter"
          },
          {
            "name": "ChaCha20Poly1305 Decrypt/libcrux/10 MB",
            "value": 52941008,
            "range": "± 174571",
            "unit": "ns/iter"
          },
          {
            "name": "ChaCha20Poly1305 Decrypt/Ring/10 MB",
            "value": 26248911,
            "range": "± 62894",
            "unit": "ns/iter"
          },
          {
            "name": "ChaCha20Poly1305 Decrypt/RustCrypto/10 MB",
            "value": 10815611,
            "range": "± 30993",
            "unit": "ns/iter"
          },
          {
            "name": "Drbg/libcrux Sha256",
            "value": 6158,
            "range": "± 32",
            "unit": "ns/iter"
          },
          {
            "name": "Drbg/libcrux Sha256 #2",
            "value": 3667,
            "range": "± 18",
            "unit": "ns/iter"
          },
          {
            "name": "Drbg/Ring",
            "value": 521,
            "range": "± 2",
            "unit": "ns/iter"
          },
          {
            "name": "Drbg/RustCrypto",
            "value": 570,
            "range": "± 2",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 PK Validation/libcrux portable",
            "value": 906,
            "range": "± 176",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Key Generation/libcrux portable (external random)",
            "value": 46523,
            "range": "± 625",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Key Generation/libcrux portable (HACL-DRBG)",
            "value": 55959,
            "range": "± 421",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Key Generation/libcrux portable (OsRng)",
            "value": 52009,
            "range": "± 78",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Key Generation/pqclean reference implementation",
            "value": 132541,
            "range": "± 890",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Encapsulation/libcrux portable (external random)",
            "value": 50436,
            "range": "± 788",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Encapsulation/libcrux portable",
            "value": 58869,
            "range": "± 911",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Encapsulation/libcrux portable OsRng",
            "value": 55511,
            "range": "± 476",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Encapsulation/pqclean reference implementation",
            "value": 148827,
            "range": "± 529",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Decapsulation/libcrux portable",
            "value": 58925,
            "range": "± 771",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Decapsulation/pqclean reference implementation",
            "value": 169995,
            "range": "± 1100",
            "unit": "ns/iter"
          },
          {
            "name": "P256 derive/libcrux",
            "value": 1954345,
            "range": "± 9484",
            "unit": "ns/iter"
          },
          {
            "name": "P256 derive/Ring",
            "value": 840320,
            "range": "± 12754",
            "unit": "ns/iter"
          },
          {
            "name": "P256 derive/RustCrypto",
            "value": 492188,
            "range": "± 1075",
            "unit": "ns/iter"
          },
          {
            "name": "P256 secret to public/libcrux",
            "value": 836576,
            "range": "± 12609",
            "unit": "ns/iter"
          },
          {
            "name": "P256 secret to public/Ring",
            "value": 301966,
            "range": "± 3948",
            "unit": "ns/iter"
          },
          {
            "name": "P256 secret to public/RustCrypto",
            "value": 491054,
            "range": "± 774",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/libcrux/100",
            "value": 626,
            "range": "± 24",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/RustCrypto/100",
            "value": 74,
            "range": "± 3",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/libcrux/1 KB",
            "value": 4750,
            "range": "± 50",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/RustCrypto/1 KB",
            "value": 732,
            "range": "± 31",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/libcrux/2 KB",
            "value": 9147,
            "range": "± 100",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/RustCrypto/2 KB",
            "value": 1428,
            "range": "± 56",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/libcrux/4 KB",
            "value": 17919,
            "range": "± 174",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/RustCrypto/4 KB",
            "value": 2821,
            "range": "± 109",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/libcrux/8 KB",
            "value": 35541,
            "range": "± 393",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/RustCrypto/8 KB",
            "value": 5610,
            "range": "± 227",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/libcrux/100",
            "value": 623,
            "range": "± 3",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/Ring/100",
            "value": 625,
            "range": "± 2",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/RustCrypto/100",
            "value": 74,
            "range": "± 3",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/libcrux/1 KB",
            "value": 4744,
            "range": "± 42",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/Ring/1 KB",
            "value": 4902,
            "range": "± 67",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/RustCrypto/1 KB",
            "value": 729,
            "range": "± 28",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/libcrux/2 KB",
            "value": 9142,
            "range": "± 115",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/Ring/2 KB",
            "value": 9475,
            "range": "± 91",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/RustCrypto/2 KB",
            "value": 1431,
            "range": "± 57",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/libcrux/4 KB",
            "value": 17904,
            "range": "± 211",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/Ring/4 KB",
            "value": 18587,
            "range": "± 147",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/RustCrypto/4 KB",
            "value": 2830,
            "range": "± 118",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/libcrux/8 KB",
            "value": 35519,
            "range": "± 389",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/Ring/8 KB",
            "value": 36862,
            "range": "± 308",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/RustCrypto/8 KB",
            "value": 5636,
            "range": "± 236",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/libcrux/100",
            "value": 1618,
            "range": "± 14",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/Ring/100",
            "value": 762,
            "range": "± 4",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/RustCrypto/100",
            "value": 779,
            "range": "± 2",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/libcrux/1 KB",
            "value": 13859,
            "range": "± 346",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/Ring/1 KB",
            "value": 6110,
            "range": "± 54",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/RustCrypto/1 KB",
            "value": 6697,
            "range": "± 47",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/libcrux/2 KB",
            "value": 26119,
            "range": "± 105",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/Ring/2 KB",
            "value": 11461,
            "range": "± 102",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/RustCrypto/2 KB",
            "value": 12563,
            "range": "± 482",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/libcrux/4 KB",
            "value": 50583,
            "range": "± 323",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/Ring/4 KB",
            "value": 22089,
            "range": "± 346",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/RustCrypto/4 KB",
            "value": 24314,
            "range": "± 441",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/libcrux/8 KB",
            "value": 99575,
            "range": "± 661",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/Ring/8 KB",
            "value": 43453,
            "range": "± 568",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/RustCrypto/8 KB",
            "value": 47803,
            "range": "± 379",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/libcrux/100",
            "value": 1604,
            "range": "± 9",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/Ring/100",
            "value": 762,
            "range": "± 4",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/RustCrypto/100",
            "value": 778,
            "range": "± 3",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/libcrux/1 KB",
            "value": 13843,
            "range": "± 44",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/Ring/1 KB",
            "value": 6109,
            "range": "± 47",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/RustCrypto/1 KB",
            "value": 6683,
            "range": "± 51",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/libcrux/2 KB",
            "value": 26100,
            "range": "± 134",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/Ring/2 KB",
            "value": 11442,
            "range": "± 115",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/RustCrypto/2 KB",
            "value": 12581,
            "range": "± 135",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/libcrux/4 KB",
            "value": 50596,
            "range": "± 102",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/Ring/4 KB",
            "value": 22095,
            "range": "± 219",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/RustCrypto/4 KB",
            "value": 24312,
            "range": "± 152",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/libcrux/8 KB",
            "value": 99640,
            "range": "± 1075",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/Ring/8 KB",
            "value": 43455,
            "range": "± 418",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/RustCrypto/8 KB",
            "value": 47795,
            "range": "± 364",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 224/libcrux/10 MB",
            "value": 219801887,
            "range": "± 363274",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 224/RustCrypto/10 MB",
            "value": 60099503,
            "range": "± 93499",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 256/libcrux/10 MB",
            "value": 233223064,
            "range": "± 537011",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 256/RustCrypto/10 MB",
            "value": 64070284,
            "range": "± 390549",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 384/libcrux/10 MB",
            "value": 304884654,
            "range": "± 577083",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 384/RustCrypto/10 MB",
            "value": 84533112,
            "range": "± 246088",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 512/libcrux/10 MB",
            "value": 439958396,
            "range": "± 3776829",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 512/RustCrypto/10 MB",
            "value": 120079764,
            "range": "± 2553706",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/derive/libcrux",
            "value": 315888,
            "range": "± 1838",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/derive/Ring",
            "value": 153887,
            "range": "± 1911",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/derive/Dalek",
            "value": 179491,
            "range": "± 581",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/derive/Dalek Ristretto",
            "value": 156534,
            "range": "± 699",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/secret to public/libcrux",
            "value": 315775,
            "range": "± 6368",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/secret to public/Ring",
            "value": 96929,
            "range": "± 497",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/secret to public/Dalek",
            "value": 53870,
            "range": "± 160",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/secret to public/Dalek Ristretto",
            "value": 42884,
            "range": "± 153",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox create/libcrux",
            "value": 2527034,
            "range": "± 3978",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox create/Ring",
            "value": 1003375,
            "range": "± 11710",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox create/Dalek",
            "value": 933961,
            "range": "± 14798",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox create/Dalek Ristretto",
            "value": 798657,
            "range": "± 1323",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox process/libcrux",
            "value": 315965,
            "range": "± 2211",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox process/Ring",
            "value": 153919,
            "range": "± 1177",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox process/Dalek",
            "value": 179470,
            "range": "± 1646",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox process/Dalek Ristretto",
            "value": 156604,
            "range": "± 1016",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx create/libcrux",
            "value": 2527254,
            "range": "± 12850",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx create/Ring",
            "value": 1003009,
            "range": "± 12476",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx create/Dalek",
            "value": 935940,
            "range": "± 16383",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx create/Dalek Ristretto",
            "value": 850108,
            "range": "± 1456",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx process/libcrux",
            "value": 631843,
            "range": "± 1047",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx process/Ring",
            "value": 307309,
            "range": "± 2483",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx process/Dalek",
            "value": 358951,
            "range": "± 1489",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx process/Dalek Ristretto",
            "value": 313165,
            "range": "± 1661",
            "unit": "ns/iter"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Jan Winkelmann",
            "username": "keks",
            "email": "146678+keks@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "ab901d247e24a7f42b4ba6c791d33856fe1f2ab6",
          "message": "Merge pull request #525 from cryspen/keks/towards-merge-queue-and-bench-graphs\n\nRework Actions to work well with Merge Queues and Enable Benchmarks in there",
          "timestamp": "2024-08-26T14:46:40Z",
          "url": "https://github.com/cryspen/libcrux/commit/ab901d247e24a7f42b4ba6c791d33856fe1f2ab6"
        },
        "date": 1724685933362,
        "tool": "cargo",
        "benches": [
          {
            "name": "ChaCha20Poly1305 Encrypt/libcrux/10 MB",
            "value": 6559260,
            "range": "± 148386",
            "unit": "ns/iter"
          },
          {
            "name": "ChaCha20Poly1305 Encrypt/Ring/10 MB",
            "value": 4489008,
            "range": "± 107376",
            "unit": "ns/iter"
          },
          {
            "name": "ChaCha20Poly1305 Encrypt/RustCrypto/10 MB",
            "value": 10189087,
            "range": "± 216170",
            "unit": "ns/iter"
          },
          {
            "name": "ChaCha20Poly1305 Decrypt/libcrux/10 MB",
            "value": 6539825,
            "range": "± 41552",
            "unit": "ns/iter"
          },
          {
            "name": "ChaCha20Poly1305 Decrypt/Ring/10 MB",
            "value": 4495262,
            "range": "± 77261",
            "unit": "ns/iter"
          },
          {
            "name": "ChaCha20Poly1305 Decrypt/RustCrypto/10 MB",
            "value": 8259283,
            "range": "± 36927",
            "unit": "ns/iter"
          },
          {
            "name": "Drbg/libcrux Sha256",
            "value": 4927,
            "range": "± 130",
            "unit": "ns/iter"
          },
          {
            "name": "Drbg/libcrux Sha256 #2",
            "value": 3213,
            "range": "± 13",
            "unit": "ns/iter"
          },
          {
            "name": "Drbg/Ring",
            "value": 80,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "Drbg/RustCrypto",
            "value": 123,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 PK Validation/libcrux portable",
            "value": 578,
            "range": "± 138",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Key Generation/libcrux portable (external random)",
            "value": 22851,
            "range": "± 333",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Key Generation/libcrux portable (HACL-DRBG)",
            "value": 31428,
            "range": "± 213",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Key Generation/libcrux portable (OsRng)",
            "value": 27445,
            "range": "± 111",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Key Generation/pqclean reference implementation",
            "value": 65663,
            "range": "± 741",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Encapsulation/libcrux portable (external random)",
            "value": 25275,
            "range": "± 399",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Encapsulation/libcrux portable",
            "value": 32767,
            "range": "± 425",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Encapsulation/libcrux portable OsRng",
            "value": 29530,
            "range": "± 433",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Encapsulation/pqclean reference implementation",
            "value": 82303,
            "range": "± 725",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Decapsulation/libcrux portable",
            "value": 32755,
            "range": "± 587",
            "unit": "ns/iter"
          },
          {
            "name": "Kyber768 Decapsulation/pqclean reference implementation",
            "value": 102290,
            "range": "± 1613",
            "unit": "ns/iter"
          },
          {
            "name": "P256 derive/libcrux",
            "value": 1115446,
            "range": "± 4976",
            "unit": "ns/iter"
          },
          {
            "name": "P256 derive/Ring",
            "value": 51318,
            "range": "± 353",
            "unit": "ns/iter"
          },
          {
            "name": "P256 derive/RustCrypto",
            "value": 141710,
            "range": "± 760",
            "unit": "ns/iter"
          },
          {
            "name": "P256 secret to public/libcrux",
            "value": 480821,
            "range": "± 3930",
            "unit": "ns/iter"
          },
          {
            "name": "P256 secret to public/Ring",
            "value": 11959,
            "range": "± 48",
            "unit": "ns/iter"
          },
          {
            "name": "P256 secret to public/RustCrypto",
            "value": 141750,
            "range": "± 530",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/libcrux/100",
            "value": 600,
            "range": "± 11",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/RustCrypto/100",
            "value": 72,
            "range": "± 2",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/libcrux/1 KB",
            "value": 4218,
            "range": "± 253",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/RustCrypto/1 KB",
            "value": 675,
            "range": "± 309",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/libcrux/2 KB",
            "value": 8062,
            "range": "± 128",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/RustCrypto/2 KB",
            "value": 1318,
            "range": "± 16",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/libcrux/4 KB",
            "value": 15775,
            "range": "± 208",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/RustCrypto/4 KB",
            "value": 2606,
            "range": "± 12",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/libcrux/8 KB",
            "value": 31199,
            "range": "± 123",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 224/RustCrypto/8 KB",
            "value": 5175,
            "range": "± 21",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/libcrux/100",
            "value": 596,
            "range": "± 2",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/Ring/100",
            "value": 130,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/RustCrypto/100",
            "value": 71,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/libcrux/1 KB",
            "value": 4226,
            "range": "± 32",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/Ring/1 KB",
            "value": 736,
            "range": "± 19",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/RustCrypto/1 KB",
            "value": 675,
            "range": "± 4",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/libcrux/2 KB",
            "value": 8063,
            "range": "± 35",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/Ring/2 KB",
            "value": 1393,
            "range": "± 5",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/RustCrypto/2 KB",
            "value": 1319,
            "range": "± 22",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/libcrux/4 KB",
            "value": 15787,
            "range": "± 77",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/Ring/4 KB",
            "value": 2681,
            "range": "± 12",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/RustCrypto/4 KB",
            "value": 2608,
            "range": "± 10",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/libcrux/8 KB",
            "value": 31194,
            "range": "± 263",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/Ring/8 KB",
            "value": 5245,
            "range": "± 115",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 256/RustCrypto/8 KB",
            "value": 5182,
            "range": "± 29",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/libcrux/100",
            "value": 441,
            "range": "± 3",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/Ring/100",
            "value": 282,
            "range": "± 9",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/RustCrypto/100",
            "value": 251,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/libcrux/1 KB",
            "value": 3112,
            "range": "± 14",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/Ring/1 KB",
            "value": 2184,
            "range": "± 14",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/RustCrypto/1 KB",
            "value": 1883,
            "range": "± 15",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/libcrux/2 KB",
            "value": 5752,
            "range": "± 24",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/Ring/2 KB",
            "value": 4075,
            "range": "± 32",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/RustCrypto/2 KB",
            "value": 3484,
            "range": "± 44",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/libcrux/4 KB",
            "value": 11086,
            "range": "± 629",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/Ring/4 KB",
            "value": 7859,
            "range": "± 43",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/RustCrypto/4 KB",
            "value": 6669,
            "range": "± 92",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/libcrux/8 KB",
            "value": 21664,
            "range": "± 101",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/Ring/8 KB",
            "value": 15406,
            "range": "± 94",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 384/RustCrypto/8 KB",
            "value": 13029,
            "range": "± 80",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/libcrux/100",
            "value": 447,
            "range": "± 4",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/Ring/100",
            "value": 282,
            "range": "± 2",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/RustCrypto/100",
            "value": 247,
            "range": "± 26",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/libcrux/1 KB",
            "value": 3067,
            "range": "± 15",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/Ring/1 KB",
            "value": 2186,
            "range": "± 40",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/RustCrypto/1 KB",
            "value": 1880,
            "range": "± 7",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/libcrux/2 KB",
            "value": 5681,
            "range": "± 86",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/Ring/2 KB",
            "value": 4073,
            "range": "± 582",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/RustCrypto/2 KB",
            "value": 3480,
            "range": "± 19",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/libcrux/4 KB",
            "value": 10914,
            "range": "± 43",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/Ring/4 KB",
            "value": 7853,
            "range": "± 175",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/RustCrypto/4 KB",
            "value": 6658,
            "range": "± 26",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/libcrux/8 KB",
            "value": 21366,
            "range": "± 108",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/Ring/8 KB",
            "value": 15405,
            "range": "± 74",
            "unit": "ns/iter"
          },
          {
            "name": "Sha2 512/RustCrypto/8 KB",
            "value": 13019,
            "range": "± 65",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 224/libcrux/10 MB",
            "value": 60937050,
            "range": "± 615207",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 224/RustCrypto/10 MB",
            "value": 24437600,
            "range": "± 127290",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 256/libcrux/10 MB",
            "value": 64518900,
            "range": "± 416258",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 256/RustCrypto/10 MB",
            "value": 25856925,
            "range": "± 166993",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 384/libcrux/10 MB",
            "value": 84344650,
            "range": "± 497475",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 384/RustCrypto/10 MB",
            "value": 33715800,
            "range": "± 226233",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 512/libcrux/10 MB",
            "value": 121055000,
            "range": "± 960595",
            "unit": "ns/iter"
          },
          {
            "name": "Sha3 512/RustCrypto/10 MB",
            "value": 48602250,
            "range": "± 228695",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/derive/libcrux",
            "value": 171977,
            "range": "± 1221",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/derive/Ring",
            "value": 56124,
            "range": "± 559",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/derive/Dalek",
            "value": 55231,
            "range": "± 341",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/derive/Dalek Ristretto",
            "value": 30453,
            "range": "± 127",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/secret to public/libcrux",
            "value": 172103,
            "range": "± 1957",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/secret to public/Ring",
            "value": 49737,
            "range": "± 175",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/secret to public/Dalek",
            "value": 18702,
            "range": "± 203",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/secret to public/Dalek Ristretto",
            "value": 14647,
            "range": "± 69",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox create/libcrux",
            "value": 1375340,
            "range": "± 6749",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox create/Ring",
            "value": 427938,
            "range": "± 2344",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox create/Dalek",
            "value": 296697,
            "range": "± 2038",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox create/Dalek Ristretto",
            "value": 174002,
            "range": "± 705",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox process/libcrux",
            "value": 171984,
            "range": "± 697",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox process/Ring",
            "value": 56163,
            "range": "± 1417",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox process/Dalek",
            "value": 55244,
            "range": "± 348",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym outfox process/Dalek Ristretto",
            "value": 30446,
            "range": "± 135",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx create/libcrux",
            "value": 1376511,
            "range": "± 11767",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx create/Ring",
            "value": 427967,
            "range": "± 3111",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx create/Dalek",
            "value": 298690,
            "range": "± 1120",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx create/Dalek Ristretto",
            "value": 192514,
            "range": "± 611",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx process/libcrux",
            "value": 343936,
            "range": "± 2966",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx process/Ring",
            "value": 112227,
            "range": "± 1050",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx process/Dalek",
            "value": 110708,
            "range": "± 883",
            "unit": "ns/iter"
          },
          {
            "name": "x25519/nym sphinx process/Dalek Ristretto",
            "value": 57675,
            "range": "± 316",
            "unit": "ns/iter"
          }
        ]
      }
    ]
  }
}