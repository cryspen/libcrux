window.BENCHMARK_DATA = {
  "lastUpdate": 1741086815024,
  "repoUrl": "https://github.com/cryspen/libcrux",
  "entries": {
    "ML-KEM Benchmark": [
      {
        "commit": {
          "author": {
            "name": "clara",
            "username": "wysiwys",
            "email": "144733119+wysiwys@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "01f8b3b4c0deed07a341ca0d3b388c2569058a16",
          "message": "Merge pull request #869 from cryspen/wysiwys/fix-mlkem-benchmarks\n\n[CI] Fix for ML-KEM benchmark: remove step to clear `Cargo.lock`",
          "timestamp": "2025-03-04T10:53:42Z",
          "url": "https://github.com/cryspen/libcrux/commit/01f8b3b4c0deed07a341ca0d3b388c2569058a16"
        },
        "date": 1741086814234,
        "tool": "cargo",
        "benches": [
          {
            "name": "ML-KEM mlkem512 Key Generation/portable (external random)",
            "value": 48055,
            "range": "± 2500",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem512 Key Generation/unpacked portable (external random)",
            "value": 47794,
            "range": "± 408",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem768 Key Generation/portable (external random)",
            "value": 76805,
            "range": "± 1752",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem768 Key Generation/unpacked portable (external random)",
            "value": 76629,
            "range": "± 1480",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem1024 Key Generation/portable (external random)",
            "value": 120062,
            "range": "± 4274",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem1024 Key Generation/unpacked portable (external random)",
            "value": 119275,
            "range": "± 1434",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem512 Encapsulation/portable (external random)",
            "value": 56187,
            "range": "± 1802",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem512 Encapsulation/unpacked portable (external random)",
            "value": 23458,
            "range": "± 293",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem768 Encapsulation/portable (external random)",
            "value": 84179,
            "range": "± 1198",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem768 Encapsulation/unpacked portable (external random)",
            "value": 30871,
            "range": "± 299",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem1024 Encapsulation/portable (external random)",
            "value": 129151,
            "range": "± 1818",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem1024 Encapsulation/unpacked portable (external random)",
            "value": 43185,
            "range": "± 439",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem512 Decapsulation/portable",
            "value": 59069,
            "range": "± 1136",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem512 Decapsulation/unpacked portable",
            "value": 39269,
            "range": "± 619",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem768 Decapsulation/portable",
            "value": 93246,
            "range": "± 1686",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem768 Decapsulation/unpacked portable",
            "value": 54247,
            "range": "± 397",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem1024 Decapsulation/portable",
            "value": 141487,
            "range": "± 7150",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem1024 Decapsulation/unpacked portable",
            "value": 72832,
            "range": "± 750",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem512 PK Validation/portable",
            "value": 1061,
            "range": "± 77",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem768 PK Validation/portable",
            "value": 1583,
            "range": "± 130",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem1024 PK Validation/portable",
            "value": 2071,
            "range": "± 136",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem512 Key Generation/portable (external random)",
            "value": 47982,
            "range": "± 422",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem512 Key Generation/unpacked portable (external random)",
            "value": 47768,
            "range": "± 384",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem768 Key Generation/portable (external random)",
            "value": 76956,
            "range": "± 2546",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem768 Key Generation/unpacked portable (external random)",
            "value": 76476,
            "range": "± 1778",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem1024 Key Generation/portable (external random)",
            "value": 119983,
            "range": "± 1267",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem1024 Key Generation/unpacked portable (external random)",
            "value": 119053,
            "range": "± 1787",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem512 Encapsulation/portable (external random)",
            "value": 56184,
            "range": "± 1554",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem512 Encapsulation/unpacked portable (external random)",
            "value": 23589,
            "range": "± 862",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem768 Encapsulation/portable (external random)",
            "value": 84226,
            "range": "± 1416",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem768 Encapsulation/unpacked portable (external random)",
            "value": 30813,
            "range": "± 1054",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem1024 Encapsulation/portable (external random)",
            "value": 130015,
            "range": "± 1839",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem1024 Encapsulation/unpacked portable (external random)",
            "value": 43267,
            "range": "± 2980",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem512 Decapsulation/portable",
            "value": 58400,
            "range": "± 1191",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem512 Decapsulation/unpacked portable",
            "value": 39213,
            "range": "± 181",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem768 Decapsulation/portable",
            "value": 93155,
            "range": "± 964",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem768 Decapsulation/unpacked portable",
            "value": 53251,
            "range": "± 373",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem1024 Decapsulation/portable",
            "value": 142145,
            "range": "± 1743",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem1024 Decapsulation/unpacked portable",
            "value": 73405,
            "range": "± 573",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem512 PK Validation/portable",
            "value": 1061,
            "range": "± 104",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem768 PK Validation/portable",
            "value": 1581,
            "range": "± 119",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem1024 PK Validation/portable",
            "value": 2064,
            "range": "± 140",
            "unit": "ns/iter"
          }
        ]
      }
    ]
  }
}