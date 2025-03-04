window.BENCHMARK_DATA = {
  "lastUpdate": 1741087802427,
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
      },
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
        "date": 1741086869658,
        "tool": "cargo",
        "benches": [
          {
            "name": "ML-KEM mlkem512 Key Generation/portable (external random)",
            "value": 10221,
            "range": "± 328",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem512 Key Generation/unpacked portable (external random)",
            "value": 9664,
            "range": "± 315",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem512 Key Generation/neon (external random)",
            "value": 5153,
            "range": "± 71",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem512 Key Generation/unpacked neon (external random)",
            "value": 5044,
            "range": "± 67",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem768 Key Generation/portable (external random)",
            "value": 15916,
            "range": "± 244",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem768 Key Generation/unpacked portable (external random)",
            "value": 15680,
            "range": "± 198",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem768 Key Generation/neon (external random)",
            "value": 9764,
            "range": "± 283",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem768 Key Generation/unpacked neon (external random)",
            "value": 9561,
            "range": "± 419",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem1024 Key Generation/portable (external random)",
            "value": 26689,
            "range": "± 2340",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem1024 Key Generation/unpacked portable (external random)",
            "value": 26440,
            "range": "± 1980",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem1024 Key Generation/neon (external random)",
            "value": 14347,
            "range": "± 684",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem1024 Key Generation/unpacked neon (external random)",
            "value": 14022,
            "range": "± 2128",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem512 Encapsulation/portable (external random)",
            "value": 11752,
            "range": "± 853",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem512 Encapsulation/unpacked portable (external random)",
            "value": 6258,
            "range": "± 363",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem512 Encapsulation/neon (external random)",
            "value": 6110,
            "range": "± 416",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem512 Encapsulation/unpacked neon (external random)",
            "value": 3062,
            "range": "± 193",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem768 Encapsulation/portable (external random)",
            "value": 20144,
            "range": "± 1958",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem768 Encapsulation/unpacked portable (external random)",
            "value": 8512,
            "range": "± 566",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem768 Encapsulation/neon (external random)",
            "value": 11133,
            "range": "± 619",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem768 Encapsulation/unpacked neon (external random)",
            "value": 4442,
            "range": "± 417",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem1024 Encapsulation/portable (external random)",
            "value": 29403,
            "range": "± 2752",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem1024 Encapsulation/unpacked portable (external random)",
            "value": 12589,
            "range": "± 1369",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem1024 Encapsulation/neon (external random)",
            "value": 15326,
            "range": "± 820",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem1024 Encapsulation/unpacked neon (external random)",
            "value": 5567,
            "range": "± 564",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem512 Decapsulation/portable",
            "value": 13516,
            "range": "± 896",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem512 Decapsulation/unpacked portable",
            "value": 9461,
            "range": "± 876",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem512 Decapsulation/neon",
            "value": 6905,
            "range": "± 630",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem512 Decapsulation/unpacked neon",
            "value": 4989,
            "range": "± 1180",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem768 Decapsulation/portable",
            "value": 21135,
            "range": "± 674",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem768 Decapsulation/unpacked portable",
            "value": 12491,
            "range": "± 680",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem768 Decapsulation/neon",
            "value": 12117,
            "range": "± 479",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem768 Decapsulation/unpacked neon",
            "value": 7400,
            "range": "± 602",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem1024 Decapsulation/portable",
            "value": 31558,
            "range": "± 1042",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem1024 Decapsulation/unpacked portable",
            "value": 16868,
            "range": "± 969",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem1024 Decapsulation/neon",
            "value": 16613,
            "range": "± 1116",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem1024 Decapsulation/unpacked neon",
            "value": 9702,
            "range": "± 1186",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem512 PK Validation/portable",
            "value": 600,
            "range": "± 224",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem512 PK Validation/neon",
            "value": 460,
            "range": "± 129",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem768 PK Validation/portable",
            "value": 908,
            "range": "± 407",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem768 PK Validation/neon",
            "value": 676,
            "range": "± 204",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem1024 PK Validation/portable",
            "value": 1200,
            "range": "± 524",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem1024 PK Validation/neon",
            "value": 953,
            "range": "± 201",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem512 Key Generation/portable (external random)",
            "value": 10396,
            "range": "± 312",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem512 Key Generation/unpacked portable (external random)",
            "value": 10196,
            "range": "± 383",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem768 Key Generation/portable (external random)",
            "value": 17301,
            "range": "± 994",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem768 Key Generation/unpacked portable (external random)",
            "value": 17058,
            "range": "± 1646",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem1024 Key Generation/portable (external random)",
            "value": 27374,
            "range": "± 2180",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem1024 Key Generation/unpacked portable (external random)",
            "value": 27190,
            "range": "± 933",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem512 Encapsulation/portable (external random)",
            "value": 11558,
            "range": "± 600",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem512 Encapsulation/unpacked portable (external random)",
            "value": 6473,
            "range": "± 484",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem768 Encapsulation/portable (external random)",
            "value": 18891,
            "range": "± 786",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem768 Encapsulation/unpacked portable (external random)",
            "value": 8797,
            "range": "± 507",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem1024 Encapsulation/portable (external random)",
            "value": 29085,
            "range": "± 1732",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem1024 Encapsulation/unpacked portable (external random)",
            "value": 12285,
            "range": "± 1099",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem512 Decapsulation/portable",
            "value": 13809,
            "range": "± 668",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem512 Decapsulation/unpacked portable",
            "value": 9349,
            "range": "± 626",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem768 Decapsulation/portable",
            "value": 21334,
            "range": "± 1179",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem768 Decapsulation/unpacked portable",
            "value": 13524,
            "range": "± 1350",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem1024 Decapsulation/portable",
            "value": 33174,
            "range": "± 2596",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem1024 Decapsulation/unpacked portable",
            "value": 17579,
            "range": "± 1259",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem512 PK Validation/portable",
            "value": 587,
            "range": "± 166",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem768 PK Validation/portable",
            "value": 923,
            "range": "± 707",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem1024 PK Validation/portable",
            "value": 1202,
            "range": "± 454",
            "unit": "ns/iter"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "franziskuskiefer",
            "email": "franziskuskiefer@gmail.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "1f71b003eaf1f03f2c58792800556ddaea4c71dd",
          "message": "Merge pull request #860 from cryspen/franziskus/mlkem-c-update\n\nmlkem c update",
          "timestamp": "2025-03-04T11:10:17Z",
          "url": "https://github.com/cryspen/libcrux/commit/1f71b003eaf1f03f2c58792800556ddaea4c71dd"
        },
        "date": 1741087801381,
        "tool": "cargo",
        "benches": [
          {
            "name": "ML-KEM mlkem512 Key Generation/portable (external random)",
            "value": 49147,
            "range": "± 2109",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem512 Key Generation/unpacked portable (external random)",
            "value": 48947,
            "range": "± 433",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem768 Key Generation/portable (external random)",
            "value": 76572,
            "range": "± 766",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem768 Key Generation/unpacked portable (external random)",
            "value": 75606,
            "range": "± 1064",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem1024 Key Generation/portable (external random)",
            "value": 119476,
            "range": "± 1637",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem1024 Key Generation/unpacked portable (external random)",
            "value": 120496,
            "range": "± 1516",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem512 Encapsulation/portable (external random)",
            "value": 53002,
            "range": "± 1021",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem512 Encapsulation/unpacked portable (external random)",
            "value": 26156,
            "range": "± 144",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem768 Encapsulation/portable (external random)",
            "value": 84781,
            "range": "± 881",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem768 Encapsulation/unpacked portable (external random)",
            "value": 30932,
            "range": "± 415",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem1024 Encapsulation/portable (external random)",
            "value": 131480,
            "range": "± 2107",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem1024 Encapsulation/unpacked portable (external random)",
            "value": 42708,
            "range": "± 417",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem512 Decapsulation/portable",
            "value": 59317,
            "range": "± 664",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem512 Decapsulation/unpacked portable",
            "value": 42205,
            "range": "± 144",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem768 Decapsulation/portable",
            "value": 92902,
            "range": "± 955",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem768 Decapsulation/unpacked portable",
            "value": 52462,
            "range": "± 854",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem1024 Decapsulation/portable",
            "value": 140392,
            "range": "± 1601",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem1024 Decapsulation/unpacked portable",
            "value": 72367,
            "range": "± 767",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem512 PK Validation/portable",
            "value": 1059,
            "range": "± 58",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem768 PK Validation/portable",
            "value": 1550,
            "range": "± 83",
            "unit": "ns/iter"
          },
          {
            "name": "ML-KEM mlkem1024 PK Validation/portable",
            "value": 2096,
            "range": "± 31",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem512 Key Generation/portable (external random)",
            "value": 49231,
            "range": "± 612",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem512 Key Generation/unpacked portable (external random)",
            "value": 48749,
            "range": "± 795",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem768 Key Generation/portable (external random)",
            "value": 76682,
            "range": "± 919",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem768 Key Generation/unpacked portable (external random)",
            "value": 75555,
            "range": "± 931",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem1024 Key Generation/portable (external random)",
            "value": 119283,
            "range": "± 1275",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem1024 Key Generation/unpacked portable (external random)",
            "value": 120118,
            "range": "± 1548",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem512 Encapsulation/portable (external random)",
            "value": 53231,
            "range": "± 526",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem512 Encapsulation/unpacked portable (external random)",
            "value": 26331,
            "range": "± 460",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem768 Encapsulation/portable (external random)",
            "value": 84771,
            "range": "± 1031",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem768 Encapsulation/unpacked portable (external random)",
            "value": 30987,
            "range": "± 381",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem1024 Encapsulation/portable (external random)",
            "value": 130712,
            "range": "± 2061",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem1024 Encapsulation/unpacked portable (external random)",
            "value": 43284,
            "range": "± 402",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem512 Decapsulation/portable",
            "value": 59167,
            "range": "± 390",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem512 Decapsulation/unpacked portable",
            "value": 42343,
            "range": "± 476",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem768 Decapsulation/portable",
            "value": 92785,
            "range": "± 1049",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem768 Decapsulation/unpacked portable",
            "value": 52784,
            "range": "± 330",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem1024 Decapsulation/portable",
            "value": 140501,
            "range": "± 1620",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem1024 Decapsulation/unpacked portable",
            "value": 73697,
            "range": "± 672",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem512 PK Validation/portable",
            "value": 1062,
            "range": "± 77",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem768 PK Validation/portable",
            "value": 1547,
            "range": "± 112",
            "unit": "ns/iter"
          },
          {
            "name": "portable ML-KEM mlkem1024 PK Validation/portable",
            "value": 2098,
            "range": "± 148",
            "unit": "ns/iter"
          }
        ]
      }
    ]
  }
}