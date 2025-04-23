window.BENCHMARK_DATA = {
  "lastUpdate": 1745397428418,
  "repoUrl": "https://github.com/cryspen/libcrux",
  "entries": {
    "ML-KEM Benchmark": [
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
          "id": "6c39188104f5b15b05fd8fbe5cf204ef51019a05",
          "message": "Merge pull request #912 from cryspen/wysiwys/mlkem-benchmark-update\n\nUpdate ML-KEM benchmarking workflow to use new benchmarking actions",
          "timestamp": "2025-04-08T08:29:25Z",
          "url": "https://github.com/cryspen/libcrux/commit/6c39188104f5b15b05fd8fbe5cf204ef51019a05"
        },
        "date": 1744111246169,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 49393,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 562",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 48771,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1008",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 76675,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 825",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 75660,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 3319",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 119452,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1103",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 120077,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 2602",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 53184,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 706",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 26252,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 230",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 84878,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1078",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 30825,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 404",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 130997,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 2568",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 43572,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 537",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 59470,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 601",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 42272,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 238",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 92770,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 989",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 52426,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 630",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 140560,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1834",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 71773,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 682",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 1057,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 67",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 1541,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 88",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 2080,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 33",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
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
          "id": "6c39188104f5b15b05fd8fbe5cf204ef51019a05",
          "message": "Merge pull request #912 from cryspen/wysiwys/mlkem-benchmark-update\n\nUpdate ML-KEM benchmarking workflow to use new benchmarking actions",
          "timestamp": "2025-04-08T08:29:25Z",
          "url": "https://github.com/cryspen/libcrux/commit/6c39188104f5b15b05fd8fbe5cf204ef51019a05"
        },
        "date": 1744111438327,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 10681,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 705",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 9462,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 517",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 5107,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 52",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 4962,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 103",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 16551,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 533",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 16184,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 550",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 9505,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 256",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 9473,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 187",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 24973,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 464",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 24849,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 466",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 13266,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 121",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 13231,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 214",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 10645,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 241",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5733,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 248",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 5638,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 183",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 2750,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 82",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 18003,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 293",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 8494,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 666",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 10883,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 344",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 4216,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 293",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 28968,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 822",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 11783,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 893",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 15324,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1301",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5457,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 303",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 13168,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 610",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 9227,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 290",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 7018,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 399",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon"
          },
          {
            "name": "Decapsulation",
            "value": 5068,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 265",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 21663,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 698",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 12903,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 644",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 11671,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 304",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon"
          },
          {
            "name": "Decapsulation",
            "value": 7378,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 558",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 30879,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 492",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 16433,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 444",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 15772,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 717",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon"
          },
          {
            "name": "Decapsulation",
            "value": 8767,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 468",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 517,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 242",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 392,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 73",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon"
          },
          {
            "name": "PK Validation",
            "value": 777,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 266",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 588,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 167",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon"
          },
          {
            "name": "PK Validation",
            "value": 1064,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 441",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 801,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 228",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon"
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
          "id": "6c39188104f5b15b05fd8fbe5cf204ef51019a05",
          "message": "Merge pull request #912 from cryspen/wysiwys/mlkem-benchmark-update\n\nUpdate ML-KEM benchmarking workflow to use new benchmarking actions",
          "timestamp": "2025-04-08T08:29:25Z",
          "url": "https://github.com/cryspen/libcrux/commit/6c39188104f5b15b05fd8fbe5cf204ef51019a05"
        },
        "date": 1744111469295,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 19359,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 145",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 19169,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 184",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 10731,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 112",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 10469,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 535",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 33250,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 717",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 32834,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 273",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 14989,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 195",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 14790,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 137",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 52861,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 502",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 52333,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 1339",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 20715,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 221",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 20447,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 236",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 23292,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 191",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 14799,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 68",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 11611,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 102",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5424,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 57",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 39008,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 587",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 21880,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 118",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 16407,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 239",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 6604,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 70",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 58773,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 612",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 31154,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 102",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 23305,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 210",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 9323,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 115",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 28711,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 221",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 22387,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 152",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 12707,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 147",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 9107,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 50",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 46593,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 575",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 31960,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 119",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 18045,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 145",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 12172,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 82",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 68846,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 575",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 44512,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 218",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 25512,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 165",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 16582,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 118",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 888,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 9",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 391,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 3",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1344,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 8",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 584,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 16",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1782,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 24",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 774,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 19",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
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
          "id": "6c39188104f5b15b05fd8fbe5cf204ef51019a05",
          "message": "Merge pull request #912 from cryspen/wysiwys/mlkem-benchmark-update\n\nUpdate ML-KEM benchmarking workflow to use new benchmarking actions",
          "timestamp": "2025-04-08T08:29:25Z",
          "url": "https://github.com/cryspen/libcrux/commit/6c39188104f5b15b05fd8fbe5cf204ef51019a05"
        },
        "date": 1744111525624,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 50556,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 486",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 50007,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 879",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 77388,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 946",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 77796,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 890",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 121165,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1506",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 121553,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1496",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 53802,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 540",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 26208,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 388",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 85942,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 829",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 31096,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 295",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 131345,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 2073",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 43423,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 209",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 60955,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 432",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 42557,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 178",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 93505,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1030",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 53729,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 822",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 141086,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1655",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 72683,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 581",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 1410,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 35",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 2038,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 46",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 2682,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 70",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
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
          "id": "6c39188104f5b15b05fd8fbe5cf204ef51019a05",
          "message": "Merge pull request #912 from cryspen/wysiwys/mlkem-benchmark-update\n\nUpdate ML-KEM benchmarking workflow to use new benchmarking actions",
          "timestamp": "2025-04-08T08:29:25Z",
          "url": "https://github.com/cryspen/libcrux/commit/6c39188104f5b15b05fd8fbe5cf204ef51019a05"
        },
        "date": 1744111566328,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 21295,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 439",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 20973,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 416",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 10427,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 220",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 10132,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 199",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 35206,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 979",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 34887,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 645",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 15094,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 634",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 14631,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 434",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 54246,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1080",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 54021,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1703",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 20967,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 581",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 21646,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2477",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 28782,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1407",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 14185,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 614",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 11430,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 368",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5526,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 335",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 47892,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2438",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 19590,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 935",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 16642,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1095",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 7230,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 523",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 70838,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2688",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 26840,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1182",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 23411,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1805",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 10235,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 931",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 37234,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1340",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 27545,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 888",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 13023,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 636",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 9602,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 524",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 58738,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1136",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 37755,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1390",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 18951,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 960",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 13303,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 6915",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 79375,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2401",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 51740,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 3169",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 26134,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1264",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 18405,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2436",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 1196,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 86",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 473,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 92",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1752,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 95",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 683,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 115",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 2345,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 130",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 904,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 141",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
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
          "id": "6c39188104f5b15b05fd8fbe5cf204ef51019a05",
          "message": "Merge pull request #912 from cryspen/wysiwys/mlkem-benchmark-update\n\nUpdate ML-KEM benchmarking workflow to use new benchmarking actions",
          "timestamp": "2025-04-08T08:29:25Z",
          "url": "https://github.com/cryspen/libcrux/commit/6c39188104f5b15b05fd8fbe5cf204ef51019a05"
        },
        "date": 1744111895492,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 19484,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 168",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 19026,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 254",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 10685,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 111",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 10360,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 96",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 33179,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 418",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 32452,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 342",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 15002,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 224",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 14688,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 247",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 51603,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 531",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 51450,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 691",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 20929,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 194",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 20410,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 201",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 23098,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 418",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 14648,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 160",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 12136,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 165",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5377,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 84",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 38349,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 370",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 21507,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 154",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 16292,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 118",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 6704,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 87",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 58749,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 1730",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 31271,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 259",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 22813,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 293",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 9266,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 120",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 28654,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 249",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 21884,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 402",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 12549,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 158",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 9154,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 76",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 46030,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 380",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 32006,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 526",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 17957,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 311",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 12381,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 229",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 68352,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 721",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 44492,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 481",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 25819,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 201",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 17049,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 169",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 964,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 49",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 486,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 41",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1394,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 87",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 697,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 57",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1782,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 108",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 929,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 77",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
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
          "id": "de487051d694b3fa2612f5a40d5ece8816157f13",
          "message": "Merge pull request #896 from cryspen/franziskus/xchacha\n\nchacha20poly1305: xchacha20 support",
          "timestamp": "2025-04-08T11:47:42Z",
          "url": "https://github.com/cryspen/libcrux/commit/de487051d694b3fa2612f5a40d5ece8816157f13"
        },
        "date": 1744113487211,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 49286,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1196",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 48769,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 610",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 76590,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 917",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 75758,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 822",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 119792,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1274",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 120102,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 2721",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 53151,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 579",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 26123,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 280",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 84672,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 988",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 30901,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 277",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 137197,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1616",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 43399,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 391",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 59170,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1233",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 41831,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 169",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 93068,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1034",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 52915,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 413",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 140499,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1601",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 71700,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 788",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 1061,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 56",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 1548,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 84",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 2063,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 16",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
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
          "id": "de487051d694b3fa2612f5a40d5ece8816157f13",
          "message": "Merge pull request #896 from cryspen/franziskus/xchacha\n\nchacha20poly1305: xchacha20 support",
          "timestamp": "2025-04-08T11:47:42Z",
          "url": "https://github.com/cryspen/libcrux/commit/de487051d694b3fa2612f5a40d5ece8816157f13"
        },
        "date": 1744113680541,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 9503,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 221",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 9265,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 88",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 5103,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 64",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 4946,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 45",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 15857,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 183",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 15591,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 480",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 9494,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 148",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 9779,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 204",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 24861,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 335",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 24753,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 424",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 14755,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 810",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 14860,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 798",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 10650,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 242",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5707,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 138",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 5628,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 215",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 2750,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 95",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 17987,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 321",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 8001,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 459",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 10355,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 170",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 3943,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 246",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 27570,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 675",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 11061,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 541",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 14446,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 619",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5048,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 141",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 12484,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 381",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 8660,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 397",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 6584,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 229",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon"
          },
          {
            "name": "Decapsulation",
            "value": 4781,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 204",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 20603,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 375",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 12133,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 705",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 11749,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 316",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon"
          },
          {
            "name": "Decapsulation",
            "value": 6889,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 293",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 30852,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 627",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 16519,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1077",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 15769,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 451",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon"
          },
          {
            "name": "Decapsulation",
            "value": 8772,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 444",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 520,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 148",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 389,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 80",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon"
          },
          {
            "name": "PK Validation",
            "value": 785,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 247",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 591,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 141",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon"
          },
          {
            "name": "PK Validation",
            "value": 1072,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 354",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 797,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 212",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon"
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
          "id": "de487051d694b3fa2612f5a40d5ece8816157f13",
          "message": "Merge pull request #896 from cryspen/franziskus/xchacha\n\nchacha20poly1305: xchacha20 support",
          "timestamp": "2025-04-08T11:47:42Z",
          "url": "https://github.com/cryspen/libcrux/commit/de487051d694b3fa2612f5a40d5ece8816157f13"
        },
        "date": 1744113723359,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 19503,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 313",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 19225,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 186",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 10793,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 121",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 10568,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 96",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 33546,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 370",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 32958,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 485",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 15004,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 217",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 14777,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 157",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 52045,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 551",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 51731,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 1248",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 20765,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 602",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 20403,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 178",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 23031,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 186",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 14861,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 54",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 11650,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 101",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5265,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 13",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 38525,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 394",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 21709,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 145",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 16286,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 132",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 6532,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 16",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 59333,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 766",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 31127,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 108",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 23379,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 235",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 9056,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 509",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 29054,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 767",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 21899,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 113",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 12628,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 32",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 9042,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 37",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 46275,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 656",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 32030,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 216",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 17951,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 145",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 12062,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 131",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 68502,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 673",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 44583,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 198",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 28114,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 210",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 16674,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 59",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 897,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 14",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 390,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 6",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1311,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 21",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 578,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 7",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1753,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 73",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 767,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 11",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
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
          "id": "de487051d694b3fa2612f5a40d5ece8816157f13",
          "message": "Merge pull request #896 from cryspen/franziskus/xchacha\n\nchacha20poly1305: xchacha20 support",
          "timestamp": "2025-04-08T11:47:42Z",
          "url": "https://github.com/cryspen/libcrux/commit/de487051d694b3fa2612f5a40d5ece8816157f13"
        },
        "date": 1744113809625,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 50314,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 275",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 50071,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 557",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 77966,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1026",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 77606,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 2110",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 122107,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1706",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 121800,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1727",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 53486,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 444",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 26561,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 224",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 86851,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 990",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 30827,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 238",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 132923,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1905",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 43137,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 393",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 61420,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 428",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 42304,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 264",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 94654,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 2385",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 54631,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 329",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 143259,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1669",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 73998,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 2683",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 1435,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 67",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 2053,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 106",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 2667,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 124",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
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
          "id": "de487051d694b3fa2612f5a40d5ece8816157f13",
          "message": "Merge pull request #896 from cryspen/franziskus/xchacha\n\nchacha20poly1305: xchacha20 support",
          "timestamp": "2025-04-08T11:47:42Z",
          "url": "https://github.com/cryspen/libcrux/commit/de487051d694b3fa2612f5a40d5ece8816157f13"
        },
        "date": 1744113842802,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 24320,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1107",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 22761,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2427",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 11341,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2879",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 11141,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 549",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 36873,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1857",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 37803,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2202",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 16013,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1204",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 15447,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 806",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 55009,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 13447",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 57478,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 4329",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 22500,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 798",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 24318,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 5746",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 31103,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1516",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 15581,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1586",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 12846,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 591",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5831,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 581",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 51057,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 17913",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 21983,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 928",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 18741,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 4550",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 8120,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1423",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 76535,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 4166",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 32137,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2067",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 26537,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 8164",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 10140,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 809",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 37913,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2530",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 27949,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1738",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 13240,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1112",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 9491,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 388",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 55143,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 3186",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 38396,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 5457",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 19196,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1699",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 13812,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 729",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 86287,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 5942",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 50390,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 4948",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 27342,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1079",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 20167,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1101",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 1208,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 74",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 457,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 56",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1718,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 114",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 667,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 91",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 2205,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 78",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 775,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 106",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
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
          "id": "de487051d694b3fa2612f5a40d5ece8816157f13",
          "message": "Merge pull request #896 from cryspen/franziskus/xchacha\n\nchacha20poly1305: xchacha20 support",
          "timestamp": "2025-04-08T11:47:42Z",
          "url": "https://github.com/cryspen/libcrux/commit/de487051d694b3fa2612f5a40d5ece8816157f13"
        },
        "date": 1744114123312,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 19352,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 187",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 19030,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 202",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 10617,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 84",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 10385,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 102",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 33255,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 341",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 32643,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 438",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 15026,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 181",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 14693,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 176",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 52148,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 632",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 51547,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 447",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 20890,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 175",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 20445,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 985",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 23121,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 215",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 14672,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 85",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 11717,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 120",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5332,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 85",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 38417,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 492",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 21594,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 143",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 16256,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 193",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 6623,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 104",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 58728,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 819",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 31112,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 285",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 22663,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 239",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 9165,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 95",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 28530,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 157",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 21811,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 179",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 12543,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 124",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 9075,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 80",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 46044,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 393",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 31944,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 235",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 17852,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 145",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 12334,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 213",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 68323,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 848",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 44308,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 333",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 25167,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 307",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 16982,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 160",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 911,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 33",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 446,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 88",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1400,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 60",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 680,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 50",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1770,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 93",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 909,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 75",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Jonas Schneider-Bensch",
            "username": "jschneider-bensch",
            "email": "124457079+jschneider-bensch@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "879bab2ebc3df985dae0c9db119c033f38c516dd",
          "message": "Merge pull request #913 from cryspen/jonas/xchacha-wycheproof\n\nWycherproof test for XChacha20Poly1305",
          "timestamp": "2025-04-08T16:13:03Z",
          "url": "https://github.com/cryspen/libcrux/commit/879bab2ebc3df985dae0c9db119c033f38c516dd"
        },
        "date": 1744129394607,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 49326,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1663",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 48865,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 7110",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 76562,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 878",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 75966,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1184",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 119530,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1318",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 120382,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1234",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 53027,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 456",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 26193,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 170",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 84875,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1341",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 30842,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 304",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 130680,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1089",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 43426,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 479",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 59201,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 593",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 42123,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 632",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 92784,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 933",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 52789,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 687",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 140323,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 5011",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 72337,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 787",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 1053,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 76",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 1540,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 109",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 2071,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 140",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Jonas Schneider-Bensch",
            "username": "jschneider-bensch",
            "email": "124457079+jschneider-bensch@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "879bab2ebc3df985dae0c9db119c033f38c516dd",
          "message": "Merge pull request #913 from cryspen/jonas/xchacha-wycheproof\n\nWycherproof test for XChacha20Poly1305",
          "timestamp": "2025-04-08T16:13:03Z",
          "url": "https://github.com/cryspen/libcrux/commit/879bab2ebc3df985dae0c9db119c033f38c516dd"
        },
        "date": 1744129583364,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 50472,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 858",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 50201,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 709",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 77389,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 904",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 77829,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 815",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 121144,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1514",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 121905,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1648",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 53983,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 591",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 26552,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 251",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 86155,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 925",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 31535,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 503",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 131300,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 2092",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 43840,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 678",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 61264,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 535",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 42757,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 269",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 93450,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1232",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 53887,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 397",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 141084,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 4154",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 73330,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 628",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 1439,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 80",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 2057,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 107",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 2671,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 150",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Jonas Schneider-Bensch",
            "username": "jschneider-bensch",
            "email": "124457079+jschneider-bensch@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "879bab2ebc3df985dae0c9db119c033f38c516dd",
          "message": "Merge pull request #913 from cryspen/jonas/xchacha-wycheproof\n\nWycherproof test for XChacha20Poly1305",
          "timestamp": "2025-04-08T16:13:03Z",
          "url": "https://github.com/cryspen/libcrux/commit/879bab2ebc3df985dae0c9db119c033f38c516dd"
        },
        "date": 1744129612035,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 10222,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 424",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 9903,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 235",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 5301,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 135",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 5364,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 614",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 16673,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1023",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 16541,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 2600",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 9640,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 268",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 10143,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 285",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 25012,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 638",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 24842,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 658",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 13560,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 749",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 13809,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 292",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 11483,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 268",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 6234,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 460",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 6634,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 947",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 3382,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 676",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 19935,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 3338",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 8079,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 291",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 11158,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 488",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 3977,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 274",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 29754,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1761",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 12003,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 910",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 15631,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 835",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5439,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 451",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 13495,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 719",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 9038,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 394",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 7203,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 653",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon"
          },
          {
            "name": "Decapsulation",
            "value": 5206,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 253",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 22182,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1160",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 13160,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 595",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 12645,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 407",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon"
          },
          {
            "name": "Decapsulation",
            "value": 7512,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 361",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 33169,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1478",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 17717,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1016",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 17024,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 724",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon"
          },
          {
            "name": "Decapsulation",
            "value": 9545,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 337",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 539,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 179",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 485,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 119",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon"
          },
          {
            "name": "PK Validation",
            "value": 845,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 301",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 588,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 170",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon"
          },
          {
            "name": "PK Validation",
            "value": 1053,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 398",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 813,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 229",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Jonas Schneider-Bensch",
            "username": "jschneider-bensch",
            "email": "124457079+jschneider-bensch@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "879bab2ebc3df985dae0c9db119c033f38c516dd",
          "message": "Merge pull request #913 from cryspen/jonas/xchacha-wycheproof\n\nWycherproof test for XChacha20Poly1305",
          "timestamp": "2025-04-08T16:13:03Z",
          "url": "https://github.com/cryspen/libcrux/commit/879bab2ebc3df985dae0c9db119c033f38c516dd"
        },
        "date": 1744129636184,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 19385,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 576",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 19282,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 232",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 10726,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 217",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 10378,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 107",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 33316,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 277",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 32906,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 479",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 14994,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 228",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 14813,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 262",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 52982,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 721",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 52194,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 755",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 20765,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 212",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 20617,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 262",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 23144,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 321",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 14697,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 228",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 11598,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 187",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5277,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 21",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 38898,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 743",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 21676,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 148",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 16294,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 742",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 6590,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 28",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 58620,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 742",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 31034,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 284",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 23267,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 240",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 9261,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 120",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 28568,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 249",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 21880,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 334",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 12621,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 90",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 9027,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 275",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 46468,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 358",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 31927,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 233",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 17946,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 227",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 12162,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 76",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 68895,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 558",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 44334,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 222",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 25479,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 200",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 16686,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 78",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 895,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 23",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 391,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 4",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1352,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 14",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 585,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 13",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1782,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 25",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 776,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 11",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Jonas Schneider-Bensch",
            "username": "jschneider-bensch",
            "email": "124457079+jschneider-bensch@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "879bab2ebc3df985dae0c9db119c033f38c516dd",
          "message": "Merge pull request #913 from cryspen/jonas/xchacha-wycheproof\n\nWycherproof test for XChacha20Poly1305",
          "timestamp": "2025-04-08T16:13:03Z",
          "url": "https://github.com/cryspen/libcrux/commit/879bab2ebc3df985dae0c9db119c033f38c516dd"
        },
        "date": 1744129962741,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 35366,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 3478",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 34414,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 8101",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 18261,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2446",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 17589,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 3715",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 57474,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 6005",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 54359,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 9462",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 25776,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 8568",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 24826,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 8929",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 90855,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 16323",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 91287,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 15176",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 36043,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 6834",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 34905,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 6954",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 38320,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 7188",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 22496,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 5725",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 17331,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2946",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 7005,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 3189",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 66834,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 39088",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 27138,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 4432",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 22990,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 5288",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 10693,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1743",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 99375,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 19172",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 39876,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 5201",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 37569,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 53858",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 13160,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1886",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 44031,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 5885",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 31950,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1738",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 14930,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1667",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 10434,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1215",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 63555,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 4087",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 43515,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2127",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 21153,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1140",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 14368,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1457",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 84570,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 6008",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 60931,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2187",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 29924,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2130",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 19061,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1081",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 1160,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 82",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 406,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 50",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1666,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 81",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 633,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 111",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 2239,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 84",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 812,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 86",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
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
          "id": "1aa8c5c0a1867566b07816d34bd1c924de804b82",
          "message": "Merge pull request #880 from cryspen/keks/bench-trace-macro\n\nAdd tracing types and a proc macro for using it to measure functions",
          "timestamp": "2025-04-10T07:20:58Z",
          "url": "https://github.com/cryspen/libcrux/commit/1aa8c5c0a1867566b07816d34bd1c924de804b82"
        },
        "date": 1744270267694,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 49270,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 907",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 48874,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 619",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 76898,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 917",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 75829,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1061",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 119533,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1431",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 120493,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1773",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 53240,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 601",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 26209,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 154",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 84729,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1120",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 30821,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 277",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 130075,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1780",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 42660,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 3468",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 57707,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1573",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 41922,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1082",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 90876,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 6148",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 51404,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1544",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 140885,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 2364",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 71493,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1664",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 1058,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 110",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 1536,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 117",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 2065,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 146",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
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
          "id": "1aa8c5c0a1867566b07816d34bd1c924de804b82",
          "message": "Merge pull request #880 from cryspen/keks/bench-trace-macro\n\nAdd tracing types and a proc macro for using it to measure functions",
          "timestamp": "2025-04-10T07:20:58Z",
          "url": "https://github.com/cryspen/libcrux/commit/1aa8c5c0a1867566b07816d34bd1c924de804b82"
        },
        "date": 1744270510789,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 19515,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 493",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 19235,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 149",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 10696,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 331",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 10457,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 70",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 33571,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 457",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 32918,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 425",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 15246,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 193",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 14943,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 147",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 51781,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 588",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 51935,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 521",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 20810,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 201",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 20526,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 944",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 23069,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 208",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 14722,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 57",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 11806,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 92",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5321,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 24",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 38737,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 291",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 21742,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 83",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 16302,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 159",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 6535,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 29",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 59297,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 631",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 31176,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 154",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 23005,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 461",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 8982,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 50",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 28995,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 193",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 21993,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 59",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 12643,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 207",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 8985,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 39",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 46314,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 1155",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 32055,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 177",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 18086,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 187",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 12143,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 56",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 68523,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 635",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 44466,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 213",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 25523,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 254",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 16515,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 118",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 886,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 10",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 390,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 8",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1360,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 27",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 579,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 10",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1784,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 21",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 767,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 12",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
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
          "id": "1aa8c5c0a1867566b07816d34bd1c924de804b82",
          "message": "Merge pull request #880 from cryspen/keks/bench-trace-macro\n\nAdd tracing types and a proc macro for using it to measure functions",
          "timestamp": "2025-04-10T07:20:58Z",
          "url": "https://github.com/cryspen/libcrux/commit/1aa8c5c0a1867566b07816d34bd1c924de804b82"
        },
        "date": 1744270511296,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 9559,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 320",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 10735,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 877",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 5405,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 296",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 4969,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 384",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 15886,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 210",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 15614,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 303",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 9483,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 139",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 9480,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 271",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 24896,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 300",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 24836,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 516",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 13288,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 208",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 13221,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 164",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 10661,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 392",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5729,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 146",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 5630,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 97",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 2777,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 106",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 18104,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 501",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 8018,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 435",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 10371,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 455",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 3927,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 77",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 27520,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 674",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 11024,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 571",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 14573,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 764",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5053,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 437",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 12500,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 325",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 8697,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 9840",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 6601,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 368",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon"
          },
          {
            "name": "Decapsulation",
            "value": 4774,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 224",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 20504,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1039",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 12162,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 812",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 11669,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 657",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon"
          },
          {
            "name": "Decapsulation",
            "value": 6890,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 213",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 30883,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 652",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 16436,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 958",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 15871,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 554",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon"
          },
          {
            "name": "Decapsulation",
            "value": 8781,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 327",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 511,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 152",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 390,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 79",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon"
          },
          {
            "name": "PK Validation",
            "value": 767,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 66",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 588,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 169",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon"
          },
          {
            "name": "PK Validation",
            "value": 1087,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 449",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 796,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 219",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon"
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
          "id": "1aa8c5c0a1867566b07816d34bd1c924de804b82",
          "message": "Merge pull request #880 from cryspen/keks/bench-trace-macro\n\nAdd tracing types and a proc macro for using it to measure functions",
          "timestamp": "2025-04-10T07:20:58Z",
          "url": "https://github.com/cryspen/libcrux/commit/1aa8c5c0a1867566b07816d34bd1c924de804b82"
        },
        "date": 1744270565083,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 50547,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 602",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 49937,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1391",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 78036,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 749",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 77501,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1056",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 122154,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1608",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 121635,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1469",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 53820,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 495",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 26269,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 391",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 85974,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1031",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 31069,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 148",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 131066,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1600",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 43551,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 289",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 61266,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1351",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 42611,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 806",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 93446,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1292",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 53744,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 602",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 141368,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1595",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 72965,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 734",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 1451,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 53",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 2036,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 77",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 2662,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 94",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
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
          "id": "1aa8c5c0a1867566b07816d34bd1c924de804b82",
          "message": "Merge pull request #880 from cryspen/keks/bench-trace-macro\n\nAdd tracing types and a proc macro for using it to measure functions",
          "timestamp": "2025-04-10T07:20:58Z",
          "url": "https://github.com/cryspen/libcrux/commit/1aa8c5c0a1867566b07816d34bd1c924de804b82"
        },
        "date": 1744270789628,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 22241,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 5801",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 22527,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 3071",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 11456,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 5226",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 10508,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2123",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 36588,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 5074",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 37955,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1222",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 15540,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 707",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 15604,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1356",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 62935,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 16787",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 63293,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 18961",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 22882,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 6724",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 21815,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 3083",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 33667,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 10836",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 15314,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 5649",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 12234,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1567",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 6342,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 854",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 62182,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 6858",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 27550,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2974",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 19003,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2209",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 7562,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 744",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 67179,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 6705",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 26361,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 4246",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 22743,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 360",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 9304,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 426",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 34768,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 531",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 27226,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 987",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 12569,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 365",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 9006,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 232",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 53515,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1117",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 37344,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 705",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 18022,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 289",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 12040,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 364",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 76624,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1278",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 49641,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 875",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 25695,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 845",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 17170,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 540",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 1174,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 82",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 439,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 40",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1685,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 158",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 683,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 147",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 2276,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 94",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 822,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 119",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
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
          "id": "1aa8c5c0a1867566b07816d34bd1c924de804b82",
          "message": "Merge pull request #880 from cryspen/keks/bench-trace-macro\n\nAdd tracing types and a proc macro for using it to measure functions",
          "timestamp": "2025-04-10T07:20:58Z",
          "url": "https://github.com/cryspen/libcrux/commit/1aa8c5c0a1867566b07816d34bd1c924de804b82"
        },
        "date": 1744270826549,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 19358,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 180",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 18976,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 178",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 10636,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 67",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 10368,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 182",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 33237,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 574",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 32426,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 688",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 15104,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 134",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 14676,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 526",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 51871,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 717",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 51392,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 621",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 20807,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 220",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 20545,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 267",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 23058,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 198",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 14703,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 136",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 11671,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 101",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5326,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 53",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 38536,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 290",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 21518,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 197",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 16234,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 357",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 6608,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 63",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 58699,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 755",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 31079,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 353",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 22765,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 634",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 9166,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 116",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 28651,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 192",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 21795,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 109",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 12545,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 124",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 9070,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 123",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 45868,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 703",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 31831,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 232",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 17797,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 196",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 12240,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 134",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 68092,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 774",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 44183,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 397",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 25217,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 375",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 16977,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 165",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 899,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 53",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 439,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 25",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1379,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 54",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 648,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 32",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1729,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 64",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 857,
            "unit": "ns/iter",
            "os": "windows-latest_64",
            "range": "± 43",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Lucas Franceschino",
            "username": "W95Psp",
            "email": "lucas@franceschino.fr"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "16b7a478960c7ff53889aba7dda0f8c29f5fd4ab",
          "message": "Merge pull request #916 from cryspen/lf-fix-instance-ids-hax-1391\n\nfix(F*): rename instance ids, following cryspen/hax#1391",
          "timestamp": "2025-04-10T11:28:53Z",
          "url": "https://github.com/cryspen/libcrux/commit/16b7a478960c7ff53889aba7dda0f8c29f5fd4ab"
        },
        "date": 1744285150885,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 49450,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 800",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 48750,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1166",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 76863,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1054",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 75769,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 930",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 119659,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1596",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 120156,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1876",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 53130,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 4604",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 26332,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 895",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 85112,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1242",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 30925,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 493",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 130311,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1566",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 43322,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 435",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 59243,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 535",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 42194,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 292",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 92691,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1014",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 52925,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 321",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 140409,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1573",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 73139,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 744",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 1066,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 81",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 1551,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 113",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 2072,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 126",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Lucas Franceschino",
            "username": "W95Psp",
            "email": "lucas@franceschino.fr"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "16b7a478960c7ff53889aba7dda0f8c29f5fd4ab",
          "message": "Merge pull request #916 from cryspen/lf-fix-instance-ids-hax-1391\n\nfix(F*): rename instance ids, following cryspen/hax#1391",
          "timestamp": "2025-04-10T11:28:53Z",
          "url": "https://github.com/cryspen/libcrux/commit/16b7a478960c7ff53889aba7dda0f8c29f5fd4ab"
        },
        "date": 1744285345151,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 9523,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 255",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 9254,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 159",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 5106,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 79",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 4948,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 43",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 15924,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 333",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 15948,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 732",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 9480,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 112",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 9472,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 301",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 24906,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 461",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 24776,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 443",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 13278,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 205",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 13233,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 378",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 10662,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 304",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5729,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 158",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 5638,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 127",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 2745,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 76",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 17986,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 375",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 8084,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 455",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 10382,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 380",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 3921,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 235",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 27559,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 767",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 11021,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 720",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 14441,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 478",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5105,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 391",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 12484,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 317",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 8989,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 533",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 6604,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 189",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon"
          },
          {
            "name": "Decapsulation",
            "value": 4773,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 206",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 23300,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1489",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 13605,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1120",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 11674,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 537",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon"
          },
          {
            "name": "Decapsulation",
            "value": 6898,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 382",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 30912,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 999",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 16446,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 803",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 15756,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 449",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon"
          },
          {
            "name": "Decapsulation",
            "value": 8771,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 415",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 515,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 136",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 391,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 106",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon"
          },
          {
            "name": "PK Validation",
            "value": 776,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 83",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 587,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 135",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon"
          },
          {
            "name": "PK Validation",
            "value": 1088,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 422",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 796,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 262",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Lucas Franceschino",
            "username": "W95Psp",
            "email": "lucas@franceschino.fr"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "16b7a478960c7ff53889aba7dda0f8c29f5fd4ab",
          "message": "Merge pull request #916 from cryspen/lf-fix-instance-ids-hax-1391\n\nfix(F*): rename instance ids, following cryspen/hax#1391",
          "timestamp": "2025-04-10T11:28:53Z",
          "url": "https://github.com/cryspen/libcrux/commit/16b7a478960c7ff53889aba7dda0f8c29f5fd4ab"
        },
        "date": 1744285383131,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 19483,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 216",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 19161,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 171",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 10813,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 119",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 10522,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 449",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 33442,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 617",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 33142,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 315",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 15022,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 134",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 14840,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 647",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 51694,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 630",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 51955,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 666",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 20820,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 181",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 20447,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 467",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 23184,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 268",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 14717,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 140",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 11653,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 185",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5292,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 32",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 38537,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 363",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 21703,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 111",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 16274,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 606",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 6538,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 122",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 59214,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 862",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 31138,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 154",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 22955,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 212",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 9038,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 462",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 29237,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 180",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 21958,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 67",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 12647,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 78",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 9108,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 583",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 46324,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 754",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 32067,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 543",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 17936,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 149",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 12126,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 60",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 68509,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 693",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 44423,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 420",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 25906,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 273",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 16654,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 153",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 915,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 8",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 391,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 7",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1305,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 14",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 578,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 13",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1739,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 23",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 771,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 19",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Lucas Franceschino",
            "username": "W95Psp",
            "email": "lucas@franceschino.fr"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "16b7a478960c7ff53889aba7dda0f8c29f5fd4ab",
          "message": "Merge pull request #916 from cryspen/lf-fix-instance-ids-hax-1391\n\nfix(F*): rename instance ids, following cryspen/hax#1391",
          "timestamp": "2025-04-10T11:28:53Z",
          "url": "https://github.com/cryspen/libcrux/commit/16b7a478960c7ff53889aba7dda0f8c29f5fd4ab"
        },
        "date": 1744285408120,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 50333,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 771",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 50044,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 518",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 78045,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1435",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 77495,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1213",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 122149,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1610",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 121534,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1367",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 53597,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 598",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 26465,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 356",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 86934,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1200",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 30844,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 282",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 132274,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1760",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 43231,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 388",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 61535,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 620",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 42321,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 249",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 94640,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 940",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 54552,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 404",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 142757,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 2890",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 74141,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 906",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 1437,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 48",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 2083,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 69",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 2708,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 88",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Lucas Franceschino",
            "username": "W95Psp",
            "email": "lucas@franceschino.fr"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "16b7a478960c7ff53889aba7dda0f8c29f5fd4ab",
          "message": "Merge pull request #916 from cryspen/lf-fix-instance-ids-hax-1391\n\nfix(F*): rename instance ids, following cryspen/hax#1391",
          "timestamp": "2025-04-10T11:28:53Z",
          "url": "https://github.com/cryspen/libcrux/commit/16b7a478960c7ff53889aba7dda0f8c29f5fd4ab"
        },
        "date": 1744285562492,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 22408,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 3192",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 22878,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 936",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 11779,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1715",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 12726,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 655",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 42039,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 3527",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 45020,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2049",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 18505,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 880",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 18116,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 835",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 64958,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 4649",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 67229,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 5981",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 26793,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1255",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 26640,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2045",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 36066,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2716",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 17253,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1349",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 13343,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 846",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 6985,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1550",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 56288,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 3683",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 22828,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 3268",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 19334,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 13848",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 7703,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 598",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 71277,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 8946",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 28811,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2859",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 27970,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 4156",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 10683,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 655",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 40927,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 5894",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 27650,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1114",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 12968,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 763",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 9391,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1246",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 65854,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2688",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 46155,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 7335",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 20035,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1183",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 14649,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 5118",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 93522,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 9552",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 51070,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2873",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 27185,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2200",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 21294,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 7212",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 1582,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 311",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 550,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 343",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1996,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 574",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 949,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 168",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 3030,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 433",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 1077,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 125",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Jonathan Protzenko",
            "username": "protz",
            "email": "jonathan.protzenko+github@gmail.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "9f6c2dedb8b130f22caa532d60f3c59c2b7de09e",
          "message": "Merge pull request #917 from msprotz/patch-3\n\nUpdate eurydice_glue.h",
          "timestamp": "2025-04-10T19:45:35Z",
          "url": "https://github.com/cryspen/libcrux/commit/9f6c2dedb8b130f22caa532d60f3c59c2b7de09e"
        },
        "date": 1744314949626,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 49340,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 627",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 48807,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1340",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 76638,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 970",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 75681,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1475",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 119571,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1787",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 120256,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1933",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 53242,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 619",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 26244,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 182",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 84768,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 673",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 30828,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 381",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 130266,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1960",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 43363,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 572",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 59157,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 572",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 42250,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 210",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 93071,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1351",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 53015,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 572",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 140486,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1708",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 72807,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 939",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 1079,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 87",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 1562,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 133",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 2072,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 109",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Jonathan Protzenko",
            "username": "protz",
            "email": "jonathan.protzenko+github@gmail.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "9f6c2dedb8b130f22caa532d60f3c59c2b7de09e",
          "message": "Merge pull request #917 from msprotz/patch-3\n\nUpdate eurydice_glue.h",
          "timestamp": "2025-04-10T19:45:35Z",
          "url": "https://github.com/cryspen/libcrux/commit/9f6c2dedb8b130f22caa532d60f3c59c2b7de09e"
        },
        "date": 1744315154224,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 10100,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 583",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 9444,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 285",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 5121,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 143",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 4969,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 135",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 16191,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 473",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 15858,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 397",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 9503,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 210",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 9513,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 237",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 25406,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 694",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 24825,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 704",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 13278,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 186",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 13207,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 137",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 10633,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 125",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5722,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 95",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 6702,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 718",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 3056,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 259",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 18840,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 780",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 8355,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 423",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 10851,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 577",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 4162,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 521",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 27689,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 568",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 11054,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 718",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 14446,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 576",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5064,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 315",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 12528,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 341",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 8691,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 493",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 6597,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 264",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon"
          },
          {
            "name": "Decapsulation",
            "value": 4778,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 196",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 20901,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 690",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 12230,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 573",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 11660,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 284",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon"
          },
          {
            "name": "Decapsulation",
            "value": 6887,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 363",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 30868,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 595",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 16573,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1163",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 15764,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 402",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon"
          },
          {
            "name": "Decapsulation",
            "value": 8796,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 996",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 516,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 163",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 392,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 83",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon"
          },
          {
            "name": "PK Validation",
            "value": 774,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 129",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 593,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 78",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon"
          },
          {
            "name": "PK Validation",
            "value": 1078,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 410",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 795,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 211",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Jonathan Protzenko",
            "username": "protz",
            "email": "jonathan.protzenko+github@gmail.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "9f6c2dedb8b130f22caa532d60f3c59c2b7de09e",
          "message": "Merge pull request #917 from msprotz/patch-3\n\nUpdate eurydice_glue.h",
          "timestamp": "2025-04-10T19:45:35Z",
          "url": "https://github.com/cryspen/libcrux/commit/9f6c2dedb8b130f22caa532d60f3c59c2b7de09e"
        },
        "date": 1744315182973,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 19531,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 262",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 19086,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 153",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 10761,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 94",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 10469,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 88",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 33574,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 341",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 32851,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 345",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 14994,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 264",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 14833,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 178",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 51636,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 769",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 52000,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 667",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 20753,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 194",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 20352,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 492",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 23105,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 243",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 14740,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 62",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 11737,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 109",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5291,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 15",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 38879,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 330",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 21734,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 92",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 16306,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 148",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 6576,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 20",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 59282,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 471",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 31218,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 304",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 23250,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 171",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 9014,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 36",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 29410,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 187",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 21951,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 51",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 12656,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 103",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 9013,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 80",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 46233,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 633",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 32106,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 79",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 17949,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 138",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 12096,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 61",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 68538,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 666",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 44320,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 244",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 25747,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 247",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 16551,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 135",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 884,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 9",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 390,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 7",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1302,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 8",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 578,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 6",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1813,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 10",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 765,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 10",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Jonathan Protzenko",
            "username": "protz",
            "email": "jonathan.protzenko+github@gmail.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "9f6c2dedb8b130f22caa532d60f3c59c2b7de09e",
          "message": "Merge pull request #917 from msprotz/patch-3\n\nUpdate eurydice_glue.h",
          "timestamp": "2025-04-10T19:45:35Z",
          "url": "https://github.com/cryspen/libcrux/commit/9f6c2dedb8b130f22caa532d60f3c59c2b7de09e"
        },
        "date": 1744315239713,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 50533,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1472",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 49966,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1100",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 78021,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 879",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 77768,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 697",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 121314,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1225",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 121887,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1829",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 53964,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 641",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 26452,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 290",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 86166,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 826",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 31242,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 432",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 131457,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1775",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 43789,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 395",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 61203,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1885",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 42780,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 526",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 93717,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1027",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 53928,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 531",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 141226,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1999",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 73012,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 682",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 1430,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 55",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 2097,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 106",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 2754,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 120",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Jonathan Protzenko",
            "username": "protz",
            "email": "jonathan.protzenko+github@gmail.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "9f6c2dedb8b130f22caa532d60f3c59c2b7de09e",
          "message": "Merge pull request #917 from msprotz/patch-3\n\nUpdate eurydice_glue.h",
          "timestamp": "2025-04-10T19:45:35Z",
          "url": "https://github.com/cryspen/libcrux/commit/9f6c2dedb8b130f22caa532d60f3c59c2b7de09e"
        },
        "date": 1744315388927,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 30253,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 4045",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 28656,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 9607",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 13577,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2636",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 15910,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 8611",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 54819,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 41777",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 50662,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 9699",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 22260,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 6022",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 19769,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 18885",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 69663,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 9542",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 71059,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 15315",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 28769,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 3933",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 28402,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 5883",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 30926,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2132",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 15288,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2047",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 12443,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 735",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5869,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 641",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 51864,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 14330",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 20617,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 4245",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 19545,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 9786",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 7929,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 513",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 74864,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 3715",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 30456,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1046",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 24141,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1266",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 10176,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 927",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 39469,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1206",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 31128,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1533",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 13135,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 599",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 9146,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 438",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 53654,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 961",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 37459,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 738",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 18268,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 582",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 12241,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 419",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 78037,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 5439",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 50119,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 729",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 25758,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 520",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 17325,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 521",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 1125,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 37",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 397,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 36",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1649,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 89",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 619,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 121",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 2195,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 108",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 844,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 86",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Jonas Schneider-Bensch",
            "username": "jschneider-bensch",
            "email": "124457079+jschneider-bensch@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "28b557014a479a290f1be65972459f10ea9ad4f3",
          "message": "Merge pull request #920 from cryspen/keks/kem-derand\n\nadd xwing-06 support",
          "timestamp": "2025-04-16T10:01:49Z",
          "url": "https://github.com/cryspen/libcrux/commit/28b557014a479a290f1be65972459f10ea9ad4f3"
        },
        "date": 1744798354257,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 49336,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1681",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 48718,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 459",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 76656,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1084",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 75829,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 818",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 119397,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1417",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 120224,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1411",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 52973,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 645",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 26138,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 229",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 84915,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 819",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 30927,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 264",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 130845,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 3426",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 43388,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 524",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 59379,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 669",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 41805,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 300",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 92856,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1042",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 52597,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 597",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 140357,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1310",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 72394,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 608",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 1078,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 115",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 1569,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 118",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 2066,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 60",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Jonas Schneider-Bensch",
            "username": "jschneider-bensch",
            "email": "124457079+jschneider-bensch@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "28b557014a479a290f1be65972459f10ea9ad4f3",
          "message": "Merge pull request #920 from cryspen/keks/kem-derand\n\nadd xwing-06 support",
          "timestamp": "2025-04-16T10:01:49Z",
          "url": "https://github.com/cryspen/libcrux/commit/28b557014a479a290f1be65972459f10ea9ad4f3"
        },
        "date": 1744798554284,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 10276,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 305",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 9957,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 651",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 5571,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 105",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 5442,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 415",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 17465,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 494",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 17262,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 904",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 10437,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 244",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 10393,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 324",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 27341,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 805",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 26964,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 562",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 14576,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1128",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 14464,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 412",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 11759,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 679",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 6312,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 510",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 6147,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 133",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 3041,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 212",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 19676,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 3952",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 8799,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 435",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 11343,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 316",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 4191,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 368",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 27639,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 563",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 11049,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 536",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 14424,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 264",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5047,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 297",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 12534,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 475",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 8735,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 379",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 6874,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 18599",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon"
          },
          {
            "name": "Decapsulation",
            "value": 5024,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 241",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 21588,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 939",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 12144,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 418",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 11689,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 197",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon"
          },
          {
            "name": "Decapsulation",
            "value": 6882,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 308",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 30948,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 747",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 16496,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1042",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 15743,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 417",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon"
          },
          {
            "name": "Decapsulation",
            "value": 8795,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 485",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 518,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 193",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 435,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 77",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon"
          },
          {
            "name": "PK Validation",
            "value": 878,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 203",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 660,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 149",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon"
          },
          {
            "name": "PK Validation",
            "value": 1162,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 467",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 890,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 287",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Jonas Schneider-Bensch",
            "username": "jschneider-bensch",
            "email": "124457079+jschneider-bensch@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "28b557014a479a290f1be65972459f10ea9ad4f3",
          "message": "Merge pull request #920 from cryspen/keks/kem-derand\n\nadd xwing-06 support",
          "timestamp": "2025-04-16T10:01:49Z",
          "url": "https://github.com/cryspen/libcrux/commit/28b557014a479a290f1be65972459f10ea9ad4f3"
        },
        "date": 1744798561922,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 19369,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 385",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 19151,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 131",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 10731,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 71",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 10481,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 110",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 33358,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 270",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 33261,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 406",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 15023,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 131",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 14882,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 189",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 52733,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 541",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 52470,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 558",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 20818,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 190",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 20491,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 175",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 23149,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 93",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 14718,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 176",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 11678,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 87",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5282,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 38",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 38968,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 392",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 21570,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 62",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 16241,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 150",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 6548,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 38",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 58776,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 1644",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 31215,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 391",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 23035,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 143",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 9006,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 104",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 28779,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 210",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 21997,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 176",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 12621,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 146",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 8903,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 84",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 46144,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 403",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 31983,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 103",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 17849,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 151",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 12120,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 39",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 68915,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 760",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 44429,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 253",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 25718,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 273",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 16458,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 328",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 897,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 11",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 391,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 10",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1350,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 22",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 587,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 11",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1787,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 25",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 776,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 13",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Jonas Schneider-Bensch",
            "username": "jschneider-bensch",
            "email": "124457079+jschneider-bensch@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "28b557014a479a290f1be65972459f10ea9ad4f3",
          "message": "Merge pull request #920 from cryspen/keks/kem-derand\n\nadd xwing-06 support",
          "timestamp": "2025-04-16T10:01:49Z",
          "url": "https://github.com/cryspen/libcrux/commit/28b557014a479a290f1be65972459f10ea9ad4f3"
        },
        "date": 1744798579059,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 50616,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1521",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 49960,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 416",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 77486,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 769",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 77696,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 982",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 121292,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 2129",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 122079,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1556",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 53661,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 396",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 26254,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 281",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 86551,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 793",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 31108,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 182",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 131186,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1424",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 43579,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 302",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 61042,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1795",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 42671,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 408",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 93494,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1147",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 53711,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 281",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 141652,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1974",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 72559,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 831",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 1413,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 49",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 2060,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 60",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 2686,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 80",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Jonas Schneider-Bensch",
            "username": "jschneider-bensch",
            "email": "124457079+jschneider-bensch@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "28b557014a479a290f1be65972459f10ea9ad4f3",
          "message": "Merge pull request #920 from cryspen/keks/kem-derand\n\nadd xwing-06 support",
          "timestamp": "2025-04-16T10:01:49Z",
          "url": "https://github.com/cryspen/libcrux/commit/28b557014a479a290f1be65972459f10ea9ad4f3"
        },
        "date": 1744798725218,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 23741,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2418",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 25345,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1011",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 11553,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 986",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 12444,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 461",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 41471,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 3915",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 42199,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 8182",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 18261,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 835",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 17648,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2230",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 64127,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 18441",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 65408,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 16441",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 25481,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2677",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 25573,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 8686",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 32916,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 6540",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 16970,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 4748",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 13736,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2836",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 6259,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 275",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 53658,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 26181",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 23112,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 5320",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 19342,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 613",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 8305,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 512",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 78540,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2269",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 32574,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 3536",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 27717,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2338",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 11533,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 4320",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 42657,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 5861",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 32593,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2225",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 15437,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 697",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 10997,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 719",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 64681,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2188",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 44805,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1667",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 22070,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 812",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 14754,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 975",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 93203,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 5820",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 60774,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1908",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 31390,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2711",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 21470,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1333",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 1423,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 58",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 544,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 60",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 2072,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 72",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 910,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 282",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 2774,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 369",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 1065,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 59",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
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
          "id": "0cc077121ef292dbc42308388552d6468b3567ce",
          "message": "Merge pull request #922 from cryspen/wysiwys/kem-derand\n\nAdd `no_std` support to additional libcrux crates",
          "timestamp": "2025-04-16T12:19:24Z",
          "url": "https://github.com/cryspen/libcrux/commit/0cc077121ef292dbc42308388552d6468b3567ce"
        },
        "date": 1744806657969,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 49224,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 2208",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 48766,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 535",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 76384,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1812",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 75861,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 935",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 119738,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1502",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 119756,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1564",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 53165,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 370",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 26770,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 207",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 84751,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 926",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 30950,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 287",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 130576,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1684",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 43339,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 438",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 59569,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 404",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 41950,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 270",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 92898,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 876",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 53033,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 536",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 140394,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 2200",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 73137,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 803",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 1053,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 78",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 1597,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 119",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 2082,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 148",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
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
          "id": "0cc077121ef292dbc42308388552d6468b3567ce",
          "message": "Merge pull request #922 from cryspen/wysiwys/kem-derand\n\nAdd `no_std` support to additional libcrux crates",
          "timestamp": "2025-04-16T12:19:24Z",
          "url": "https://github.com/cryspen/libcrux/commit/0cc077121ef292dbc42308388552d6468b3567ce"
        },
        "date": 1744806783557,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 9500,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 246",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 9264,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 102",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 5108,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 109",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 4948,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 51",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 15844,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 250",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 15575,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 209",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 9537,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 369",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 9472,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 202",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 24871,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 389",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 24761,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 638",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 13258,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 308",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 13225,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 327",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 10665,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 173",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5701,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 142",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 5635,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 182",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 2749,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 86",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 18012,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 561",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 8025,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 369",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 10790,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 579",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 3996,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 315",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 29536,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 4058",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 11979,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1860",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 14967,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 949",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5207,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 418",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 12474,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 171",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 8657,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 230",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 6588,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 364",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon"
          },
          {
            "name": "Decapsulation",
            "value": 4770,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 193",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 22833,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1240",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 13507,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1009",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 11734,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 562",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon"
          },
          {
            "name": "Decapsulation",
            "value": 6887,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 314",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 30937,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 852",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 16536,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1107",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 15794,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 508",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon"
          },
          {
            "name": "Decapsulation",
            "value": 8780,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 295",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 524,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 152",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 391,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 85",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon"
          },
          {
            "name": "PK Validation",
            "value": 780,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 129",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 583,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 165",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon"
          },
          {
            "name": "PK Validation",
            "value": 1077,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 538",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 793,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 217",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon"
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
          "id": "0cc077121ef292dbc42308388552d6468b3567ce",
          "message": "Merge pull request #922 from cryspen/wysiwys/kem-derand\n\nAdd `no_std` support to additional libcrux crates",
          "timestamp": "2025-04-16T12:19:24Z",
          "url": "https://github.com/cryspen/libcrux/commit/0cc077121ef292dbc42308388552d6468b3567ce"
        },
        "date": 1744806814890,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 19405,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 305",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 19291,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 84",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 10761,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 171",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 10447,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 105",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 33375,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 360",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 32839,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 670",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 15047,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 266",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 14845,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 135",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 52516,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 643",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 52233,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 698",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 20784,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 454",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 20429,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 221",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 23095,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 116",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 14665,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 119",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 11760,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 109",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5281,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 34",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 38768,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 411",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 21698,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 90",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 16271,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 129",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 6544,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 155",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 58651,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 649",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 31118,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 205",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 22907,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 208",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 9303,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 123",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 28788,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 232",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 21941,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 146",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 12931,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 81",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 8893,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 42",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 46388,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 445",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 32001,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 105",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 17848,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 303",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 12130,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 47",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 69086,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 776",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 44313,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 480",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 25373,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 210",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 16537,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 94",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 917,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 15",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 418,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 8",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1337,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 10",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 591,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 16",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1827,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 40",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 828,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 21",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
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
          "id": "0cc077121ef292dbc42308388552d6468b3567ce",
          "message": "Merge pull request #922 from cryspen/wysiwys/kem-derand\n\nAdd `no_std` support to additional libcrux crates",
          "timestamp": "2025-04-16T12:19:24Z",
          "url": "https://github.com/cryspen/libcrux/commit/0cc077121ef292dbc42308388552d6468b3567ce"
        },
        "date": 1744806947839,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 22345,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1678",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 22366,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1534",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 10857,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1832",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 11197,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1515",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 41283,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 18584",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 41453,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 11200",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 17769,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2961",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 18172,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 5682",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 66000,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 24701",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 63141,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 35760",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 24729,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 4806",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 27937,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 12988",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 34038,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 4260",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 15755,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 7794",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 12314,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2173",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 6308,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2770",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 49057,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 15681",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 27301,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 17860",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 18779,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 9186",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 8469,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1034",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 71617,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 14605",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 35660,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 9126",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 28016,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 6916",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 11287,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1614",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 36316,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 7344",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 27846,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2425",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 13377,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1290",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 9259,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1138",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 54977,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 6191",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 39269,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1895",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 18733,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 4651",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 12882,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1600",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 79151,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 5979",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 51830,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 3383",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 26737,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 4020",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 18196,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 1360",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 1200,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 392",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 465,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 44",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1716,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 95",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 662,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 111",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 2246,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 132",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 878,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 109",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
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
          "id": "0cc077121ef292dbc42308388552d6468b3567ce",
          "message": "Merge pull request #922 from cryspen/wysiwys/kem-derand\n\nAdd `no_std` support to additional libcrux crates",
          "timestamp": "2025-04-16T12:19:24Z",
          "url": "https://github.com/cryspen/libcrux/commit/0cc077121ef292dbc42308388552d6468b3567ce"
        },
        "date": 1744806943447,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 50721,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 466",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 50190,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 477",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 77506,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1109",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 77743,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 604",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 121103,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1415",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 121758,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 2378",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 53647,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1164",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 26447,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 307",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 86704,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1342",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 30651,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 224",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 132229,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 2081",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 42901,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 377",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 61368,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 2654",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 42184,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 429",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 94608,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1252",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 54586,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 463",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 143466,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1612",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 73768,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 670",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 1437,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 45",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 2082,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 61",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 2692,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 87",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
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
          "id": "3d356440bea25987a22c37cc21c8ad65a530acd7",
          "message": "Merge pull request #926 from cryspen/franziskus/psq-cleanup\n\npsq: drop flamegraph",
          "timestamp": "2025-04-22T14:18:16Z",
          "url": "https://github.com/cryspen/libcrux/commit/3d356440bea25987a22c37cc21c8ad65a530acd7"
        },
        "date": 1745332143031,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 49327,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 986",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 48753,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1247",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 76866,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 910",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 75631,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 751",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 119564,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1247",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 120190,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1660",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 52955,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 372",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 26359,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 255",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 84839,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 746",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 30922,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 406",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 130860,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1546",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 43429,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 458",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 59338,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 461",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 41999,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 268",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 92766,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1117",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 52999,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 330",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 140263,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1661",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 71640,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 709",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 1063,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 35",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 1549,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 29",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 2086,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 31",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
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
          "id": "3d356440bea25987a22c37cc21c8ad65a530acd7",
          "message": "Merge pull request #926 from cryspen/franziskus/psq-cleanup\n\npsq: drop flamegraph",
          "timestamp": "2025-04-22T14:18:16Z",
          "url": "https://github.com/cryspen/libcrux/commit/3d356440bea25987a22c37cc21c8ad65a530acd7"
        },
        "date": 1745332320993,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 9526,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 233",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 9312,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 305",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 5107,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 84",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 4958,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 170",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 15850,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 158",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 15583,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 233",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 9494,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 130",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 9475,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 132",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 24865,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 503",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 25025,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 613",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 13236,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 205",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 13324,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 389",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 10650,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 185",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5719,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 160",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 5622,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 155",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 2773,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 200",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 19142,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1302",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 8843,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 693",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 11113,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 485",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 4209,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 263",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 29345,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1493",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 11966,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 834",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 15789,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 806",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5682,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 401",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 13800,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 983",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 9650,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1136",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 6839,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 354",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon"
          },
          {
            "name": "Decapsulation",
            "value": 5211,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 334",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 24879,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 3363",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 13079,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 2308",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 11757,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 396",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon"
          },
          {
            "name": "Decapsulation",
            "value": 6919,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 435",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 32120,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1107",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 17125,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 479",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 15724,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 429",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon"
          },
          {
            "name": "Decapsulation",
            "value": 8766,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 442",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 521,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 153",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 393,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 80",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon"
          },
          {
            "name": "PK Validation",
            "value": 777,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 280",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 589,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 83",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon"
          },
          {
            "name": "PK Validation",
            "value": 1037,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 474",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 797,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 239",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon"
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
          "id": "3d356440bea25987a22c37cc21c8ad65a530acd7",
          "message": "Merge pull request #926 from cryspen/franziskus/psq-cleanup\n\npsq: drop flamegraph",
          "timestamp": "2025-04-22T14:18:16Z",
          "url": "https://github.com/cryspen/libcrux/commit/3d356440bea25987a22c37cc21c8ad65a530acd7"
        },
        "date": 1745332350000,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 19488,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 672",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 19203,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 136",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 10779,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 210",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 10545,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 166",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 33364,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 566",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 32902,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 780",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 15035,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 227",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 14900,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 103",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 52927,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 1174",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 52269,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 781",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 20745,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 197",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 20505,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 204",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 23231,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 184",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 14705,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 346",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 11739,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 53",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5339,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 117",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 39062,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 502",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 21807,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 150",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 16305,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 142",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 6547,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 153",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 58652,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 1001",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 31037,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 130",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 23053,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 196",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 9197,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 76",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 28904,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 223",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 21851,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 106",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 12940,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 65",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 9064,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 53",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 46387,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 500",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 32039,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 105",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 17929,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 133",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 12176,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 171",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 68894,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 842",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 44579,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 197",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 25458,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 361",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 16594,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 221",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 915,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 26",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 404,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 17",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1359,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 10",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 594,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 15",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 1851,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 59",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 800,
            "unit": "ns/iter",
            "os": "ubuntu-latest_64",
            "range": "± 36",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
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
          "id": "3d356440bea25987a22c37cc21c8ad65a530acd7",
          "message": "Merge pull request #926 from cryspen/franziskus/psq-cleanup\n\npsq: drop flamegraph",
          "timestamp": "2025-04-22T14:18:16Z",
          "url": "https://github.com/cryspen/libcrux/commit/3d356440bea25987a22c37cc21c8ad65a530acd7"
        },
        "date": 1745332401597,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 50448,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 475",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 49887,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 433",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 77392,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1816",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 77638,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 831",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 121572,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1360",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 121705,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1445",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 53742,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 571",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 26245,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 212",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 86060,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1183",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 31117,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 255",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 131063,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1602",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 43431,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 277",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 61029,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1892",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 42586,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 178",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 93500,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1329",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 53667,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 388",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 141097,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 1811",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 72471,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 777",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 1428,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 30",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 2063,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 64",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 2733,
            "unit": "ns/iter",
            "os": "windows-latest_32",
            "range": "± 134",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
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
          "id": "3d356440bea25987a22c37cc21c8ad65a530acd7",
          "message": "Merge pull request #926 from cryspen/franziskus/psq-cleanup\n\npsq: drop flamegraph",
          "timestamp": "2025-04-22T14:18:16Z",
          "url": "https://github.com/cryspen/libcrux/commit/3d356440bea25987a22c37cc21c8ad65a530acd7"
        },
        "date": 1745332626278,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 33897,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 5508",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 32340,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 6576",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 18976,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2475",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 18922,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 4036",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 61985,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 17110",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 55176,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 59286",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 26369,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 6792",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 25527,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 3397",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 81816,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 8265",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 80801,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 36333",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 35761,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 14012",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 36649,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 13211",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 43285,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 7920",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 23754,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 13256",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 17291,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 2980",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 11121,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 5385",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 66680,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 8283",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 28198,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 4557",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 25440,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 3282",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 10011,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 4192",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 89236,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 13040",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 39213,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 8338",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 35481,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 11334",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 14650,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 4101",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 49117,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 7592",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 37980,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 15045",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 18207,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 4786",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 13041,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 4736",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 71626,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 35250",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 55017,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 27101",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 24590,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 4494",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 16374,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 6584",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 122308,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 28046",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 78122,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 22537",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 39958,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 6355",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
          },
          {
            "name": "Decapsulation",
            "value": 27030,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 5457",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 1589,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 287",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 616,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 77",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 2477,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 262",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 1027,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 171",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "avx2"
          },
          {
            "name": "PK Validation",
            "value": 3565,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 984",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 1208,
            "unit": "ns/iter",
            "os": "macos-13_64",
            "range": "± 138",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "avx2"
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
          "id": "2a67890fa5b82134b34daf627a649e7075287c67",
          "message": "Merge pull request #921 from cryspen/dependabot/go_modules/benchmarks/benches/circl/golang.org/x/crypto-0.35.0\n\nBump golang.org/x/crypto from 0.31.0 to 0.35.0 in /benchmarks/benches/circl",
          "timestamp": "2025-04-23T08:23:13Z",
          "url": "https://github.com/cryspen/libcrux/commit/2a67890fa5b82134b34daf627a649e7075287c67"
        },
        "date": 1745397234705,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 49350,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 842",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 48758,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1932",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 76575,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1076",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 75530,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1280",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 119334,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1536",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 120239,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 3122",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 53021,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 295",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 26184,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 160",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 84702,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1157",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 30831,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 246",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 130386,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 3485",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 43423,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1625",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 59342,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 725",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 41935,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 199",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 92960,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 2216",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 52546,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 573",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 140446,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 1388",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 72591,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 982",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 1062,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 86",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 1547,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 122",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 2080,
            "unit": "ns/iter",
            "os": "ubuntu-latest_32",
            "range": "± 99",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
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
          "id": "2a67890fa5b82134b34daf627a649e7075287c67",
          "message": "Merge pull request #921 from cryspen/dependabot/go_modules/benchmarks/benches/circl/golang.org/x/crypto-0.35.0\n\nBump golang.org/x/crypto from 0.31.0 to 0.35.0 in /benchmarks/benches/circl",
          "timestamp": "2025-04-23T08:23:13Z",
          "url": "https://github.com/cryspen/libcrux/commit/2a67890fa5b82134b34daf627a649e7075287c67"
        },
        "date": 1745397423934,
        "bigger_is_better": false,
        "benches": [
          {
            "name": "Key Generation",
            "value": 9525,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 823",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 9267,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 304",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 5225,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 259",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 4973,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 371",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 15927,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1489",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 15591,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 783",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 10304,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1002",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 10730,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 922",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 26055,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 2005",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 24923,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 698",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Key Generation",
            "value": 14214,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1085",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Key Generation",
            "value": 13976,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 536",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 11047,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 307",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5920,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 189",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 5642,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 198",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 3180,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 286",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 19811,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 2352",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 8045,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 505",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 10468,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 550",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 4134,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 490",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 28950,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1231",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 12287,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 2047",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked (external random)"
          },
          {
            "name": "Encapsulation",
            "value": 15828,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1554",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "external random"
          },
          {
            "name": "Encapsulation",
            "value": 5691,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 917",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "unpacked (external random)"
          },
          {
            "name": "Decapsulation",
            "value": 13653,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 731",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 9505,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 847",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 7250,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 643",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon"
          },
          {
            "name": "Decapsulation",
            "value": 5279,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 530",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 22340,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1657",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 13352,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 983",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 12653,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1016",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon"
          },
          {
            "name": "Decapsulation",
            "value": 7534,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 570",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 33274,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1500",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "Decapsulation",
            "value": 17893,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1166",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable",
            "api": "unpacked"
          },
          {
            "name": "Decapsulation",
            "value": 16905,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 1214",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon"
          },
          {
            "name": "Decapsulation",
            "value": 9774,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 3191",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon",
            "api": "unpacked"
          },
          {
            "name": "PK Validation",
            "value": 643,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 559",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 431,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 134",
            "category": "ML-KEM",
            "keySize": 512,
            "platform": "neon"
          },
          {
            "name": "PK Validation",
            "value": 799,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 356",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 624,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 200",
            "category": "ML-KEM",
            "keySize": 768,
            "platform": "neon"
          },
          {
            "name": "PK Validation",
            "value": 1300,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 518",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "portable"
          },
          {
            "name": "PK Validation",
            "value": 949,
            "unit": "ns/iter",
            "os": "macos-latest_64",
            "range": "± 402",
            "category": "ML-KEM",
            "keySize": 1024,
            "platform": "neon"
          }
        ]
      }
    ]
  }
}