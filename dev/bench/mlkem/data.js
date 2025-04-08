window.BENCHMARK_DATA = {
  "lastUpdate": 1744129967974,
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
      }
    ]
  }
}