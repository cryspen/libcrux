window.BENCHMARK_DATA = {
  "lastUpdate": 1744111442581,
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
      }
    ]
  }
}