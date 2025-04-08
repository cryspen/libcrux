window.BENCHMARK_DATA = {
  "lastUpdate": 1744111250146,
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
      }
    ]
  }
}