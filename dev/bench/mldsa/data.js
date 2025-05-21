window.BENCHMARK_DATA = {
  "lastUpdate": 1747814769001,
  "repoUrl": "https://github.com/cryspen/libcrux",
  "entries": {
    "ML-DSA Benchmark": [
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "Franziskus Kiefer"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "879dc2826c6d8953d1bc4bcf6992f8d449d4a90b",
          "message": "Merge pull request #980 from cryspen/wysiwys/output-benchmarks-to-same-repo\n\n[CI] Push ML-KEM and ML-DSA benchmark results to `gh-pages` branch in this repository",
          "timestamp": "2025-05-19T14:30:01Z",
          "url": "/commits/879dc2826c6d8953d1bc4bcf6992f8d449d4a90b"
        },
        "date": 1747665186030,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 78,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 328,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 87,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 75,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 90,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 35,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 25,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 78,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 31,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 152,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 525,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 145,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 140,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 143,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 70,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 44,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 125,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 49,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 221,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 655,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 229,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 240,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 176,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 80,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 70,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 146,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 75,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "auto"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "Franziskus Kiefer"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "879dc2826c6d8953d1bc4bcf6992f8d449d4a90b",
          "message": "Merge pull request #980 from cryspen/wysiwys/output-benchmarks-to-same-repo\n\n[CI] Push ML-KEM and ML-DSA benchmark results to `gh-pages` branch in this repository",
          "timestamp": "2025-05-19T14:30:01Z",
          "url": "/commits/879dc2826c6d8953d1bc4bcf6992f8d449d4a90b"
        },
        "date": 1747665360414,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 209,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 536,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 206,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 260,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 811,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 286,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 399,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 868,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 364,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 476,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.32,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 479,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 631,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 1.13,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 604,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 780,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.68,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 803,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "auto"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "Franziskus Kiefer"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "879dc2826c6d8953d1bc4bcf6992f8d449d4a90b",
          "message": "Merge pull request #980 from cryspen/wysiwys/output-benchmarks-to-same-repo\n\n[CI] Push ML-KEM and ML-DSA benchmark results to `gh-pages` branch in this repository",
          "timestamp": "2025-05-19T14:30:01Z",
          "url": "/commits/879dc2826c6d8953d1bc4bcf6992f8d449d4a90b"
        },
        "date": 1747665401680,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 77,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 323,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 86,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 77,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 96,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 35,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 105,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 444,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 119,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 151,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 534,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 142,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 134,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 143,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 54,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 191,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 708,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 188,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 221,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 646,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 228,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 247,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 179,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 84,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 294,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 881,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 312,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "auto"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "Franziskus Kiefer"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "879dc2826c6d8953d1bc4bcf6992f8d449d4a90b",
          "message": "Merge pull request #980 from cryspen/wysiwys/output-benchmarks-to-same-repo\n\n[CI] Push ML-KEM and ML-DSA benchmark results to `gh-pages` branch in this repository",
          "timestamp": "2025-05-19T14:30:01Z",
          "url": "/commits/879dc2826c6d8953d1bc4bcf6992f8d449d4a90b"
        },
        "date": 1747665521076,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 212,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 542,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 208,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 225,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 697,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 241,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 403,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 870,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 369,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 413,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.16,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 400,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 639,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 1.14,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 610,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 657,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.42,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 664,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "auto"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "Franziskus Kiefer"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "879dc2826c6d8953d1bc4bcf6992f8d449d4a90b",
          "message": "Merge pull request #980 from cryspen/wysiwys/output-benchmarks-to-same-repo\n\n[CI] Push ML-KEM and ML-DSA benchmark results to `gh-pages` branch in this repository",
          "timestamp": "2025-05-19T14:30:01Z",
          "url": "/commits/879dc2826c6d8953d1bc4bcf6992f8d449d4a90b"
        },
        "date": 1747666613611,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 107,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 411,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 108,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 85,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 137,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 47,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 219,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 643,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 208,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 167,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 207,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 72,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 310,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 746,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 306,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 263,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 199,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 95,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "avx2"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "Franziskus Kiefer"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "879dc2826c6d8953d1bc4bcf6992f8d449d4a90b",
          "message": "Merge pull request #980 from cryspen/wysiwys/output-benchmarks-to-same-repo\n\n[CI] Push ML-KEM and ML-DSA benchmark results to `gh-pages` branch in this repository",
          "timestamp": "2025-05-19T14:30:01Z",
          "url": "/commits/879dc2826c6d8953d1bc4bcf6992f8d449d4a90b"
        },
        "date": 1747666763334,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 41,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 151,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 44,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 29,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 137,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "neon"
          },
          {
            "value": 33,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "neon"
          },
          {
            "value": 22,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 72,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 25,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 81,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 289,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 74,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 57,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 218,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "neon"
          },
          {
            "value": 51,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "neon"
          },
          {
            "value": 47,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 106,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 36,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 111,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 304,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 115,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 75,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 251,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "neon"
          },
          {
            "value": 78,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "neon"
          },
          {
            "value": 54,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 129,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 57,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "auto"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "Franziskus Kiefer"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "50eb9beccf4a634a65dd4d4bebb76ba972b3add7",
          "message": "Merge pull request #982 from cryspen/jonas/psq-ci\n\nAdd CI workflow for building & testing PSQ",
          "timestamp": "2025-05-20T09:14:22Z",
          "url": "/commits/50eb9beccf4a634a65dd4d4bebb76ba972b3add7"
        },
        "date": 1747732604062,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 39,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 152,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 44,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 27,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 131,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "neon"
          },
          {
            "value": 32,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "neon"
          },
          {
            "value": 22,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 72,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 25,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 81,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 246,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 72,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 62,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 257,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "neon"
          },
          {
            "value": 57,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "neon"
          },
          {
            "value": 55,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 117,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 39,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 116,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 302,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 115,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 71,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 264,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "neon"
          },
          {
            "value": 80,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "neon"
          },
          {
            "value": 55,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 129,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 56,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "auto"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "Franziskus Kiefer"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "50eb9beccf4a634a65dd4d4bebb76ba972b3add7",
          "message": "Merge pull request #982 from cryspen/jonas/psq-ci\n\nAdd CI workflow for building & testing PSQ",
          "timestamp": "2025-05-20T09:14:22Z",
          "url": "/commits/50eb9beccf4a634a65dd4d4bebb76ba972b3add7"
        },
        "date": 1747732651694,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 78,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 331,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 87,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 75,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 90,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 36,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 25,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 77,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 31,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 152,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 540,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 144,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 140,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 156,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 68,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 44,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 123,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 49,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 222,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 649,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 229,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 242,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 179,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 80,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 70,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 145,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 75,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "auto"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "Franziskus Kiefer"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "50eb9beccf4a634a65dd4d4bebb76ba972b3add7",
          "message": "Merge pull request #982 from cryspen/jonas/psq-ci\n\nAdd CI workflow for building & testing PSQ",
          "timestamp": "2025-05-20T09:14:22Z",
          "url": "/commits/50eb9beccf4a634a65dd4d4bebb76ba972b3add7"
        },
        "date": 1747732677695,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 76,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 273,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 84,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 71,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 103,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 37,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 148,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 455,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 143,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 118,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 160,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 54,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 224,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 542,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 226,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 197,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 210,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 94,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "avx2"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "Franziskus Kiefer"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "50eb9beccf4a634a65dd4d4bebb76ba972b3add7",
          "message": "Merge pull request #982 from cryspen/jonas/psq-ci\n\nAdd CI workflow for building & testing PSQ",
          "timestamp": "2025-05-20T09:14:22Z",
          "url": "/commits/50eb9beccf4a634a65dd4d4bebb76ba972b3add7"
        },
        "date": 1747732825974,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 209,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 533,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 206,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 260,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 807,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 286,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 399,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 872,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 366,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 476,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.32,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 476,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 634,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 1.14,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 606,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 783,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.67,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 803,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "auto"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "Franziskus Kiefer"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "50eb9beccf4a634a65dd4d4bebb76ba972b3add7",
          "message": "Merge pull request #982 from cryspen/jonas/psq-ci\n\nAdd CI workflow for building & testing PSQ",
          "timestamp": "2025-05-20T09:14:22Z",
          "url": "/commits/50eb9beccf4a634a65dd4d4bebb76ba972b3add7"
        },
        "date": 1747732863590,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 78,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 324,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 86,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 79,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 98,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 35,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 104,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 447,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 119,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 150,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 539,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 143,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 134,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 141,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 54,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 191,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 706,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 188,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 220,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 649,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 228,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 235,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 177,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 84,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 295,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 881,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 310,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "auto"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "Franziskus Kiefer"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "50eb9beccf4a634a65dd4d4bebb76ba972b3add7",
          "message": "Merge pull request #982 from cryspen/jonas/psq-ci\n\nAdd CI workflow for building & testing PSQ",
          "timestamp": "2025-05-20T09:14:22Z",
          "url": "/commits/50eb9beccf4a634a65dd4d4bebb76ba972b3add7"
        },
        "date": 1747733058958,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 212,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 543,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 209,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 225,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 706,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 242,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 402,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 866,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 370,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 413,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.15,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 400,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 639,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 1.13,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 611,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 657,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.44,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 667,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "auto"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "Franziskus Kiefer"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "87f49c6c5517daebf596903972981b1f3e34fbb1",
          "message": "Merge pull request #985 from cryspen/wysiwys/ed25519-wycheproof-dev-dependency\n\nmove wycheproof to dev dependencies in `libcrux-ed25519`",
          "timestamp": "2025-05-20T15:23:12Z",
          "url": "/commits/87f49c6c5517daebf596903972981b1f3e34fbb1"
        },
        "date": 1747754753092,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 40,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 156,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 44,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 28,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 134,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "neon"
          },
          {
            "value": 35,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "neon"
          },
          {
            "value": 23,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 79,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 27,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 86,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 257,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 74,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 59,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 220,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "neon"
          },
          {
            "value": 53,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "neon"
          },
          {
            "value": 48,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 112,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 37,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 115,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 318,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 120,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 75,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 259,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "neon"
          },
          {
            "value": 81,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "neon"
          },
          {
            "value": 57,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 133,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 58,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "auto"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "Franziskus Kiefer"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "87f49c6c5517daebf596903972981b1f3e34fbb1",
          "message": "Merge pull request #985 from cryspen/wysiwys/ed25519-wycheproof-dev-dependency\n\nmove wycheproof to dev dependencies in `libcrux-ed25519`",
          "timestamp": "2025-05-20T15:23:12Z",
          "url": "/commits/87f49c6c5517daebf596903972981b1f3e34fbb1"
        },
        "date": 1747754779537,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 79,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 333,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 87,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 75,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 91,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 35,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 25,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 78,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 31,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 152,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 538,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 145,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 139,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 157,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 56,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 44,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 123,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 49,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 221,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 661,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 229,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 241,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 177,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 80,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 70,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 144,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 74,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "auto"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "Franziskus Kiefer"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "87f49c6c5517daebf596903972981b1f3e34fbb1",
          "message": "Merge pull request #985 from cryspen/wysiwys/ed25519-wycheproof-dev-dependency\n\nmove wycheproof to dev dependencies in `libcrux-ed25519`",
          "timestamp": "2025-05-20T15:23:12Z",
          "url": "/commits/87f49c6c5517daebf596903972981b1f3e34fbb1"
        },
        "date": 1747754807658,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 73,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 264,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 81,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 60,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 104,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 38,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 149,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 430,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 135,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 111,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 144,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 51,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 234,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 523,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 216,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 188,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 178,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 77,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "avx2"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "Franziskus Kiefer"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "87f49c6c5517daebf596903972981b1f3e34fbb1",
          "message": "Merge pull request #985 from cryspen/wysiwys/ed25519-wycheproof-dev-dependency\n\nmove wycheproof to dev dependencies in `libcrux-ed25519`",
          "timestamp": "2025-05-20T15:23:12Z",
          "url": "/commits/87f49c6c5517daebf596903972981b1f3e34fbb1"
        },
        "date": 1747754916995,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 77,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 324,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 86,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 73,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 90,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 35,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 105,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 448,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 119,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 150,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 538,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 142,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 134,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 140,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 55,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 193,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 711,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 188,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 221,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 642,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 228,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 235,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 176,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 85,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 295,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 876,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 311,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "auto"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "Franziskus Kiefer"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "87f49c6c5517daebf596903972981b1f3e34fbb1",
          "message": "Merge pull request #985 from cryspen/wysiwys/ed25519-wycheproof-dev-dependency\n\nmove wycheproof to dev dependencies in `libcrux-ed25519`",
          "timestamp": "2025-05-20T15:23:12Z",
          "url": "/commits/87f49c6c5517daebf596903972981b1f3e34fbb1"
        },
        "date": 1747754966288,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 210,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 537,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 207,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 260,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 804,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 286,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 414,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 876,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 365,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 477,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.32,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 475,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 629,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 1.13,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 602,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 781,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.67,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 802,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "auto"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "Franziskus Kiefer"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "87f49c6c5517daebf596903972981b1f3e34fbb1",
          "message": "Merge pull request #985 from cryspen/wysiwys/ed25519-wycheproof-dev-dependency\n\nmove wycheproof to dev dependencies in `libcrux-ed25519`",
          "timestamp": "2025-05-20T15:23:12Z",
          "url": "/commits/87f49c6c5517daebf596903972981b1f3e34fbb1"
        },
        "date": 1747755128894,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 212,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 543,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 207,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 224,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 702,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 241,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 403,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 877,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 370,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 414,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.15,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 400,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 638,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 1.12,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 610,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 659,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.42,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 666,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "auto"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "Franziskus Kiefer"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "6e0aaa669f1fbe9713a91288a753931d7cb8442d",
          "message": "Merge pull request #882 from cryspen/sha3-arm\n\nSome optimizations for SHA-3 on Aarch64",
          "timestamp": "2025-05-20T17:54:06Z",
          "url": "/commits/6e0aaa669f1fbe9713a91288a753931d7cb8442d"
        },
        "date": 1747763824378,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 72,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 257,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 76,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 58,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 88,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 33,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 139,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 404,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 129,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 105,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 138,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 50,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 202,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 497,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 202,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 185,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 177,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 76,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "avx2"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "Franziskus Kiefer"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "6e0aaa669f1fbe9713a91288a753931d7cb8442d",
          "message": "Merge pull request #882 from cryspen/sha3-arm\n\nSome optimizations for SHA-3 on Aarch64",
          "timestamp": "2025-05-20T17:54:06Z",
          "url": "/commits/6e0aaa669f1fbe9713a91288a753931d7cb8442d"
        },
        "date": 1747763826191,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 42,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 163,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 45,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 30,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 150,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "neon"
          },
          {
            "value": 35,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "neon"
          },
          {
            "value": 24,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 79,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 28,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 87,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 262,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 80,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 65,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 277,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "neon"
          },
          {
            "value": 60,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "neon"
          },
          {
            "value": 51,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 123,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 41,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 129,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 336,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 147,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 143,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 494,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "neon"
          },
          {
            "value": 103,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "neon"
          },
          {
            "value": 67,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 149,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 61,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "auto"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "Franziskus Kiefer"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "6e0aaa669f1fbe9713a91288a753931d7cb8442d",
          "message": "Merge pull request #882 from cryspen/sha3-arm\n\nSome optimizations for SHA-3 on Aarch64",
          "timestamp": "2025-05-20T17:54:06Z",
          "url": "/commits/6e0aaa669f1fbe9713a91288a753931d7cb8442d"
        },
        "date": 1747763835128,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 76,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 327,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 86,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 75,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 91,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 34,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 25,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 78,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 31,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 150,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 525,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 142,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 138,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 139,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 53,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 44,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 127,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 49,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 219,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 641,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 224,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 244,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 181,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 84,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 70,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 143,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 74,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "auto"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "Franziskus Kiefer"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "6e0aaa669f1fbe9713a91288a753931d7cb8442d",
          "message": "Merge pull request #882 from cryspen/sha3-arm\n\nSome optimizations for SHA-3 on Aarch64",
          "timestamp": "2025-05-20T17:54:06Z",
          "url": "/commits/6e0aaa669f1fbe9713a91288a753931d7cb8442d"
        },
        "date": 1747763982944,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 76,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 326,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 84,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 74,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 90,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 36,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 105,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 451,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 120,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 148,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 537,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 139,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 133,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 139,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 53,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 192,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 701,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 189,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 214,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 633,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 222,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 259,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 179,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 83,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 296,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 880,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 311,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "auto"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "Franziskus Kiefer"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "6e0aaa669f1fbe9713a91288a753931d7cb8442d",
          "message": "Merge pull request #882 from cryspen/sha3-arm\n\nSome optimizations for SHA-3 on Aarch64",
          "timestamp": "2025-05-20T17:54:06Z",
          "url": "/commits/6e0aaa669f1fbe9713a91288a753931d7cb8442d"
        },
        "date": 1747764011526,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 209,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 568,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 217,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 261,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 806,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 287,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 396,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 927,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 379,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 473,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.3,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 471,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 629,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 1.18,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 617,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 780,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.67,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 802,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "auto"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "Franziskus Kiefer"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "6e0aaa669f1fbe9713a91288a753931d7cb8442d",
          "message": "Merge pull request #882 from cryspen/sha3-arm\n\nSome optimizations for SHA-3 on Aarch64",
          "timestamp": "2025-05-20T17:54:06Z",
          "url": "/commits/6e0aaa669f1fbe9713a91288a753931d7cb8442d"
        },
        "date": 1747764072699,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 208,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 567,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 229,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 224,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 713,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 239,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 396,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 905,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 375,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 406,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.12,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 394,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 625,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 1.16,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 612,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 659,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.42,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 666,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "auto"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "Franziskus Kiefer"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "fd1e10f98bfe7a1afddf4de64d9727e7e6304540",
          "message": "Merge pull request #882 from cryspen/sha3-arm\n\nSome optimizations for SHA-3 on Aarch64",
          "timestamp": "2025-05-21T04:51:52Z",
          "url": "/commits/fd1e10f98bfe7a1afddf4de64d9727e7e6304540"
        },
        "date": 1747803255033,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 38,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 151,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 42,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 26,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 128,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "neon"
          },
          {
            "value": 32,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "neon"
          },
          {
            "value": 22,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 71,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 26,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 80,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 247,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 70,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 57,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 211,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "neon"
          },
          {
            "value": 50,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "neon"
          },
          {
            "value": 47,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 109,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 36,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 111,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 294,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 113,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 72,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 255,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "neon"
          },
          {
            "value": 80,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "neon"
          },
          {
            "value": 57,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 135,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 60,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "auto"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "Franziskus Kiefer"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "fd1e10f98bfe7a1afddf4de64d9727e7e6304540",
          "message": "Merge pull request #882 from cryspen/sha3-arm\n\nSome optimizations for SHA-3 on Aarch64",
          "timestamp": "2025-05-21T04:51:52Z",
          "url": "/commits/fd1e10f98bfe7a1afddf4de64d9727e7e6304540"
        },
        "date": 1747803301439,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 76,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 329,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 85,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 75,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 89,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 34,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 25,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 77,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 31,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 150,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 530,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 142,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 137,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 138,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 56,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 44,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 124,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 49,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 216,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 644,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 224,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 240,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 175,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 80,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 70,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 145,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 75,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "auto"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "Franziskus Kiefer"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "fd1e10f98bfe7a1afddf4de64d9727e7e6304540",
          "message": "Merge pull request #882 from cryspen/sha3-arm\n\nSome optimizations for SHA-3 on Aarch64",
          "timestamp": "2025-05-21T04:51:52Z",
          "url": "/commits/fd1e10f98bfe7a1afddf4de64d9727e7e6304540"
        },
        "date": 1747803306771,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 72,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 267,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 83,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 59,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 90,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 34,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 139,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 433,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 133,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 110,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 145,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 52,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 217,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 507,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 209,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 196,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 191,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 78,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "avx2"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "Franziskus Kiefer"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "fd1e10f98bfe7a1afddf4de64d9727e7e6304540",
          "message": "Merge pull request #882 from cryspen/sha3-arm\n\nSome optimizations for SHA-3 on Aarch64",
          "timestamp": "2025-05-21T04:51:52Z",
          "url": "/commits/fd1e10f98bfe7a1afddf4de64d9727e7e6304540"
        },
        "date": 1747803480643,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 211,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 570,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 217,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 261,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 801,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 286,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 395,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 933,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 378,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 473,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.3,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 473,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 628,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 1.22,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 617,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 783,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.67,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 802,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "auto"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "Franziskus Kiefer"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "fd1e10f98bfe7a1afddf4de64d9727e7e6304540",
          "message": "Merge pull request #882 from cryspen/sha3-arm\n\nSome optimizations for SHA-3 on Aarch64",
          "timestamp": "2025-05-21T04:51:52Z",
          "url": "/commits/fd1e10f98bfe7a1afddf4de64d9727e7e6304540"
        },
        "date": 1747803513072,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 76,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 323,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 84,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 74,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 91,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 36,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 105,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 453,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 119,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 148,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 533,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 140,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 132,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 139,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 53,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 192,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 710,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 189,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 219,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 635,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 221,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 235,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 180,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 84,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 297,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 873,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 312,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "auto"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Franziskus Kiefer",
            "username": "Franziskus Kiefer"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "fd1e10f98bfe7a1afddf4de64d9727e7e6304540",
          "message": "Merge pull request #882 from cryspen/sha3-arm\n\nSome optimizations for SHA-3 on Aarch64",
          "timestamp": "2025-05-21T04:51:52Z",
          "url": "/commits/fd1e10f98bfe7a1afddf4de64d9727e7e6304540"
        },
        "date": 1747803618128,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 208,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 564,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 216,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 221,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 714,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 238,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 393,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 907,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 374,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 404,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.12,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 393,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 628,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 1.15,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 610,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 657,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.43,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 667,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "auto"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Lucas Franceschino",
            "username": "Lucas Franceschino"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "f4c2e5c01311fbbeeb317f7238a6b2fa7bcb2624",
          "message": "Merge pull request #971 from cryspen/fix-fstar-base-makefile\n\nF*: improve makefile, detect duplicates in `SLOW_MODULES`",
          "timestamp": "2025-05-21T08:00:17Z",
          "url": "/commits/f4c2e5c01311fbbeeb317f7238a6b2fa7bcb2624"
        },
        "date": 1747814617739,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 76,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 324,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 85,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 75,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 90,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 34,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 25,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 78,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 31,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 150,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 538,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 142,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 137,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 141,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 53,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 44,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 124,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 49,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 215,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 646,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 224,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 240,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 174,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 82,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 70,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 144,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 74,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "auto"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Lucas Franceschino",
            "username": "Lucas Franceschino"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "96abd9f2460ff92811a1c181662590d96c37949c",
          "message": "Merge pull request #970 from cryspen/update-core-models\n\ncore-models: backport changes from `cryspen/core-models`",
          "timestamp": "2025-05-21T08:02:48Z",
          "url": "/commits/96abd9f2460ff92811a1c181662590d96c37949c"
        },
        "date": 1747814764613,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 76,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 323,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 85,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 75,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 90,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 34,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 25,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 78,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 31,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 150,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 529,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 142,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 137,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 139,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 54,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 44,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 127,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 49,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 216,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 639,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 225,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 244,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 179,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 86,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 70,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 146,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 75,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "auto"
          }
        ]
      }
    ]
  },
  "groupBy": [
    "label",
    "keySize",
    "os"
  ],
  "schema": [
    "implementation",
    "keySize",
    "label",
    "hardware",
    "os"
  ]
}