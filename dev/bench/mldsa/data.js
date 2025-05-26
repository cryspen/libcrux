window.BENCHMARK_DATA = {
  "lastUpdate": 1748268257102,
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
        "date": 1747814788845,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 208,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 565,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 218,
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
            "value": 813,
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
            "value": 935,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 377,
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
            "value": 1.29,
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
            "value": 627,
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
            "value": 801,
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
        "date": 1747814855856,
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
            "value": 160,
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
            "value": 27,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 129,
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
            "value": 74,
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
            "value": 80,
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
            "value": 108,
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
            "value": 110,
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
            "value": 113,
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
            "value": 250,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "neon"
          },
          {
            "value": 79,
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
            "value": 128,
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
        "date": 1747814867767,
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
            "value": 325,
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
            "value": 442,
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
            "value": 152,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 526,
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
            "value": 141,
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
            "value": 712,
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
            "value": 215,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 644,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 223,
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
            "value": 83,
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
        "date": 1747814898894,
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
            "value": 570,
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
            "value": 222,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 708,
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
            "value": 395,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 897,
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
            "value": 393,
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
            "value": 1.17,
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
            "value": 658,
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
            "value": 665,
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
          "id": "96abd9f2460ff92811a1c181662590d96c37949c",
          "message": "Merge pull request #970 from cryspen/update-core-models\n\ncore-models: backport changes from `cryspen/core-models`",
          "timestamp": "2025-05-21T08:02:48Z",
          "url": "/commits/96abd9f2460ff92811a1c181662590d96c37949c"
        },
        "date": 1747814937131,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 208,
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
            "value": 218,
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
            "value": 810,
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
            "value": 396,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 922,
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
            "value": 472,
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
            "value": 628,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 1.19,
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
            "value": 779,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.66,
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
        "date": 1747814935394,
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
            "value": 320,
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
            "value": 81,
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
            "value": 450,
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
            "value": 149,
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
            "value": 720,
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
            "value": 215,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 641,
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
            "value": 179,
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
            "value": 296,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 872,
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
        "date": 1747815001545,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 80,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 268,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 89,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 64,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 98,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 35,
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
            "value": 423,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 132,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 108,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 139,
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
            "value": 205,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 499,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 203,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 186,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 179,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 80,
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
        "date": 1747815020606,
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
            "value": 559,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 215,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 220,
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
            "value": 394,
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
            "value": 373,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 405,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.11,
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
            "value": 624,
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
            "value": 611,
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
            "value": 1.43,
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
        "date": 1747815883922,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 90,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 311,
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
            "value": 61,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 100,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 35,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 164,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 449,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 144,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 129,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 163,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 59,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 246,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 581,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 231,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 199,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 197,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 86,
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
        "date": 1747815903440,
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
            "value": 155,
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
            "value": 133,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "neon"
          },
          {
            "value": 34,
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
            "value": 74,
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
            "value": 84,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 255,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 78,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 60,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 214,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "neon"
          },
          {
            "value": 52,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "neon"
          },
          {
            "value": 50,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 116,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 44,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 128,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 374,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 146,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 95,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 326,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "neon"
          },
          {
            "value": 95,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "neon"
          },
          {
            "value": 62,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 144,
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
          "id": "2cc36e8f62bc305ed45cbcf6c7672931f8f41d18",
          "message": "Merge pull request #991 from Parrot7483/fix-hacl-build\n\nfix build warning on linux",
          "timestamp": "2025-05-22T06:19:37Z",
          "url": "/commits/2cc36e8f62bc305ed45cbcf6c7672931f8f41d18"
        },
        "date": 1747894921099,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 43,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 158,
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
            "value": 72,
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
            "value": 244,
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
            "value": 120,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 305,
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
            "value": 71,
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
            "value": 131,
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
          "id": "2cc36e8f62bc305ed45cbcf6c7672931f8f41d18",
          "message": "Merge pull request #991 from Parrot7483/fix-hacl-build\n\nfix build warning on linux",
          "timestamp": "2025-05-22T06:19:37Z",
          "url": "/commits/2cc36e8f62bc305ed45cbcf6c7672931f8f41d18"
        },
        "date": 1747894958741,
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
            "value": 535,
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
            "value": 140,
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
            "value": 216,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 638,
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
            "value": 241,
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
            "value": 144,
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
          "id": "2cc36e8f62bc305ed45cbcf6c7672931f8f41d18",
          "message": "Merge pull request #991 from Parrot7483/fix-hacl-build\n\nfix build warning on linux",
          "timestamp": "2025-05-22T06:19:37Z",
          "url": "/commits/2cc36e8f62bc305ed45cbcf6c7672931f8f41d18"
        },
        "date": 1747894966835,
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
            "value": 254,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 77,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 63,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 94,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 35,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 143,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 421,
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
            "value": 114,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 153,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 53,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 233,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 534,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 218,
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
            "value": 191,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 83,
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
          "id": "2cc36e8f62bc305ed45cbcf6c7672931f8f41d18",
          "message": "Merge pull request #991 from Parrot7483/fix-hacl-build\n\nfix build warning on linux",
          "timestamp": "2025-05-22T06:19:37Z",
          "url": "/commits/2cc36e8f62bc305ed45cbcf6c7672931f8f41d18"
        },
        "date": 1747895143451,
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
            "value": 327,
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
            "value": 147,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 530,
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
            "value": 132,
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
            "value": 190,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 216,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 634,
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
            "value": 249,
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
            "value": 296,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 883,
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
          "id": "2cc36e8f62bc305ed45cbcf6c7672931f8f41d18",
          "message": "Merge pull request #991 from Parrot7483/fix-hacl-build\n\nfix build warning on linux",
          "timestamp": "2025-05-22T06:19:37Z",
          "url": "/commits/2cc36e8f62bc305ed45cbcf6c7672931f8f41d18"
        },
        "date": 1747895177629,
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
            "value": 570,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 218,
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
            "value": 810,
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
            "value": 915,
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
            "value": 1.21,
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
            "value": 1.68,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 801,
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
          "id": "2cc36e8f62bc305ed45cbcf6c7672931f8f41d18",
          "message": "Merge pull request #991 from Parrot7483/fix-hacl-build\n\nfix build warning on linux",
          "timestamp": "2025-05-22T06:19:37Z",
          "url": "/commits/2cc36e8f62bc305ed45cbcf6c7672931f8f41d18"
        },
        "date": 1747895217625,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 209,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 565,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 217,
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
            "value": 393,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 913,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 376,
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
            "value": 1.11,
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
            "value": 1.15,
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
            "value": 656,
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
            "value": 665,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "406ab5549c03ef90d021674f6e9ec3c3d238091d",
          "message": "Merge pull request #989 from cryspen/mldsa-portable-ntt\n\nRange Proofs and Proof Speedups for ML-DSA (Portable) NTT",
          "timestamp": "2025-05-22T13:21:43Z",
          "url": "/commits/406ab5549c03ef90d021674f6e9ec3c3d238091d"
        },
        "date": 1747920256457,
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
            "value": 154,
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
            "value": 33,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "neon"
          },
          {
            "value": 21,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 73,
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
            "value": 91,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 255,
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
            "value": 57,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 210,
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
            "value": 115,
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
            "value": 111,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 296,
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
            "value": 71,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 253,
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
            "value": 54,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 140,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "406ab5549c03ef90d021674f6e9ec3c3d238091d",
          "message": "Merge pull request #989 from cryspen/mldsa-portable-ntt\n\nRange Proofs and Proof Speedups for ML-DSA (Portable) NTT",
          "timestamp": "2025-05-22T13:21:43Z",
          "url": "/commits/406ab5549c03ef90d021674f6e9ec3c3d238091d"
        },
        "date": 1747920310368,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 77,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 326,
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
            "value": 26,
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
            "value": 531,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 143,
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
            "value": 140,
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
            "value": 126,
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
            "value": 218,
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
            "value": 241,
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
            "value": 83,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "406ab5549c03ef90d021674f6e9ec3c3d238091d",
          "message": "Merge pull request #989 from cryspen/mldsa-portable-ntt\n\nRange Proofs and Proof Speedups for ML-DSA (Portable) NTT",
          "timestamp": "2025-05-22T13:21:43Z",
          "url": "/commits/406ab5549c03ef90d021674f6e9ec3c3d238091d"
        },
        "date": 1747920326850,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 78,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 299,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 92,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 65,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 114,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 35,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 151,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 432,
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
            "value": 122,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 158,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 59,
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
            "value": 569,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 224,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 200,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 189,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 85,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "406ab5549c03ef90d021674f6e9ec3c3d238091d",
          "message": "Merge pull request #989 from cryspen/mldsa-portable-ntt\n\nRange Proofs and Proof Speedups for ML-DSA (Portable) NTT",
          "timestamp": "2025-05-22T13:21:43Z",
          "url": "/commits/406ab5549c03ef90d021674f6e9ec3c3d238091d"
        },
        "date": 1747920522576,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 218,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 590,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 225,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 276,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 852,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 302,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 415,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 975,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 395,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 508,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.4,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 501,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 662,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 1.28,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 654,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 833,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.78,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 835,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "406ab5549c03ef90d021674f6e9ec3c3d238091d",
          "message": "Merge pull request #989 from cryspen/mldsa-portable-ntt\n\nRange Proofs and Proof Speedups for ML-DSA (Portable) NTT",
          "timestamp": "2025-05-22T13:21:43Z",
          "url": "/commits/406ab5549c03ef90d021674f6e9ec3c3d238091d"
        },
        "date": 1747920521086,
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
            "value": 329,
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
            "value": 109,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 472,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 124,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 147,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 528,
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
            "value": 133,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 138,
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
            "value": 191,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 704,
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
            "value": 215,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 638,
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
            "value": 236,
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
            "value": 299,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 867,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 313,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "406ab5549c03ef90d021674f6e9ec3c3d238091d",
          "message": "Merge pull request #989 from cryspen/mldsa-portable-ntt\n\nRange Proofs and Proof Speedups for ML-DSA (Portable) NTT",
          "timestamp": "2025-05-22T13:21:43Z",
          "url": "/commits/406ab5549c03ef90d021674f6e9ec3c3d238091d"
        },
        "date": 1747920639201,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 209,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 572,
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
            "value": 227,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 710,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 244,
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
            "value": 919,
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
            "value": 415,
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
            "value": 402,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 627,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 1.17,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 613,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 669,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.49,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 677,
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
            "name": "Jan Winkelmann",
            "username": "Jan Winkelmann"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "b13627a96e4d204e5db026fdf5bb8bde623e7d58",
          "message": "Merge pull request #993 from cryspen/keks/release-prep-0.0.3\n\nBump most crates to 0.0.3-alpha.1 and add changelogs",
          "timestamp": "2025-05-22T15:41:43Z",
          "url": "/commits/b13627a96e4d204e5db026fdf5bb8bde623e7d58"
        },
        "date": 1747928692074,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 77,
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
            "value": 26,
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
            "value": 533,
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
            "value": 137,
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
            "value": 647,
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
            "value": 241,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 178,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 81,
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
            "name": "Jan Winkelmann",
            "username": "Jan Winkelmann"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "b13627a96e4d204e5db026fdf5bb8bde623e7d58",
          "message": "Merge pull request #993 from cryspen/keks/release-prep-0.0.3\n\nBump most crates to 0.0.3-alpha.1 and add changelogs",
          "timestamp": "2025-05-22T15:41:43Z",
          "url": "/commits/b13627a96e4d204e5db026fdf5bb8bde623e7d58"
        },
        "date": 1747928867807,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 208,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 575,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 219,
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
            "value": 805,
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
            "value": 928,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 377,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 475,
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
            "value": 628,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 1.19,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 624,
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
            "value": 1.66,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 801,
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
            "name": "Jan Winkelmann",
            "username": "Jan Winkelmann"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "b13627a96e4d204e5db026fdf5bb8bde623e7d58",
          "message": "Merge pull request #993 from cryspen/keks/release-prep-0.0.3\n\nBump most crates to 0.0.3-alpha.1 and add changelogs",
          "timestamp": "2025-05-22T15:41:43Z",
          "url": "/commits/b13627a96e4d204e5db026fdf5bb8bde623e7d58"
        },
        "date": 1747928893493,
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
            "value": 148,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 535,
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
            "value": 132,
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
            "value": 708,
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
            "value": 215,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 650,
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
            "value": 86,
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
            "name": "Jan Winkelmann",
            "username": "Jan Winkelmann"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "b13627a96e4d204e5db026fdf5bb8bde623e7d58",
          "message": "Merge pull request #993 from cryspen/keks/release-prep-0.0.3\n\nBump most crates to 0.0.3-alpha.1 and add changelogs",
          "timestamp": "2025-05-22T15:41:43Z",
          "url": "/commits/b13627a96e4d204e5db026fdf5bb8bde623e7d58"
        },
        "date": 1747928957809,
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
            "value": 712,
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
            "value": 394,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 908,
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
            "value": 393,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 624,
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
            "value": 611,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 658,
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
            "value": 665,
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
            "name": "Jan Winkelmann",
            "username": "Jan Winkelmann"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "b13627a96e4d204e5db026fdf5bb8bde623e7d58",
          "message": "Merge pull request #993 from cryspen/keks/release-prep-0.0.3\n\nBump most crates to 0.0.3-alpha.1 and add changelogs",
          "timestamp": "2025-05-22T15:41:43Z",
          "url": "/commits/b13627a96e4d204e5db026fdf5bb8bde623e7d58"
        },
        "date": 1747929199549,
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
            "value": 155,
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
            "value": 28,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 136,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "neon"
          },
          {
            "value": 34,
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
            "value": 29,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 93,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 301,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 86,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 68,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 268,
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
            "value": 56,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 113,
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
            "value": 119,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 341,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 145,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 78,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 273,
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
            "value": 56,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 128,
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
            "name": "Jan Winkelmann",
            "username": "Jan Winkelmann"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "b13627a96e4d204e5db026fdf5bb8bde623e7d58",
          "message": "Merge pull request #993 from cryspen/keks/release-prep-0.0.3\n\nBump most crates to 0.0.3-alpha.1 and add changelogs",
          "timestamp": "2025-05-22T15:41:43Z",
          "url": "/commits/b13627a96e4d204e5db026fdf5bb8bde623e7d58"
        },
        "date": 1747929288083,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 85,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 302,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 89,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 69,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 95,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 36,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 155,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 482,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 162,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 117,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 152,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 68,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 252,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 592,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 252,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 195,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 202,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 88,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "4d5f5b5cd3b4e259c9db06437fc70a63551ed92d",
          "message": "Merge pull request #989 from cryspen/mldsa-portable-ntt\n\nRange Proofs and Proof Speedups for ML-DSA (Portable) NTT",
          "timestamp": "2025-05-22T15:55:45Z",
          "url": "/commits/4d5f5b5cd3b4e259c9db06437fc70a63551ed92d"
        },
        "date": 1747929531933,
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
            "value": 331,
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
            "value": 74,
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
            "value": 537,
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
            "value": 648,
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
            "value": 241,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 178,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 81,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 71,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 142,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "4d5f5b5cd3b4e259c9db06437fc70a63551ed92d",
          "message": "Merge pull request #989 from cryspen/mldsa-portable-ntt\n\nRange Proofs and Proof Speedups for ML-DSA (Portable) NTT",
          "timestamp": "2025-05-22T15:55:45Z",
          "url": "/commits/4d5f5b5cd3b4e259c9db06437fc70a63551ed92d"
        },
        "date": 1747929713325,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 208,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 571,
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
            "value": 816,
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
            "value": 942,
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
            "value": 478,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.31,
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
            "value": 1.19,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 618,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 779,
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
            "value": 799,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "4d5f5b5cd3b4e259c9db06437fc70a63551ed92d",
          "message": "Merge pull request #989 from cryspen/mldsa-portable-ntt\n\nRange Proofs and Proof Speedups for ML-DSA (Portable) NTT",
          "timestamp": "2025-05-22T15:55:45Z",
          "url": "/commits/4d5f5b5cd3b4e259c9db06437fc70a63551ed92d"
        },
        "date": 1747929724770,
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
            "value": 329,
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
            "value": 81,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 92,
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
            "value": 111,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 484,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 126,
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
            "value": 529,
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
            "value": 134,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 142,
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
            "value": 215,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 637,
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
            "value": 83,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 298,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 874,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 313,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "4d5f5b5cd3b4e259c9db06437fc70a63551ed92d",
          "message": "Merge pull request #989 from cryspen/mldsa-portable-ntt\n\nRange Proofs and Proof Speedups for ML-DSA (Portable) NTT",
          "timestamp": "2025-05-22T15:55:45Z",
          "url": "/commits/4d5f5b5cd3b4e259c9db06437fc70a63551ed92d"
        },
        "date": 1747929834496,
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
            "value": 573,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 217,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 227,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 722,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 244,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 395,
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
            "value": 375,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 415,
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
            "value": 402,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 627,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 1.17,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 613,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 669,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.47,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 676,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "4d5f5b5cd3b4e259c9db06437fc70a63551ed92d",
          "message": "Merge pull request #989 from cryspen/mldsa-portable-ntt\n\nRange Proofs and Proof Speedups for ML-DSA (Portable) NTT",
          "timestamp": "2025-05-22T15:55:45Z",
          "url": "/commits/4d5f5b5cd3b4e259c9db06437fc70a63551ed92d"
        },
        "date": 1747930972701,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 104,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 310,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 123,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 75,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 116,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 40,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 168,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 585,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 198,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 137,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 198,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 93,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 374,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 841,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 275,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 231,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 266,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 98,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "4d5f5b5cd3b4e259c9db06437fc70a63551ed92d",
          "message": "Merge pull request #989 from cryspen/mldsa-portable-ntt\n\nRange Proofs and Proof Speedups for ML-DSA (Portable) NTT",
          "timestamp": "2025-05-22T15:55:45Z",
          "url": "/commits/4d5f5b5cd3b4e259c9db06437fc70a63551ed92d"
        },
        "date": 1747931000221,
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
            "value": 150,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 43,
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
            "value": 129,
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
            "value": 21,
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
            "value": 26,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 85,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 255,
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
            "value": 57,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 210,
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
            "value": 49,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 107,
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
            "value": 301,
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
            "value": 253,
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
            "value": 128,
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
            "name": "Lucas Franceschino",
            "username": "Lucas Franceschino"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "ab44219b95cc0b00dd1e2a7d568aaa5a72542a87",
          "message": "Merge pull request #988 from cryspen/mldsa-avx2-ntt-smt-pat-lucas\n\nML-DSA: Avx2 NTT: proofs",
          "timestamp": "2025-05-23T12:09:31Z",
          "url": "/commits/ab44219b95cc0b00dd1e2a7d568aaa5a72542a87"
        },
        "date": 1748002313151,
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
            "value": 157,
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
            "value": 129,
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
            "value": 21,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 73,
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
            "value": 244,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 78,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 64,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 247,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "neon"
          },
          {
            "value": 56,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "neon"
          },
          {
            "value": 50,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 111,
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
            "value": 110,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 301,
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
            "value": 71,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 257,
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
            "value": 128,
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
            "name": "Lucas Franceschino",
            "username": "Lucas Franceschino"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "ab44219b95cc0b00dd1e2a7d568aaa5a72542a87",
          "message": "Merge pull request #988 from cryspen/mldsa-avx2-ntt-smt-pat-lucas\n\nML-DSA: Avx2 NTT: proofs",
          "timestamp": "2025-05-23T12:09:31Z",
          "url": "/commits/ab44219b95cc0b00dd1e2a7d568aaa5a72542a87"
        },
        "date": 1748002353928,
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
            "value": 258,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 78,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 61,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 91,
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
            "value": 141,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 410,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 131,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 119,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 141,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 53,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 212,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 509,
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
            "value": 189,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 181,
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
            "name": "Lucas Franceschino",
            "username": "Lucas Franceschino"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "ab44219b95cc0b00dd1e2a7d568aaa5a72542a87",
          "message": "Merge pull request #988 from cryspen/mldsa-avx2-ntt-smt-pat-lucas\n\nML-DSA: Avx2 NTT: proofs",
          "timestamp": "2025-05-23T12:09:31Z",
          "url": "/commits/ab44219b95cc0b00dd1e2a7d568aaa5a72542a87"
        },
        "date": 1748002362322,
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
            "value": 328,
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
            "value": 539,
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
            "value": 122,
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
            "value": 642,
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
            "value": 242,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 178,
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
            "name": "Lucas Franceschino",
            "username": "Lucas Franceschino"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "ab44219b95cc0b00dd1e2a7d568aaa5a72542a87",
          "message": "Merge pull request #988 from cryspen/mldsa-avx2-ntt-smt-pat-lucas\n\nML-DSA: Avx2 NTT: proofs",
          "timestamp": "2025-05-23T12:09:31Z",
          "url": "/commits/ab44219b95cc0b00dd1e2a7d568aaa5a72542a87"
        },
        "date": 1748002490902,
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
            "value": 328,
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
            "value": 78,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 94,
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
            "value": 109,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 480,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 125,
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
            "value": 535,
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
            "value": 132,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 138,
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
            "value": 191,
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
            "value": 188,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 215,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 651,
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
            "value": 249,
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
            "value": 299,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 877,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 313,
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
            "name": "Lucas Franceschino",
            "username": "Lucas Franceschino"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "ab44219b95cc0b00dd1e2a7d568aaa5a72542a87",
          "message": "Merge pull request #988 from cryspen/mldsa-avx2-ntt-smt-pat-lucas\n\nML-DSA: Avx2 NTT: proofs",
          "timestamp": "2025-05-23T12:09:31Z",
          "url": "/commits/ab44219b95cc0b00dd1e2a7d568aaa5a72542a87"
        },
        "date": 1748002534181,
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
            "value": 572,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 218,
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
            "value": 816,
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
            "value": 398,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 922,
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
            "value": 478,
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
            "value": 631,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 1.2,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 619,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 779,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.66,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 800,
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
            "name": "Lucas Franceschino",
            "username": "Lucas Franceschino"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "a92ec170499c3bdd7505f4c650b3f4bae10f9dbc",
          "message": "Merge pull request #988 from cryspen/mldsa-avx2-ntt-smt-pat-lucas\n\nML-DSA: Avx2 NTT: proofs",
          "timestamp": "2025-05-23T12:17:12Z",
          "url": "/commits/a92ec170499c3bdd7505f4c650b3f4bae10f9dbc"
        },
        "date": 1748002840028,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 77,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 325,
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
            "value": 74,
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
            "value": 537,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 143,
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
            "value": 140,
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
            "value": 215,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 652,
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
            "value": 81,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 71,
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
          "id": "a92ec170499c3bdd7505f4c650b3f4bae10f9dbc",
          "message": "Merge pull request #988 from cryspen/mldsa-avx2-ntt-smt-pat-lucas\n\nML-DSA: Avx2 NTT: proofs",
          "timestamp": "2025-05-23T12:17:12Z",
          "url": "/commits/a92ec170499c3bdd7505f4c650b3f4bae10f9dbc"
        },
        "date": 1748003021855,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 208,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 574,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 218,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 262,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 822,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 288,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 397,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 935,
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
            "value": 478,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.31,
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
            "value": 629,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 1.21,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 619,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 779,
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
            "value": 801,
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
            "name": "Lucas Franceschino",
            "username": "Lucas Franceschino"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "a92ec170499c3bdd7505f4c650b3f4bae10f9dbc",
          "message": "Merge pull request #988 from cryspen/mldsa-avx2-ntt-smt-pat-lucas\n\nML-DSA: Avx2 NTT: proofs",
          "timestamp": "2025-05-23T12:17:12Z",
          "url": "/commits/a92ec170499c3bdd7505f4c650b3f4bae10f9dbc"
        },
        "date": 1748003035752,
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
            "value": 328,
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
            "value": 78,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 93,
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
            "value": 109,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 471,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 124,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 147,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 559,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 146,
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
            "value": 52,
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
            "value": 709,
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
            "value": 214,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 643,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 223,
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
            "value": 299,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 865,
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
            "name": "Lucas Franceschino",
            "username": "Lucas Franceschino"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "a92ec170499c3bdd7505f4c650b3f4bae10f9dbc",
          "message": "Merge pull request #988 from cryspen/mldsa-avx2-ntt-smt-pat-lucas\n\nML-DSA: Avx2 NTT: proofs",
          "timestamp": "2025-05-23T12:17:12Z",
          "url": "/commits/a92ec170499c3bdd7505f4c650b3f4bae10f9dbc"
        },
        "date": 1748003074511,
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
            "value": 577,
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
            "value": 227,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 716,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 244,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 395,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 917,
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
            "value": 417,
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
            "value": 402,
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
            "value": 667,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.47,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 676,
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
          "id": "a92ec170499c3bdd7505f4c650b3f4bae10f9dbc",
          "message": "Merge pull request #988 from cryspen/mldsa-avx2-ntt-smt-pat-lucas\n\nML-DSA: Avx2 NTT: proofs",
          "timestamp": "2025-05-23T12:17:12Z",
          "url": "/commits/a92ec170499c3bdd7505f4c650b3f4bae10f9dbc"
        },
        "date": 1748003572864,
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
            "value": 149,
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
            "value": 127,
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
            "value": 25,
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
            "value": 245,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 73,
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
            "value": 215,
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
            "value": 49,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 113,
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
            "value": 113,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 305,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 116,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 74,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 261,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "neon"
          },
          {
            "value": 79,
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
            "value": 127,
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
            "name": "Lucas Franceschino",
            "username": "Lucas Franceschino"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "a92ec170499c3bdd7505f4c650b3f4bae10f9dbc",
          "message": "Merge pull request #988 from cryspen/mldsa-avx2-ntt-smt-pat-lucas\n\nML-DSA: Avx2 NTT: proofs",
          "timestamp": "2025-05-23T12:17:12Z",
          "url": "/commits/a92ec170499c3bdd7505f4c650b3f4bae10f9dbc"
        },
        "date": 1748003649411,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 94,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 346,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 119,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 93,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 125,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 42,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 200,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 607,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 169,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 127,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 192,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 70,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 283,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 688,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 257,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 229,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 263,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 100,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "dcaee5ddffe11f8355e3a41ab8c962d889c4315d",
          "message": "Merge pull request #988 from cryspen/mldsa-avx2-ntt-smt-pat-lucas\n\nML-DSA: Avx2 NTT: proofs",
          "timestamp": "2025-05-23T14:01:25Z",
          "url": "/commits/dcaee5ddffe11f8355e3a41ab8c962d889c4315d"
        },
        "date": 1748009033060,
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
            "value": 153,
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
            "value": 28,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 127,
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
            "value": 21,
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
            "value": 84,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 250,
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
            "value": 58,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 207,
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
            "value": 48,
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
            "value": 38,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 119,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 308,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 130,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 78,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 283,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "neon"
          },
          {
            "value": 83,
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
            "value": 128,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "dcaee5ddffe11f8355e3a41ab8c962d889c4315d",
          "message": "Merge pull request #988 from cryspen/mldsa-avx2-ntt-smt-pat-lucas\n\nML-DSA: Avx2 NTT: proofs",
          "timestamp": "2025-05-23T14:01:25Z",
          "url": "/commits/dcaee5ddffe11f8355e3a41ab8c962d889c4315d"
        },
        "date": 1748009075588,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 77,
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
            "value": 86,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 74,
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
            "value": 79,
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
            "value": 122,
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
            "value": 650,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "dcaee5ddffe11f8355e3a41ab8c962d889c4315d",
          "message": "Merge pull request #988 from cryspen/mldsa-avx2-ntt-smt-pat-lucas\n\nML-DSA: Avx2 NTT: proofs",
          "timestamp": "2025-05-23T14:01:25Z",
          "url": "/commits/dcaee5ddffe11f8355e3a41ab8c962d889c4315d"
        },
        "date": 1748009085269,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 80,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 270,
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
            "value": 62,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 95,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 35,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 157,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 437,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 138,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 119,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 174,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 55,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 211,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 536,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 219,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 194,
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
            "value": 83,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "dcaee5ddffe11f8355e3a41ab8c962d889c4315d",
          "message": "Merge pull request #988 from cryspen/mldsa-avx2-ntt-smt-pat-lucas\n\nML-DSA: Avx2 NTT: proofs",
          "timestamp": "2025-05-23T14:01:25Z",
          "url": "/commits/dcaee5ddffe11f8355e3a41ab8c962d889c4315d"
        },
        "date": 1748009261325,
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
            "value": 572,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 218,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 263,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 812,
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
            "value": 397,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 920,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 380,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 479,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.34,
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
            "value": 631,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 1.21,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 620,
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
            "value": 1.68,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 799,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "dcaee5ddffe11f8355e3a41ab8c962d889c4315d",
          "message": "Merge pull request #988 from cryspen/mldsa-avx2-ntt-smt-pat-lucas\n\nML-DSA: Avx2 NTT: proofs",
          "timestamp": "2025-05-23T14:01:25Z",
          "url": "/commits/dcaee5ddffe11f8355e3a41ab8c962d889c4315d"
        },
        "date": 1748009298357,
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
            "value": 77,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 95,
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
            "value": 109,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 471,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 124,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 147,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 532,
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
            "value": 191,
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
            "value": 188,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 216,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 640,
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
            "value": 83,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 298,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 875,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "dcaee5ddffe11f8355e3a41ab8c962d889c4315d",
          "message": "Merge pull request #988 from cryspen/mldsa-avx2-ntt-smt-pat-lucas\n\nML-DSA: Avx2 NTT: proofs",
          "timestamp": "2025-05-23T14:01:25Z",
          "url": "/commits/dcaee5ddffe11f8355e3a41ab8c962d889c4315d"
        },
        "date": 1748009410354,
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
            "value": 592,
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
            "value": 230,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 716,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 246,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 394,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 916,
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
            "value": 415,
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
            "value": 403,
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
            "value": 1.17,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 613,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 673,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.49,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 677,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "1eadcf7b9f5ae08fd21dddf60cacbf4c8bb7a0d8",
          "message": "Merge pull request #987 from cryspen/lf-montgomery_multiply_aux\n\nml-dsa: avx2: intro. `montgomery_multiply_aux`",
          "timestamp": "2025-05-23T15:57:52Z",
          "url": "/commits/1eadcf7b9f5ae08fd21dddf60cacbf4c8bb7a0d8"
        },
        "date": 1748016059767,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 77,
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
            "value": 74,
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
            "value": 79,
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
            "value": 536,
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
            "value": 216,
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
            "value": 241,
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
            "value": 81,
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
            "value": 141,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "1eadcf7b9f5ae08fd21dddf60cacbf4c8bb7a0d8",
          "message": "Merge pull request #987 from cryspen/lf-montgomery_multiply_aux\n\nml-dsa: avx2: intro. `montgomery_multiply_aux`",
          "timestamp": "2025-05-23T15:57:52Z",
          "url": "/commits/1eadcf7b9f5ae08fd21dddf60cacbf4c8bb7a0d8"
        },
        "date": 1748016251615,
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
            "value": 578,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 218,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 262,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 814,
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
            "value": 938,
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
            "value": 479,
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
            "value": 630,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 1.2,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 620,
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
            "value": 1.69,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 799,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "1eadcf7b9f5ae08fd21dddf60cacbf4c8bb7a0d8",
          "message": "Merge pull request #987 from cryspen/lf-montgomery_multiply_aux\n\nml-dsa: avx2: intro. `montgomery_multiply_aux`",
          "timestamp": "2025-05-23T15:57:52Z",
          "url": "/commits/1eadcf7b9f5ae08fd21dddf60cacbf4c8bb7a0d8"
        },
        "date": 1748016247643,
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
            "value": 329,
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
            "value": 109,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 475,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 124,
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
            "value": 530,
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
            "value": 141,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 52,
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
            "value": 696,
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
            "value": 216,
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
            "value": 223,
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
            "value": 299,
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
            "value": 313,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "1eadcf7b9f5ae08fd21dddf60cacbf4c8bb7a0d8",
          "message": "Merge pull request #987 from cryspen/lf-montgomery_multiply_aux\n\nml-dsa: avx2: intro. `montgomery_multiply_aux`",
          "timestamp": "2025-05-23T15:57:52Z",
          "url": "/commits/1eadcf7b9f5ae08fd21dddf60cacbf4c8bb7a0d8"
        },
        "date": 1748016340455,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 209,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 579,
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
            "value": 227,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 721,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 244,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 397,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 914,
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
            "value": 420,
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
            "value": 402,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 626,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 1.17,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 614,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 669,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.48,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 677,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "1eadcf7b9f5ae08fd21dddf60cacbf4c8bb7a0d8",
          "message": "Merge pull request #987 from cryspen/lf-montgomery_multiply_aux\n\nml-dsa: avx2: intro. `montgomery_multiply_aux`",
          "timestamp": "2025-05-23T15:57:52Z",
          "url": "/commits/1eadcf7b9f5ae08fd21dddf60cacbf4c8bb7a0d8"
        },
        "date": 1748016643962,
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
            "value": 152,
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
            "value": 126,
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
            "value": 21,
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
            "value": 92,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 245,
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
            "value": 213,
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
            "value": 115,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 38,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 114,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 300,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 119,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 86,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 283,
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
            "value": 128,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 55,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "1eadcf7b9f5ae08fd21dddf60cacbf4c8bb7a0d8",
          "message": "Merge pull request #987 from cryspen/lf-montgomery_multiply_aux\n\nml-dsa: avx2: intro. `montgomery_multiply_aux`",
          "timestamp": "2025-05-23T15:57:52Z",
          "url": "/commits/1eadcf7b9f5ae08fd21dddf60cacbf4c8bb7a0d8"
        },
        "date": 1748016714793,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 80,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 309,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 90,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 81,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 118,
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
            "value": 168,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 446,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 144,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 131,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 195,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 65,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 240,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 580,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 276,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 257,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 253,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 91,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "11e69e5b09ff4b5a1fd0496ca82ca3c4b84922d1",
          "message": "Merge pull request #987 from cryspen/lf-montgomery_multiply_aux\n\nml-dsa: avx2: intro. `montgomery_multiply_aux`",
          "timestamp": "2025-05-24T07:23:17Z",
          "url": "/commits/11e69e5b09ff4b5a1fd0496ca82ca3c4b84922d1"
        },
        "date": 1748071535513,
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
            "value": 147,
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
            "value": 126,
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
            "value": 21,
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
            "value": 25,
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
            "value": 243,
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
            "value": 58,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 209,
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
            "value": 108,
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
            "value": 116,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 296,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 112,
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
            "value": 250,
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
            "value": 127,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 55,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "11e69e5b09ff4b5a1fd0496ca82ca3c4b84922d1",
          "message": "Merge pull request #987 from cryspen/lf-montgomery_multiply_aux\n\nml-dsa: avx2: intro. `montgomery_multiply_aux`",
          "timestamp": "2025-05-24T07:23:17Z",
          "url": "/commits/11e69e5b09ff4b5a1fd0496ca82ca3c4b84922d1"
        },
        "date": 1748071581896,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 77,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 335,
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
            "value": 74,
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
            "value": 32,
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
            "value": 536,
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
            "value": 216,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 642,
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
            "value": 81,
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
            "value": 142,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "11e69e5b09ff4b5a1fd0496ca82ca3c4b84922d1",
          "message": "Merge pull request #987 from cryspen/lf-montgomery_multiply_aux\n\nml-dsa: avx2: intro. `montgomery_multiply_aux`",
          "timestamp": "2025-05-24T07:23:17Z",
          "url": "/commits/11e69e5b09ff4b5a1fd0496ca82ca3c4b84922d1"
        },
        "date": 1748071651616,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 102,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 345,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 113,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 98,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 140,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 62,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 196,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 533,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 162,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 134,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 164,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 65,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 284,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 611,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 262,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 210,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 203,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 90,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "11e69e5b09ff4b5a1fd0496ca82ca3c4b84922d1",
          "message": "Merge pull request #987 from cryspen/lf-montgomery_multiply_aux\n\nml-dsa: avx2: intro. `montgomery_multiply_aux`",
          "timestamp": "2025-05-24T07:23:17Z",
          "url": "/commits/11e69e5b09ff4b5a1fd0496ca82ca3c4b84922d1"
        },
        "date": 1748071722487,
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
            "value": 324,
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
            "value": 81,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 95,
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
            "value": 109,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 476,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 124,
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
            "value": 528,
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
            "value": 140,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 52,
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
            "value": 715,
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
            "value": 215,
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
            "value": 223,
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
            "value": 85,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 299,
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
            "value": 313,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "11e69e5b09ff4b5a1fd0496ca82ca3c4b84922d1",
          "message": "Merge pull request #987 from cryspen/lf-montgomery_multiply_aux\n\nml-dsa: avx2: intro. `montgomery_multiply_aux`",
          "timestamp": "2025-05-24T07:23:17Z",
          "url": "/commits/11e69e5b09ff4b5a1fd0496ca82ca3c4b84922d1"
        },
        "date": 1748071780002,
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
            "value": 569,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 218,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 262,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 819,
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
            "value": 396,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 945,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 380,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 478,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.33,
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
            "value": 630,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 1.19,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 619,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 779,
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
            "value": 799,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "11e69e5b09ff4b5a1fd0496ca82ca3c4b84922d1",
          "message": "Merge pull request #987 from cryspen/lf-montgomery_multiply_aux\n\nml-dsa: avx2: intro. `montgomery_multiply_aux`",
          "timestamp": "2025-05-24T07:23:17Z",
          "url": "/commits/11e69e5b09ff4b5a1fd0496ca82ca3c4b84922d1"
        },
        "date": 1748071946455,
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
            "value": 573,
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
            "value": 227,
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
            "value": 244,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 395,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 927,
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
            "value": 416,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.13,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 402,
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
            "value": 1.17,
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
            "value": 668,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.48,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 676,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "b29301b57f1b30c487b87be6f2f001e1ecaaa8ea",
          "message": "Merge pull request #999 from cryspen/ml-dsa-generic-range-proofs\n\nRange Proofs for some ML-DSA modules",
          "timestamp": "2025-05-24T17:27:13Z",
          "url": "/commits/b29301b57f1b30c487b87be6f2f001e1ecaaa8ea"
        },
        "date": 1748107789202,
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
            "value": 155,
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
            "value": 34,
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
            "value": 75,
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
            "value": 85,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 255,
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
            "value": 60,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 222,
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
            "value": 50,
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
            "value": 38,
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
            "value": 315,
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
            "value": 80,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 272,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "neon"
          },
          {
            "value": 85,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "neon"
          },
          {
            "value": 60,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 140,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "b29301b57f1b30c487b87be6f2f001e1ecaaa8ea",
          "message": "Merge pull request #999 from cryspen/ml-dsa-generic-range-proofs\n\nRange Proofs for some ML-DSA modules",
          "timestamp": "2025-05-24T17:27:13Z",
          "url": "/commits/b29301b57f1b30c487b87be6f2f001e1ecaaa8ea"
        },
        "date": 1748107816224,
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
            "value": 74,
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
            "value": 536,
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
            "value": 122,
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
            "value": 241,
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
            "value": 81,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 69,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 142,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 73,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "b29301b57f1b30c487b87be6f2f001e1ecaaa8ea",
          "message": "Merge pull request #999 from cryspen/ml-dsa-generic-range-proofs\n\nRange Proofs for some ML-DSA modules",
          "timestamp": "2025-05-24T17:27:13Z",
          "url": "/commits/b29301b57f1b30c487b87be6f2f001e1ecaaa8ea"
        },
        "date": 1748107818300,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 71,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 256,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 78,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 61,
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
            "value": 138,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 408,
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
            "value": 108,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 136,
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
            "value": 210,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 502,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 204,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 186,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 180,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "b29301b57f1b30c487b87be6f2f001e1ecaaa8ea",
          "message": "Merge pull request #999 from cryspen/ml-dsa-generic-range-proofs\n\nRange Proofs for some ML-DSA modules",
          "timestamp": "2025-05-24T17:27:13Z",
          "url": "/commits/b29301b57f1b30c487b87be6f2f001e1ecaaa8ea"
        },
        "date": 1748108005662,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 208,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 564,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 218,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 266,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 822,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 290,
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
            "value": 957,
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
            "value": 482,
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
            "value": 630,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 1.2,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 619,
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
            "value": 1.68,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "b29301b57f1b30c487b87be6f2f001e1ecaaa8ea",
          "message": "Merge pull request #999 from cryspen/ml-dsa-generic-range-proofs\n\nRange Proofs for some ML-DSA modules",
          "timestamp": "2025-05-24T17:27:13Z",
          "url": "/commits/b29301b57f1b30c487b87be6f2f001e1ecaaa8ea"
        },
        "date": 1748108037854,
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
            "value": 329,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 83,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 78,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 93,
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
            "value": 109,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 479,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 123,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 146,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 531,
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
            "value": 131,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 138,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 52,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 197,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 763,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 196,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 215,
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
            "value": 222,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 236,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 181,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 87,
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
            "value": 880,
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
            "name": "karthikbhargavan",
            "username": "karthikbhargavan"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "b29301b57f1b30c487b87be6f2f001e1ecaaa8ea",
          "message": "Merge pull request #999 from cryspen/ml-dsa-generic-range-proofs\n\nRange Proofs for some ML-DSA modules",
          "timestamp": "2025-05-24T17:27:13Z",
          "url": "/commits/b29301b57f1b30c487b87be6f2f001e1ecaaa8ea"
        },
        "date": 1748108087499,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 209,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 579,
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
            "value": 224,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 699,
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
            "value": 395,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 919,
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
            "value": 392,
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
            "value": 673,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.45,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 681,
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
          "id": "ee5cbcd95b10b6b994d2d9e0437caf313a91b01d",
          "message": "Merge pull request #981 from Parrot7483/hash-tests\n\nAdd tests for hash functions",
          "timestamp": "2025-05-25T10:23:00Z",
          "url": "/commits/ee5cbcd95b10b6b994d2d9e0437caf313a91b01d"
        },
        "date": 1748168720735,
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
            "value": 148,
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
            "value": 127,
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
            "value": 21,
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
            "value": 83,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 242,
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
            "value": 58,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 210,
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
            "value": 110,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 301,
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
            "value": 73,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 253,
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
          "id": "ee5cbcd95b10b6b994d2d9e0437caf313a91b01d",
          "message": "Merge pull request #981 from Parrot7483/hash-tests\n\nAdd tests for hash functions",
          "timestamp": "2025-05-25T10:23:00Z",
          "url": "/commits/ee5cbcd95b10b6b994d2d9e0437caf313a91b01d"
        },
        "date": 1748168768284,
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
            "value": 322,
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
            "value": 74,
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
            "value": 138,
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
            "value": 55,
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
            "value": 216,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 638,
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
            "value": 241,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 178,
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
            "value": 143,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 73,
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
          "id": "ee5cbcd95b10b6b994d2d9e0437caf313a91b01d",
          "message": "Merge pull request #981 from Parrot7483/hash-tests\n\nAdd tests for hash functions",
          "timestamp": "2025-05-25T10:23:00Z",
          "url": "/commits/ee5cbcd95b10b6b994d2d9e0437caf313a91b01d"
        },
        "date": 1748168799789,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 81,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 297,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 95,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 70,
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
            "value": 38,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 166,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 488,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 152,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 131,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 172,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 60,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 237,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 587,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 245,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 223,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 212,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 87,
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
          "id": "ee5cbcd95b10b6b994d2d9e0437caf313a91b01d",
          "message": "Merge pull request #981 from Parrot7483/hash-tests\n\nAdd tests for hash functions",
          "timestamp": "2025-05-25T10:23:00Z",
          "url": "/commits/ee5cbcd95b10b6b994d2d9e0437caf313a91b01d"
        },
        "date": 1748168953581,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 208,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 572,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 218,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 262,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 823,
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
            "value": 399,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 958,
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
            "value": 479,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.31,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 474,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 630,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 1.2,
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
            "value": 1.66,
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
          "id": "ee5cbcd95b10b6b994d2d9e0437caf313a91b01d",
          "message": "Merge pull request #981 from Parrot7483/hash-tests\n\nAdd tests for hash functions",
          "timestamp": "2025-05-25T10:23:00Z",
          "url": "/commits/ee5cbcd95b10b6b994d2d9e0437caf313a91b01d"
        },
        "date": 1748168972070,
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
            "value": 330,
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
            "value": 80,
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
            "value": 36,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 109,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 478,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 124,
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
            "value": 523,
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
            "value": 137,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 52,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 198,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 767,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 196,
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
            "value": 644,
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
            "value": 264,
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
            "value": 84,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 299,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 884,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 313,
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
          "id": "ee5cbcd95b10b6b994d2d9e0437caf313a91b01d",
          "message": "Merge pull request #981 from Parrot7483/hash-tests\n\nAdd tests for hash functions",
          "timestamp": "2025-05-25T10:23:00Z",
          "url": "/commits/ee5cbcd95b10b6b994d2d9e0437caf313a91b01d"
        },
        "date": 1748169078148,
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
            "value": 573,
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
            "value": 227,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 704,
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
            "value": 394,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 922,
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
            "value": 403,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.11,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 390,
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
            "value": 1.2,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 613,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 673,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.45,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 681,
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
            "name": "Jan Winkelmann",
            "username": "Jan Winkelmann"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "a19524b01812e3806e628f472ac7eb91514aebb5",
          "message": "Merge pull request #1001 from cryspen/keks/sha2-readme-path\n\nReference the correct Readme in Cargo.toml files",
          "timestamp": "2025-05-26T10:13:07Z",
          "url": "/commits/a19524b01812e3806e628f472ac7eb91514aebb5"
        },
        "date": 1748254583172,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 77,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 330,
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
            "value": 74,
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
            "value": 138,
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
            "value": 122,
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
            "name": "Jan Winkelmann",
            "username": "Jan Winkelmann"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "112ad388ca07f56665e0b8cbfbe6ac851a9a9eaa",
          "message": "Merge pull request #995 from cryspen/keks/testutils-expose-tracing-macro\n\nReexport tracing macro in test-utils crate",
          "timestamp": "2025-05-26T10:13:11Z",
          "url": "/commits/112ad388ca07f56665e0b8cbfbe6ac851a9a9eaa"
        },
        "date": 1748254593156,
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
            "value": 74,
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
            "value": 531,
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
            "value": 216,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 643,
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
            "value": 247,
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
            "value": 81,
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
            "value": 142,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 73,
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
            "name": "Jan Winkelmann",
            "username": "Jan Winkelmann"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "112ad388ca07f56665e0b8cbfbe6ac851a9a9eaa",
          "message": "Merge pull request #995 from cryspen/keks/testutils-expose-tracing-macro\n\nReexport tracing macro in test-utils crate",
          "timestamp": "2025-05-26T10:13:11Z",
          "url": "/commits/112ad388ca07f56665e0b8cbfbe6ac851a9a9eaa"
        },
        "date": 1748254728612,
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
            "value": 324,
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
            "value": 78,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 95,
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
            "value": 109,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 478,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 124,
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
            "value": 536,
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
            "value": 132,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 137,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 67,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 197,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 762,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 196,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 215,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 644,
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
            "value": 262,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 185,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 86,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 299,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 868,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 313,
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
            "name": "Jan Winkelmann",
            "username": "Jan Winkelmann"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "112ad388ca07f56665e0b8cbfbe6ac851a9a9eaa",
          "message": "Merge pull request #995 from cryspen/keks/testutils-expose-tracing-macro\n\nReexport tracing macro in test-utils crate",
          "timestamp": "2025-05-26T10:13:11Z",
          "url": "/commits/112ad388ca07f56665e0b8cbfbe6ac851a9a9eaa"
        },
        "date": 1748254771300,
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
            "value": 573,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 218,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 262,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 825,
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
            "value": 964,
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
            "value": 477,
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
            "value": 474,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 632,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 1.19,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 618,
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
            "name": "Jan Winkelmann",
            "username": "Jan Winkelmann"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "a19524b01812e3806e628f472ac7eb91514aebb5",
          "message": "Merge pull request #1001 from cryspen/keks/sha2-readme-path\n\nReference the correct Readme in Cargo.toml files",
          "timestamp": "2025-05-26T10:13:07Z",
          "url": "/commits/a19524b01812e3806e628f472ac7eb91514aebb5"
        },
        "date": 1748254772235,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 208,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 572,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 218,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 262,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 819,
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
            "value": 396,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 978,
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
            "value": 477,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.31,
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
            "value": 631,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 1.19,
            "unit": "ms/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 619,
            "unit": "μs/iter",
            "os": "ubuntu-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 782,
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
            "name": "Jan Winkelmann",
            "username": "Jan Winkelmann"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "a19524b01812e3806e628f472ac7eb91514aebb5",
          "message": "Merge pull request #1001 from cryspen/keks/sha2-readme-path\n\nReference the correct Readme in Cargo.toml files",
          "timestamp": "2025-05-26T10:13:07Z",
          "url": "/commits/a19524b01812e3806e628f472ac7eb91514aebb5"
        },
        "date": 1748254793254,
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
            "value": 321,
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
            "value": 109,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 476,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 124,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 147,
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
            "value": 138,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 52,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 197,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 766,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 196,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 216,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 640,
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
            "value": 299,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 875,
            "unit": "μs/iter",
            "os": "windows-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 313,
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
            "name": "Jan Winkelmann",
            "username": "Jan Winkelmann"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "112ad388ca07f56665e0b8cbfbe6ac851a9a9eaa",
          "message": "Merge pull request #995 from cryspen/keks/testutils-expose-tracing-macro\n\nReexport tracing macro in test-utils crate",
          "timestamp": "2025-05-26T10:13:11Z",
          "url": "/commits/112ad388ca07f56665e0b8cbfbe6ac851a9a9eaa"
        },
        "date": 1748254918917,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 209,
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
            "value": 224,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 708,
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
            "value": 393,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 917,
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
            "value": 403,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.11,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 391,
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
            "value": 1.17,
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
            "value": 673,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.47,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 682,
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
            "name": "Jan Winkelmann",
            "username": "Jan Winkelmann"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "a19524b01812e3806e628f472ac7eb91514aebb5",
          "message": "Merge pull request #1001 from cryspen/keks/sha2-readme-path\n\nReference the correct Readme in Cargo.toml files",
          "timestamp": "2025-05-26T10:13:07Z",
          "url": "/commits/a19524b01812e3806e628f472ac7eb91514aebb5"
        },
        "date": 1748254969502,
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
            "value": 573,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 218,
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
            "value": 703,
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
            "value": 394,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 922,
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
            "value": 391,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 627,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 1.18,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 613,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 673,
            "unit": "μs/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 1.47,
            "unit": "ms/iter",
            "os": "windows-latest_32",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 682,
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
            "name": "Jan Winkelmann",
            "username": "Jan Winkelmann"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "112ad388ca07f56665e0b8cbfbe6ac851a9a9eaa",
          "message": "Merge pull request #995 from cryspen/keks/testutils-expose-tracing-macro\n\nReexport tracing macro in test-utils crate",
          "timestamp": "2025-05-26T10:13:11Z",
          "url": "/commits/112ad388ca07f56665e0b8cbfbe6ac851a9a9eaa"
        },
        "date": 1748255264228,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 96,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 349,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 104,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 80,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 113,
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
            "value": 171,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 572,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 165,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 133,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 179,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 64,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 263,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 646,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 267,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 258,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 240,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 101,
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
            "name": "Jan Winkelmann",
            "username": "Jan Winkelmann"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "112ad388ca07f56665e0b8cbfbe6ac851a9a9eaa",
          "message": "Merge pull request #995 from cryspen/keks/testutils-expose-tracing-macro\n\nReexport tracing macro in test-utils crate",
          "timestamp": "2025-05-26T10:13:11Z",
          "url": "/commits/112ad388ca07f56665e0b8cbfbe6ac851a9a9eaa"
        },
        "date": 1748255297704,
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
            "value": 152,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 43,
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
            "value": 132,
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
            "value": 74,
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
            "value": 86,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 253,
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
            "value": 57,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 207,
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
            "value": 300,
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
            "value": 71,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 253,
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
            "value": 55,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 128,
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
            "name": "Jan Winkelmann",
            "username": "Jan Winkelmann"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "a19524b01812e3806e628f472ac7eb91514aebb5",
          "message": "Merge pull request #1001 from cryspen/keks/sha2-readme-path\n\nReference the correct Readme in Cargo.toml files",
          "timestamp": "2025-05-26T10:13:07Z",
          "url": "/commits/a19524b01812e3806e628f472ac7eb91514aebb5"
        },
        "date": 1748255418924,
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
            "value": 155,
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
            "value": 126,
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
            "value": 21,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 73,
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
            "value": 80,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 253,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 76,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 58,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 215,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "neon"
          },
          {
            "value": 52,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "neon"
          },
          {
            "value": 50,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 114,
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
            "value": 114,
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
            "value": 116,
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
            "value": 253,
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
            "value": 54,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 128,
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
            "name": "Jan Winkelmann",
            "username": "Jan Winkelmann"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "a19524b01812e3806e628f472ac7eb91514aebb5",
          "message": "Merge pull request #1001 from cryspen/keks/sha2-readme-path\n\nReference the correct Readme in Cargo.toml files",
          "timestamp": "2025-05-26T10:13:07Z",
          "url": "/commits/a19524b01812e3806e628f472ac7eb91514aebb5"
        },
        "date": 1748255519609,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 80,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 323,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 111,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 70,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 119,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 39,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 157,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 514,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 164,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 132,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 174,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 61,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 235,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 589,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 253,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 234,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 206,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 87,
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
            "name": "Jan Winkelmann",
            "username": "Jan Winkelmann"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "59a10ba5649a5bb890ef8225d671608b94912cbf",
          "message": "Merge pull request #1002 from cryspen/keks/more-release-prep-0.0.3\n\nfix Readme references in more Cargo.tomls",
          "timestamp": "2025-05-26T14:00:54Z",
          "url": "/commits/59a10ba5649a5bb890ef8225d671608b94912cbf"
        },
        "date": 1748268196039,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 43,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 166,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 43,
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
            "value": 132,
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
            "value": 21,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "auto"
          },
          {
            "value": 73,
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
            "value": 80,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 245,
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
            "value": 207,
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
            "value": 37,
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
            "value": 303,
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
            "value": 71,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "neon"
          },
          {
            "value": 257,
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
            "value": 128,
            "unit": "μs/iter",
            "os": "macos-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "auto"
          },
          {
            "value": 55,
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
            "name": "Jan Winkelmann",
            "username": "Jan Winkelmann"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "59a10ba5649a5bb890ef8225d671608b94912cbf",
          "message": "Merge pull request #1002 from cryspen/keks/more-release-prep-0.0.3\n\nfix Readme references in more Cargo.tomls",
          "timestamp": "2025-05-26T14:00:54Z",
          "url": "/commits/59a10ba5649a5bb890ef8225d671608b94912cbf"
        },
        "date": 1748268240812,
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
            "value": 260,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 78,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 61,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 89,
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
            "value": 142,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 417,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 132,
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
            "value": 142,
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
            "value": 208,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 513,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "portable"
          },
          {
            "value": 207,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 191,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 184,
            "unit": "μs/iter",
            "os": "macos-13_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 79,
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
            "name": "Jan Winkelmann",
            "username": "Jan Winkelmann"
          },
          "committer": {
            "name": "GitHub",
            "username": "GitHub"
          },
          "id": "59a10ba5649a5bb890ef8225d671608b94912cbf",
          "message": "Merge pull request #1002 from cryspen/keks/more-release-prep-0.0.3\n\nfix Readme references in more Cargo.tomls",
          "timestamp": "2025-05-26T14:00:54Z",
          "url": "/commits/59a10ba5649a5bb890ef8225d671608b94912cbf"
        },
        "date": 1748268252120,
        "bigger_is_better": false,
        "benches": [
          {
            "value": 77,
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
            "value": 87,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "portable"
          },
          {
            "value": 74,
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
            "value": 33,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "pqclean ML-DSA",
            "keySize": "44",
            "label": "Verify",
            "hardware": "auto"
          },
          {
            "value": 151,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "65",
            "label": "KeyGen",
            "hardware": "portable"
          },
          {
            "value": 534,
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
            "value": 122,
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
            "value": 638,
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
            "value": 243,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "KeyGen",
            "hardware": "avx2"
          },
          {
            "value": 178,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Sign",
            "hardware": "avx2"
          },
          {
            "value": 81,
            "unit": "μs/iter",
            "os": "ubuntu-latest_64",
            "implementation": "libcrux ML-DSA",
            "keySize": "87",
            "label": "Verify",
            "hardware": "avx2"
          },
          {
            "value": 71,
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