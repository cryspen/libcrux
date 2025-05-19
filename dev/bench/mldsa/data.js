window.BENCHMARK_DATA = {
  "lastUpdate": 1747665536365,
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