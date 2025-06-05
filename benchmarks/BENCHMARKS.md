# Benchmarks

# x25519

|        | DH        | S2P       |
| ------ | --------- | --------- |
| M1 Pro | 31.196 µs | 31.298 µs |

## Other implementations

| M1 Pro          | DH        | S2P       |
| --------------- | --------- | --------- |
| Ring            | 29.897 µs | 11.237 µs |
| OpenSSL         | 30.904 µs | 31.226 µs |
| Dalek           | 36.378 µs | 11.923 µs |
| Dalek Ristretto | 30.752 µs | 10.144 µs |

# Ed25519

|        | Sign      | Verify    |
| ------ | --------- | --------- |
| M1 Pro | 46.183 µs | 48.268 µs |

## Other implementations


| M1 Pro  | Sign      | Verify    |
| ------- | --------- | --------- |
| Ring    | 11.698 µs | 37.573 µs |
| OpenSSL | 31.304 µs | 85.937 µs |
| Dalek   | 12.972 µs | 32.988 µs |

# Chacha20Poly1305

10MB

|        | Encrypt   | Decrypt   |
| ------ | --------- | --------- |
| M1 Pro | 24.492 ms | 25.299 ms |

## Other implementations

| M1 Pro          | Encrypt   | Decrypt   |
| --------------- | --------- | --------- |
| Ring            | 6.6243 ms | 8.8118 ms |
| OpenSSL         | 7.0036 ms | 7.1077 ms |
| Rust Crypto Org | 32.171 ms | 35.792 ms |

# SHA2-256

|        | 100B      | 1KB       | 2KB       | 4KB       | 8KB       |
| ------ | --------- | --------- | --------- | --------- | --------- |
| M1 Pro | 411.17 ns | 3.2339 µs | 6.2949 µs | 12.497 µs | 24.459 µs |

## Other implementations

| M1 Pro          | 100B      | 1KB       | 2KB       | 4KB       | 8KB       |
| --------------- | --------- | --------- | --------- | --------- | --------- |
| Ring            | 80.446 ns | 467.13 ns | 883.78 ns | 1.7287 µs | 3.4154 µs |
| OpenSSL         | 342.57 ns | 711.44 ns | 1.1485 µs | 1.9812 µs | 3.6302 µs |
| Rust Crypto Org | 406.58 ns | 3.1644 µs | 6.0994 µs | 12.107 µs | 23.604 µs |

