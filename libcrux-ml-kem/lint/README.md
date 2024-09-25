# Linting for PQC

Lining pqc public keys.

## Lints

| Lint                      | Name       | Implementation                               |
| ------------------------- | ---------- | -------------------------------------------- |
| Empty parameters          | ML_KEM_001 | only in certs                                |
| Key usage                 | ML_KEM_002 | only in certs                                |
| Correct aid encoding      | ML_KEM_003 | only in certs                                |
| Correct ek length         | ML_KEM_004 | Enforced by API                              |
| Correct seed length       | ML_KEM_005 | Enforced by API (as part of ML_KEM_004)      |
| Correct matrix dimensions | ML_KEM_006 | Implied                                      |
| Valid public key space    | ML_KEM_007 | Checked by `validate_public_key` or `decode` |
| Correct vector            | ML_KEM_008 | Implied                                      |
| Correct matrix entries    | ML_KEM_009 | Implied                                      |
| Correct matrix entries    | ML_KEM_010 | Implied                                      |
| Pk seed non-zero          | ML_KEM_011 | Checked by `validate_public_key` or `decode` |

| Lint                     | ID              | Name                               | S?  | Implementation                      | Description                                                                                                                                  |
| ------------------------ | --------------- | ---------------------------------- | --- | ----------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------- |
| Correct key usage        | ML_KEM_INTER_01 | e_ml_kem_key_usage                 |     | In Java                             | A certificate with an ML-KEM public key must only have the keyEncipherment key usage value.                                                  |
| Correct aid encoding     | ML_KEM_INTER_02 | e_ml_kem_public_key_aid_encoding   |     | In Java                             | The algorithm identifier in the public key of a certificate with an ML-KEM public key must have the correct encoding.                        |
|                          | ML_KEM_DIM_01   | e_ml_kem_ek_length                 |     | Rust `dim_01.json`                  | An encoded ML-KEM encapsulation key must be of the correct length.                                                                           |
|                          | ML_KEM_DIM_02   | e_ml_kem_ek_seed_length            | Y   |                                     | The seed contained in the ML-KEM encapsulation key must be of the correct length.                                                            |
|                          | ML_KEM_DIM_03   | e_ml_kem_ek_matrix_dimension       | Y   |                                     | The matrix expanded from the seed, that is contained in the MLKEM encapsulation key, must have the correct dimensions.                       |
|                          | ML_KEM_DIM_04   | e_ml_kem_ek_vector_dimension       | Y   |                                     | The vector contained in the extracted ML-KEM encapsulation key, must have the correct dimension.                                             |
|                          | ML_KEM_DOM_01   | e_ml_kem_ek_matrix_entries         | Y   |                                     | The matrix expanded from the seed, that is contained in the ML-KEM encapsulation key, must have entries from the correct space.              |
|                          | ML_KEM_DOM_02   | e_ml_kem_ek_vector_entries         | Y   |                                     | The vector contained in the extracted ML-KEM encapsulation key, must have entries from the correct space.                                    |
|                          | ML_KEM_DIS_01   | e_ml_kem_ek_seed_entry_frequency   |     | Rust `dis_01.json`                  | The seed contained in the ML-KEM encapsulation key must not have too many occurrences of the same element.                                   |
|                          | ML_KEM_DIS_02   | e_ml_kem_ek_seed_entry_run         |     | Rust `dis_02.json`                  | The seed contained in the ML-KEM encapsulation key must not have a too long run of the same element.                                         |
|                          | ML_KEM_DIS_03   | e_ml_kem_ek_seed_sl_entries        |     | Rust `dis_03.json`, `dis_03_2.json` | The seed contained in the ML-KEM encapsulation key must not have too small or too large entries.                                             |
|                          | ML_KEM_DIS_04   | e_ml_kem_ek_matrix_entry_frequency |     | Rust                                | The matrix expanded from the seed, that is contained in the ML-KEM encapsulation key must not have too many occurrences of the same element. |
|                          | ML_KEM_DIS_05   | e_ml_kem_ek_matrix_entry_run       |     | Rust                                | The matrix expanded from the seed, that is contained in the ML-KEM encapsulation key must not have a too long run of the same element.       |
|                          | ML_KEM_DIS_06   | e_ml_kem_ek_matrix_sl_entries      |     | Rust                                | The matrix expanded from the seed, that is contained in the ML-KEM encapsulation key must not have too small or too large entries.           |
|                          | ML_KEM_DIS_07   | e_ml_kem_ek_vector_distribution    |     |                                     | Given a large number of public keys, the vectors contained in the extracted ML-KEM public keys must follow a centered binomial distribution. |
| Known encoded public key | ML_KEM_GEN_01   | e_known_encoded_key                |     | In Java                             | A public key whose corresponding private key is known to be compromised, is weak, or is leaked must not be placed in a certificate.          |
|                          | ML_KEM_GEN_02   | e_ml_kem_ek_encoding               |     |                                     | An ML-KEM encryption key must be correctly encoded.                                                                                          |

## Usage

Make sure you have Rust installed [getting started](https://www.rust-lang.org/learn/get-started).

In `libcrux-ml-kem` run

```bash
cargo run --example cli -- --help
```

to get help.
This should print the following.

```
Usage: cli [OPTIONS] <COMMAND>

Commands:
  generate-key
  encaps
  decaps
  lint
  help          Print this message or the help of the given subcommand(s)

Options:
  -a, --algorithm <ALGORITHM>
          The key length, 512, 768, or 1024

          Defaults to 768

  -h, --help
          Print help (see a summary with '-h')
```

For the `lint` subcommand, the usage is as follows

```bash
cargo run --example cli -- lint --help
```

```
Usage: cli lint [OPTIONS]

Options:
  -f, --file <FILE>
          Optionally, a file name to store/read the lint. Defaults to `lint.json`.

          The lint will be store into/read from `$file.json` when this is used.

  -n, --name <NAME>
          Generate a lint with the given name

  -i, --invalid <INVALID>
          A raw, invalid, hex public key

  -r, --result <RESULT>
          Optionally, a file name to store the lint result. Defaults to `lint_result.json`

  -h, --help
          Print help (see a summary with '-h')
```
