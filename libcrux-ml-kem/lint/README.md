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
