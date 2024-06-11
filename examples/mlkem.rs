use std::{
    fs::File,
    io::{Read, Write},
};

use base64::prelude::*;
use libcrux::{
    drbg::Drbg,
    kem::{self, PublicKey},
};

use clap::{Parser, Subcommand};
use serde::{Deserialize, Serialize};

#[allow(non_snake_case)]
#[derive(Serialize, Deserialize)]
struct Lint {
    lintName: String,
    algorithm: String,
    valid: bool,
    r#type: String,
    id: String,
    publicKey: String,
}

#[allow(non_snake_case)]
#[derive(Serialize, Deserialize)]
struct LintResult {
    lintName: String,
    id: String,
    result: String,
}

enum LintType {
    PublicKey,
}

fn kem_algorithm(algorithm: &str) -> kem::Algorithm {
    match algorithm {
        "MlKem512" => kem::Algorithm::MlKem512,
        "MlKem768" => kem::Algorithm::MlKem768,
        "MlKem1024" => kem::Algorithm::MlKem1024,
        _ => panic!("Unsupported kem algorithm {algorithm}"),
    }
}

fn kem_algorithm_str(algorithm: &kem::Algorithm) -> String {
    match algorithm {
        kem::Algorithm::MlKem512 => "MlKem512".to_owned(),
        kem::Algorithm::MlKem768 => "MlKem768".to_owned(),
        kem::Algorithm::MlKem1024 => "MlKem1024".to_owned(),
        _ => panic!("Unsupported kem algorithm {algorithm:?}"),
    }
}

impl Lint {
    // XXX: Only kem for now. Needs updating for ml-dsa
    fn new(
        id: String,
        lint_type: LintType,
        pk: &[u8],
        name: &str,
        algorithm: kem::Algorithm,
        valid: bool,
    ) -> Self {
        Self {
            lintName: name.to_owned(),
            r#type: match lint_type {
                LintType::PublicKey => "PublicKey".to_owned(),
            },
            id,
            publicKey: BASE64_STANDARD.encode(pk),
            algorithm: kem_algorithm_str(&algorithm),
            valid,
        }
    }

    fn input_type(&self) -> Option<LintType> {
        match self.publicKey.as_str() {
            "PublicKey" => Some(LintType::PublicKey),
            _ => None,
        }
    }

    fn id(&self) -> &str {
        &self.id
    }

    fn kem_algorithm(&self) -> kem::Algorithm {
        kem_algorithm(&self.algorithm)
    }

    fn public_key(&self) -> Option<Vec<u8>> {
        BASE64_STANDARD.decode(&self.publicKey).ok()
    }
}

#[derive(Subcommand)]
enum GenerateCli {
    GenerateKey {
        /// Optionally, a file name to store the keys into.
        ///
        /// The keys will be store into `$out.pub` and `$out.priv` when this is used.
        #[arg(short, long)]
        out: Option<String>,
    },
    Encaps {
        /// Public key input file to encrypt to.
        #[arg(short, long)]
        key: String,

        /// Optionally, a file name to store the encapsulation output.
        ///
        /// This defaults to `mlkem.ct`.
        #[arg(short, long)]
        ct: Option<String>,

        /// Optionally, a file name to store the shared secret output.
        ///
        /// This defaults to `mlkem-encapsulated.ss`.
        #[arg(short, long)]
        ss: Option<String>,
    },
    Decaps {
        /// Private key input file to decapsulate with.
        #[arg(short, long)]
        key: String,

        /// Encapsulated secret.
        #[arg(short, long)]
        ct: String,

        /// Optionally, a file name to store the shared secret.
        ///
        /// This defaults to `mlkem-decapsulated.ss``.
        #[arg(short, long)]
        ss: Option<String>,
    },
    Lint {
        /// Optionally, a file name to store/read the lint.
        /// Defaults to `lint.json`.
        ///
        /// The lint will be store into/read from `$file.json` when this is used.
        #[arg(short, long)]
        file: Option<String>,

        /// Generate a lint with the given name.
        #[arg(short, long)]
        name: Option<String>,

        /// A raw, invalid, hex public key.
        #[arg(short, long)]
        invalid: Option<String>,

        /// Optionally, a file name to store the lint result.
        /// Defaults to `lint_result.json`.
        #[arg(short, long)]
        result: Option<String>,
    },
}

#[derive(Parser)]
struct Cli {
    /// Generate a key pair and write it out.
    ///
    /// When no output files are given, `mlkem.pub` and `mlkem` are used.
    #[command(subcommand)]
    cmd: GenerateCli,

    /// The key length, 512, 768, or 1024
    ///
    /// Defaults to 768
    #[arg(short, long)]
    algorithm: Option<u16>,
}

fn main() {
    pretty_env_logger::init();

    let cli = Cli::parse();

    let alg = if let Some(l) = cli.algorithm {
        match l {
            512 => kem::Algorithm::MlKem512,
            768 => kem::Algorithm::MlKem768,
            1024 => kem::Algorithm::MlKem1024,
            _ => {
                eprintln!("Invalid algorithm variant {l}");
                return;
            }
        }
    } else {
        kem::Algorithm::MlKem768
    };

    let mut rng = Drbg::new(libcrux::digest::Algorithm::Sha256).unwrap();

    match cli.cmd {
        GenerateCli::GenerateKey { out: file } => {
            // Generate a key pair and write it out.
            let (sk_name, pk_name) = match file {
                Some(n) => (format!("{n}.priv"), format!("{n}.pub")),
                None => ("mlkem.priv".to_owned(), "mlkem.pub".to_owned()),
            };

            let (secret_key, public_key) = kem::key_gen(alg, &mut rng).unwrap();

            println!("Writing private key to {sk_name}");
            File::create(sk_name.clone())
                .expect(&format!("Can not create file {sk_name}"))
                .write_all(&secret_key.encode())
                .expect("Error writing private key");
            println!("Writing public key to {pk_name}");
            File::create(pk_name.clone())
                .expect(&format!("Can not create file {pk_name}"))
                .write_all(&public_key.encode())
                .expect("Error writing public key");
        }

        GenerateCli::Encaps { key, ct: out, ss } => {
            let pk = bytes_from_file(key);
            let pk = kem::PublicKey::decode(alg, &pk).expect("Error decoding public key");

            let (shared_secret, ciphertext) =
                pk.encapsulate(&mut rng).expect("Error encapsulating");

            let ct_out = match out {
                Some(n) => n,
                None => "mlkem.ct".to_owned(),
            };
            let ss_out = match ss {
                Some(n) => n,
                None => "mlkem-encapsulated.ss".to_owned(),
            };

            println!("Writing ciphertext to {ct_out}");
            let mut out_file =
                File::create(ct_out.clone()).expect(&format!("Can not create file {ct_out}"));
            out_file
                .write_all(&ciphertext.encode())
                .expect("Error writing public key");

            println!("Writing shared secret to {ss_out}");
            let mut out_file =
                File::create(ss_out.clone()).expect(&format!("Can not create file {ss_out}"));
            out_file
                .write_all(&shared_secret.encode())
                .expect("Error writing public key");
        }
        GenerateCli::Decaps { key, ss: out, ct } => {
            let sk = bytes_from_file(key);
            let sk = kem::PrivateKey::decode(alg, &sk).expect("Error decoding private key");

            let ct = bytes_from_file(ct);

            let ct = kem::Ct::decode(alg, &ct).expect("Error decoding ct.");
            let shared_secret = ct.decapsulate(&sk).expect("Error decapsulating.");

            let out = match out {
                Some(n) => n,
                None => "mlkem-decapsulated.ss".to_owned(),
            };

            println!("Writing shared secret to {out}");
            let mut out_file =
                File::create(out.clone()).expect(&format!("Can not create file {out}"));
            out_file
                .write_all(&shared_secret.encode())
                .expect("Error writing public key");
        }
        GenerateCli::Lint {
            file,
            name,
            result,
            invalid,
        } => {
            let file = match file {
                Some(n) => n,
                None => "lint.json".to_owned(),
            };

            if let Some(lint_name) = name {
                // Generate for the given lint.

                // There's a hex public key.
                let (public_key, validity) = if let Some(pk) = invalid {
                    let pk_bytes = hex::decode(&pk)
                        .expect(&format!("Error reading hex pk from command line\n\t{}", pk));
                    (pk_bytes, false)
                } else {
                    // Generates a key pair.
                    let (_, public_key) = kem::key_gen(alg, &mut rng).unwrap();
                    (public_key.encode(), true)
                };

                let mut payload = lint_name.as_bytes().to_vec();
                payload.extend_from_slice(&public_key);
                let id = libcrux::digest::sha2_256(&payload);
                let lint = Lint::new(
                    hex::encode(&id),
                    LintType::PublicKey,
                    &public_key,
                    &lint_name,
                    alg,
                    validity,
                );
                let lint = lint;

                println!("Writing lint to {file}");
                let mut file =
                    File::create(file.clone()).expect(&format!("Can not create file {file}"));
                serde_json::to_writer_pretty(&mut file, &lint).expect("Error writing lint file");
            } else {
                // Run the lint in the file.
                let json_file =
                    File::open(file.clone()).expect(&format!("Can not open file {file}"));
                let lint: Lint = serde_json::from_reader(json_file)
                    .expect(&format!("Error reading file {file}"));
                let alg = lint.kem_algorithm();

                let pk_bytes = lint.public_key().expect("Error reading public key.");
                eprintln!("alg: {alg:?}");
                let result_key = PublicKey::decode(alg, &pk_bytes);

                let mut lint_result = LintResult {
                    lintName: lint.lintName.clone(),
                    id: lint.id.clone(),
                    result: "Failure".to_owned(),
                };

                // We expect this one to pass.
                if lint.valid && result_key.is_err() {
                    lint_result.result = "Error".to_owned();
                    print_status("Error: valid lint lead to error.", &pk_bytes, &lint);
                }

                // This pk should not have passed.
                if !lint.valid && result_key.is_ok() {
                    lint_result.result = "Error".to_owned();
                    print_status(
                        "Error: pk validation didn't fail for invalid lint .",
                        &pk_bytes,
                        &lint,
                    );
                }

                // Passed. Valid.
                if lint.valid && result_key.is_ok() {
                    lint_result.result = "Pass".to_owned();
                    print_status(
                        "Pass: valid lint lead to successful pk validation.",
                        &pk_bytes,
                        &lint,
                    );
                }

                // Passed. Invalid
                if !lint.valid && result_key.is_err() {
                    lint_result.result = "Pass".to_owned();
                    print_status(
                        "Pass: invalid lint lead to pk validation error.",
                        &pk_bytes,
                        &lint,
                    );
                }

                let file = match result {
                    Some(n) => n,
                    None => "lint_result.json".to_owned(),
                };

                println!("Writing lint to {file}");
                let mut file =
                    File::create(file.clone()).expect(&format!("Can not create file {file}"));
                serde_json::to_writer_pretty(&mut file, &lint_result)
                    .expect("Error writing lint file");
            }
        }
    }
}

fn print_status(msg: &str, pk_bytes: &[u8], lint: &Lint) {
    eprintln!("{msg}");
    eprintln!("pk: {}", hex::encode(pk_bytes));
    eprintln!("lint: {}", serde_json::to_string_pretty(&lint).unwrap());
}

fn bytes_from_file(file: String) -> Vec<u8> {
    println!("Reading file {file}");
    let mut bytes = Vec::new();
    File::open(file.clone())
        .expect(&format!("Error opening file {file}"))
        .read_to_end(&mut bytes)
        .expect(&format!("Error reading file {file}."));
    bytes
}
