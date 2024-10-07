use std::{
    fs::File,
    io::{Read, Write},
};

use base64::prelude::*;
use clap::{Parser, Subcommand};
use libcrux_ml_kem::{
    mlkem1024::{
        self, MlKem1024Ciphertext, MlKem1024KeyPair, MlKem1024PrivateKey, MlKem1024PublicKey,
    },
    mlkem512::{self, MlKem512Ciphertext, MlKem512KeyPair, MlKem512PrivateKey, MlKem512PublicKey},
    mlkem768::{self, MlKem768Ciphertext, MlKem768KeyPair, MlKem768PrivateKey, MlKem768PublicKey},
    MlKemSharedSecret,
};
use rand::RngCore;
use serde::{Deserialize, Serialize};

#[allow(non_snake_case)]
#[derive(Serialize, Deserialize)]
struct Lint {
    lintName: String,
    // algorithm: Algorithm,
    // valid: bool,
    // r#type: String,
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

impl Lint {
    // XXX: Only kem for now. Needs updating for ml-dsa
    fn new(
        id: String,
        // lint_type: LintType,
        pk: &[u8],
        name: &str,
        // algorithm: Algorithm,
        // valid: bool,
    ) -> Self {
        Self {
            lintName: name.to_owned(),
            // r#type: match lint_type {
            //     LintType::PublicKey => "PublicKey".to_owned(),
            // },
            id,
            publicKey: BASE64_STANDARD.encode(pk),
            // algorithm,
            // valid,
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

    // fn kem_algorithm(&self) -> Algorithm {
    //     self.algorithm
    // }

    fn public_key(&self) -> Option<Vec<u8>> {
        BASE64_STANDARD.decode(&self.publicKey).ok()
    }
}

#[derive(Subcommand)]
enum Cmd {
    GenerateKey {
        /// Optionally, a file name to store the keys into.
        ///
        /// The keys will be store into `$out.pub` and `$out.priv` when this is used.
        #[arg(short, long)]
        out: Option<String>,

        /// Generate an unpacked key.
        #[arg(short, long)]
        unpacked: bool,
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
    cmd: Cmd,

    /// The key length, 512, 768, or 1024
    ///
    /// Defaults to 768
    #[arg(short, long)]
    algorithm: Option<u16>,
}

#[derive(Serialize, Deserialize, Clone, Copy, Debug)]
enum Algorithm {
    MlKem1024,
    MlKem768,
    MlKem512,
}

enum KeyPair {
    MlKem1024(MlKem1024KeyPair),
    MlKem768(MlKem768KeyPair),
    MlKem512(MlKem512KeyPair),
}

enum UnpackedKeyPair {
    MlKem1024(mlkem1024::portable::unpacked::MlKem1024KeyPairUnpacked),
    MlKem768(mlkem768::portable::unpacked::MlKem768KeyPairUnpacked),
    MlKem512(mlkem512::portable::unpacked::MlKem512KeyPairUnpacked),
}

impl UnpackedKeyPair {
    fn generate(alg: Algorithm, rng: &mut impl RngCore) -> Self {
        let randomness = rand(rng);
        match alg {
            Algorithm::MlKem1024 => {
                let mut kp = mlkem1024::portable::unpacked::MlKem1024KeyPairUnpacked::new();
                mlkem1024::portable::unpacked::generate_key_pair(randomness, &mut kp);
                UnpackedKeyPair::MlKem1024(kp)
            }
            Algorithm::MlKem768 => {
                let mut kp = mlkem768::portable::unpacked::MlKem768KeyPairUnpacked::new();
                mlkem768::portable::unpacked::generate_key_pair(randomness, &mut kp);
                UnpackedKeyPair::MlKem768(kp)
            }
            Algorithm::MlKem512 => {
                let mut kp = mlkem512::portable::unpacked::MlKem512KeyPairUnpacked::new();
                mlkem512::portable::unpacked::generate_key_pair(randomness, &mut kp);
                UnpackedKeyPair::MlKem512(kp)
            }
        }
    }

    fn write_to_file(&self, sk_name: String, pk_name: String) {
        match self {
            UnpackedKeyPair::MlKem1024(_) => todo!(),
            UnpackedKeyPair::MlKem768(kp) => {
                todo!()
                // let mut bytes = [0u8; 32 + 3 * 16 * 32 + 32 + 3 * 3 * 16 * 32 + 3 * 16 * 32 + 32];
                // kp.to_bytes(&mut bytes);
                // write_to_file(sk_name + "_" + &pk_name, &bytes);
            }
            UnpackedKeyPair::MlKem512(_) => todo!(),
        }
    }
}

impl KeyPair {
    fn generate(alg: Algorithm, rng: &mut impl RngCore) -> Self {
        let randomness = rand(rng);
        match alg {
            Algorithm::MlKem1024 => KeyPair::MlKem1024(mlkem1024::generate_key_pair(randomness)),
            Algorithm::MlKem768 => KeyPair::MlKem768(mlkem768::generate_key_pair(randomness)),
            Algorithm::MlKem512 => KeyPair::MlKem512(mlkem512::generate_key_pair(randomness)),
        }
    }

    fn write_to_file(&self, sk_name: String, pk_name: String) {
        write_to_file(sk_name, self.private_key_slice());
        write_to_file(pk_name, self.public_key_slice());
    }

    fn private_key_slice(&self) -> &[u8] {
        match self {
            KeyPair::MlKem1024(k) => k.sk(),
            KeyPair::MlKem768(k) => k.sk(),
            KeyPair::MlKem512(k) => k.sk(),
        }
    }

    fn public_key_slice(&self) -> &[u8] {
        match self {
            KeyPair::MlKem1024(k) => k.pk(),
            KeyPair::MlKem768(k) => k.pk(),
            KeyPair::MlKem512(k) => k.pk(),
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum Error {
    InvalidPublicKey,
    InvalidPrivateKey,
    InvalidCiphertext,
}

enum PublicKey {
    MlKem1024(MlKem1024PublicKey),
    MlKem768(MlKem768PublicKey),
    MlKem512(MlKem512PublicKey),
}

impl PublicKey {
    fn decode(alg: Algorithm, pk: &[u8]) -> Result<Self, Error> {
        match alg {
            Algorithm::MlKem1024 => {
                let pk = MlKem1024PublicKey::try_from(pk).map_err(|_| Error::InvalidPublicKey)?;
                if mlkem1024::validate_public_key(&pk) {
                    Ok(Self::MlKem1024(pk))
                } else {
                    Err(Error::InvalidPublicKey)
                }
            }
            Algorithm::MlKem768 => {
                let pk = MlKem768PublicKey::try_from(pk).map_err(|_| Error::InvalidPublicKey)?;
                if mlkem768::validate_public_key(&pk) {
                    Ok(Self::MlKem768(pk))
                } else {
                    Err(Error::InvalidPublicKey)
                }
            }
            Algorithm::MlKem512 => {
                let pk = MlKem512PublicKey::try_from(pk).map_err(|_| Error::InvalidPublicKey)?;
                if mlkem512::validate_public_key(&pk) {
                    Ok(Self::MlKem512(pk))
                } else {
                    Err(Error::InvalidPublicKey)
                }
            }
        }
    }

    fn encapsulate(&self, rng: &mut impl RngCore) -> (Ciphertext, MlKemSharedSecret) {
        let randomness = rand(rng);
        match self {
            PublicKey::MlKem1024(k) => {
                let (ct, ss) = mlkem1024::encapsulate(k, randomness);
                (Ciphertext::MlKem1024(ct), ss)
            }
            PublicKey::MlKem768(k) => {
                let (ct, ss) = mlkem768::encapsulate(k, randomness);
                (Ciphertext::MlKem768(ct), ss)
            }
            PublicKey::MlKem512(k) => {
                let (ct, ss) = mlkem512::encapsulate(k, randomness);
                (Ciphertext::MlKem512(ct), ss)
            }
        }
    }
}

enum PrivateKey {
    MlKem1024(MlKem1024PrivateKey),
    MlKem768(MlKem768PrivateKey),
    MlKem512(MlKem512PrivateKey),
}
impl PrivateKey {
    fn decode(alg: Algorithm, sk: &[u8]) -> Result<Self, Error> {
        match alg {
            Algorithm::MlKem1024 => MlKem1024PrivateKey::try_from(sk)
                .map(Self::MlKem1024)
                .map_err(|_| Error::InvalidPrivateKey),
            Algorithm::MlKem768 => MlKem768PrivateKey::try_from(sk)
                .map(Self::MlKem768)
                .map_err(|_| Error::InvalidPrivateKey),
            Algorithm::MlKem512 => MlKem512PrivateKey::try_from(sk)
                .map(Self::MlKem512)
                .map_err(|_| Error::InvalidPrivateKey),
        }
    }
}

fn rand<const L: usize>(rng: &mut impl RngCore) -> [u8; L] {
    let mut r = [0u8; L];
    rng.fill_bytes(&mut r);
    r
}

enum Ciphertext {
    MlKem1024(MlKem1024Ciphertext),
    MlKem768(MlKem768Ciphertext),
    MlKem512(MlKem512Ciphertext),
}
impl Ciphertext {
    fn write_to_file(&self, ct_out: String) {
        match self {
            Ciphertext::MlKem1024(ct) => write_to_file(ct_out, ct.as_ref()),
            Ciphertext::MlKem768(ct) => write_to_file(ct_out, ct.as_ref()),
            Ciphertext::MlKem512(ct) => write_to_file(ct_out, ct.as_ref()),
        }
    }

    fn decode(alg: Algorithm, ct: &[u8]) -> Result<Self, Error> {
        match alg {
            Algorithm::MlKem1024 => MlKem1024Ciphertext::try_from(ct)
                .map(Self::MlKem1024)
                .map_err(|_| Error::InvalidCiphertext),
            Algorithm::MlKem768 => MlKem768Ciphertext::try_from(ct)
                .map(Self::MlKem768)
                .map_err(|_| Error::InvalidCiphertext),
            Algorithm::MlKem512 => MlKem512Ciphertext::try_from(ct)
                .map(Self::MlKem512)
                .map_err(|_| Error::InvalidCiphertext),
        }
    }

    fn decapsulate(&self, sk: &PrivateKey) -> MlKemSharedSecret {
        match (self, sk) {
            (Ciphertext::MlKem1024(ct), PrivateKey::MlKem1024(sk)) => {
                mlkem1024::decapsulate(sk, ct)
            }
            (Ciphertext::MlKem768(ct), PrivateKey::MlKem768(sk)) => mlkem768::decapsulate(sk, ct),
            (Ciphertext::MlKem512(ct), PrivateKey::MlKem512(sk)) => mlkem512::decapsulate(sk, ct),
            _ => unreachable!(),
        }
    }
}

fn main() {
    pretty_env_logger::init();

    let cli = Cli::parse();

    let alg = if let Some(l) = cli.algorithm {
        match l {
            512 => Algorithm::MlKem512,
            768 => Algorithm::MlKem768,
            1024 => Algorithm::MlKem1024,
            _ => {
                eprintln!("Invalid algorithm variant {l}");
                return;
            }
        }
    } else {
        Algorithm::MlKem768
    };

    let mut rng = rand::rngs::OsRng;

    match cli.cmd {
        Cmd::GenerateKey {
            out: file,
            unpacked,
        } => {
            // Generate a key pair and write it out.
            let (sk_name, pk_name) = match file {
                Some(n) => (format!("{n}.priv"), format!("{n}.pub")),
                None => ("mlkem.priv".to_owned(), "mlkem.pub".to_owned()),
            };

            if unpacked {
                let key_pair = UnpackedKeyPair::generate(alg, &mut rng);
                key_pair.write_to_file(sk_name, pk_name);
            } else {
                let key_pair = KeyPair::generate(alg, &mut rng);
                key_pair.write_to_file(sk_name, pk_name);
            }
        }

        Cmd::Encaps { key, ct: out, ss } => {
            let pk = bytes_from_file(key);
            let pk = PublicKey::decode(alg, &pk).expect("Error decoding public key");

            let (ciphertext, shared_secret) = pk.encapsulate(&mut rng);

            let ct_out = match out {
                Some(n) => n,
                None => "mlkem.ct".to_owned(),
            };
            let ss_out = match ss {
                Some(n) => n,
                None => "mlkem-encapsulated.ss".to_owned(),
            };

            ciphertext.write_to_file(ct_out);
            write_to_file(ss_out, &shared_secret);
        }
        Cmd::Decaps { key, ss: out, ct } => {
            let sk = bytes_from_file(key);
            let sk = PrivateKey::decode(alg, &sk).expect("Error decoding private key");

            let ct = bytes_from_file(ct);

            let ct = Ciphertext::decode(alg, &ct).expect("Error decoding ct.");
            let shared_secret = ct.decapsulate(&sk);

            let out = match out {
                Some(n) => n,
                None => "mlkem-decapsulated.ss".to_owned(),
            };

            write_to_file(out, &shared_secret);
        }
        Cmd::Lint {
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
                    let key_pair = KeyPair::generate(alg, &mut rng);
                    (key_pair.public_key_slice().to_vec(), true)
                };

                let mut payload = lint_name.as_bytes().to_vec();
                payload.extend_from_slice(&public_key);
                let id = libcrux_sha3::sha256(&payload);
                let lint = Lint::new(
                    hex::encode(&id),
                    // LintType::PublicKey,
                    &public_key,
                    &lint_name,
                    // alg,
                    // validity,
                );
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
                let alg = Algorithm::MlKem768;
                // let alg = lint.kem_algorithm();

                let pk_bytes = lint.public_key().expect("Error reading public key.");
                eprintln!("alg: {alg:?}");

                // Decode the public key.
                // This verifies that it's a valid key.
                let result_key = PublicKey::decode(alg, &pk_bytes);

                let mut lint_result = LintResult {
                    lintName: lint.lintName.clone(),
                    id: lint.id.clone(),
                    result: "Failure".to_owned(),
                };

                // We expect this one to pass.
                if result_key.is_err() {
                    lint_result.result = "Error".to_owned();
                    print_status("Error: valid lint lead to error.", &pk_bytes, &lint);
                }

                // This pk should not have passed.
                if result_key.is_ok() {
                    lint_result.result = "Pass".to_owned();
                    print_status(
                        "This is a valid public key",
                        &pk_bytes,
                        &lint,
                    );
                }

                // // Passed. Valid.
                // if lint.valid && result_key.is_ok() {
                //     lint_result.result = "Pass".to_owned();
                //     print_status(
                //         "Pass: valid lint lead to successful pk validation.",
                //         &pk_bytes,
                //         &lint,
                //     );
                // }

                // // Passed. Invalid
                // if !lint.valid && result_key.is_err() {
                //     lint_result.result = "Pass".to_owned();
                //     print_status(
                //         "Pass: lint with invalid PK lead to pk validation error.",
                //         &pk_bytes,
                //         &lint,
                //     );
                // }

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

fn write_to_file(file: String, bytes: &[u8]) {
    println!("Writing to {file}");
    let mut out_file = File::create(file.clone()).expect(&format!("Can not create file {file}"));
    out_file.write_all(bytes).expect("Error writing public key");
}
