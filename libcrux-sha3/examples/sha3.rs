use clap::Parser;
use libcrux_secrets::{ClassifyRef, ClassifyRefMut as _, DeclassifyRef};
use libcrux_sha3::*;

#[derive(Parser, Debug)]
#[clap(author, version, about = "Computes SHA3 of a the given string.", long_about = None)]
struct Args {
    #[clap(
        short,
        long,
        value_parser,
        default_value = "sha256",
        help = "Hash variant (e.g., sha224, sha256, sha384, sha512, shake128, shake256)."
    )]
    variant: String,

    #[clap(
        short,
        long,
        value_parser,
        default_value = "32",
        help = "Output length for keccak. Defaults to 32."
    )]
    out_len: usize,

    #[clap(
        short,
        long,
        value_parser,
        default_value = "1",
        help = "Compute the value this many times. Defaults to 1. For benchmarking"
    )]
    iterations: usize,

    #[clap(help = "Input string.")]
    input: String,
}

fn main() {
    let args = Args::parse();

    let data = args.input.as_bytes().classify_ref();
    let variant = args.variant.to_lowercase();
    let variant = variant.as_str();

    let mut digest = String::new();
    for _ in 0..args.iterations {
        digest = match variant {
            "sha224" => hex::encode(sha224(data).declassify_ref()),
            "sha256" => hex::encode(sha256(data).declassify_ref()),
            "sha384" => hex::encode(sha384(data).declassify_ref()),
            "sha512" => hex::encode(sha512(data).declassify_ref()),
            "shake128" => {
                let mut digest = vec![0u8; args.out_len];
                shake128_ema(digest.classify_ref_mut(), data);
                hex::encode(digest)
            }
            "shake256" => {
                let mut digest = vec![0u8; args.out_len];
                shake256_ema(digest.classify_ref_mut(), data);
                hex::encode(digest)
            }
            unknown_variant => {
                eprintln!(
                "Unsupported or unknown variant: \"{}\".\nSupported variants are: sha224, sha256, sha384, sha512, shake128, shake256.\n",
                unknown_variant
            );
                hex::encode(sha256(args.input.as_bytes().classify_ref()).declassify_ref())
            }
        };
    }

    println!("{digest}");
}
