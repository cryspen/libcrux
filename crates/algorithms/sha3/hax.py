#! /usr/bin/env python3

import os
import argparse
import subprocess
import sys


def shell(command, expect=0, cwd=None, env={}):
    subprocess_stdout = subprocess.DEVNULL

    print("Env:", env)
    print("Command: ", end="")
    for i, word in enumerate(command):
        if i == 4:
            print("'{}' ".format(word), end="")
        else:
            print("{} ".format(word), end="")

    print("\nDirectory: {}".format(cwd))

    os_env = os.environ
    os_env.update(env)

    ret = subprocess.run(command, cwd=cwd, env=os_env)
    if ret.returncode != expect:
        raise Exception("Error {}. Expected {}.".format(ret, expect))


class extractAction(argparse.Action):

    def __call__(self, parser, args, values, option_string=None) -> None:
        # Extract platform interfaces
        include_str = "+:** -**::x86::init::cpuid -**::x86::init::cpuid_count"
        interface_include = "+**"
        cargo_hax_into = [
            "cargo",
            "hax",
            "into",
            "-i",
            include_str,
            "fstar",
            "--interfaces",
            interface_include,
        ]
        hax_env = {}
        shell(
            cargo_hax_into,
            cwd="../../sys/platform",
            env=hax_env,
        )

        # Extract intrinsics interfaces
        include_str = "+:**"
        interface_include = "+**"
        if args.portable:
            cargo_args = []
        else:
            cargo_args = ["-C", "--features", "simd128,simd256", ";"]

        cargo_hax_into = [
            "cargo",
            "hax",
        ] + cargo_args + [
            "into",
            "-i",
            include_str,
            "fstar",
            "--interfaces",
            interface_include,
        ]
        hax_env = {}
        shell(
            cargo_hax_into,
            cwd="../../utils/intrinsics",
            env=hax_env,
        )

        # Extract libcrux-secrets
        include_str = "+**"
        interface_include = ""
        cargo_hax_into = [
            "cargo",
            "hax",
            "into",
            "-i",
            include_str,
            "fstar",
        ]
        hax_env = {}
        shell(
            cargo_hax_into,
            cwd="../../utils/secrets",
            env=hax_env,
        )

        # Extract Core models
        cargo_hax_into = [
            "cargo",
            "hax",
            "into",
            "fstar",
        ]
        hax_env = {}
        shell(
            cargo_hax_into,
            cwd="../../utils/core-models",
            env=hax_env,
        )

        # Extract sha3
        if args.portable:
            # For portable-only: exclude all SIMD implementations
            include_str = "+** -**::avx2::** -**::neon::** -**::simd128::** -**::simd256::**"
            cargo_args = []
        else:
            include_str = "+**"
            cargo_args = ["-C", "--features", "simd128,simd256", ";"]

        interface_include = "+**"
        cargo_hax_into = [
            "cargo",
            "hax",
        ] + cargo_args + [
            "into",
            "-i",
            include_str,
            "fstar",
            "--z3rlimit",
            "80",
        ]
        hax_env = {}
        shell(
            cargo_hax_into,
            cwd=".",
            env=hax_env,
        )
        return None


class proveAction(argparse.Action):

    def __call__(self, parser, args, values, option_string=None) -> None:
        admit_env = {}
        if args.admit:
            admit_env = {"OTHERFLAGS": "--admit_smt_queries true"}
        shell(["make", "-j4", "-C", "proofs/fstar/extraction/"], env=admit_env)
        return None


class cleanAction(argparse.Action):

    def __call__(self, parser, args, values, option_string=None) -> None:
        extraction_dir = "proofs/fstar/extraction"

        if not os.path.exists(extraction_dir):
            print(f"Directory {extraction_dir} does not exist, nothing to clean.")
            return None

        print(f"Cleaning {extraction_dir}...")
        shell(["make", "-C", extraction_dir, "clean"])
        print("Clean completed.")
        return None


def parse_arguments():
    parser = argparse.ArgumentParser(
        description="Libcrux prove script. "
        + "Make sure to separate sub-command arguments with --."
    )
    subparsers = parser.add_subparsers()

    extract_parser = subparsers.add_parser(
        "extract", help="Extract the F* code for the proofs."
    )
    extract_parser.add_argument(
        "--portable",
        help="Extract only portable implementations (exclude SIMD variants).",
        action="store_true",
    )
    extract_parser.add_argument("extract", nargs="*", action=extractAction)

    prover_parser = subparsers.add_parser(
        "prove",
        help="""
        Run F*.

        This typechecks the extracted code.
        To lax-typecheck use --admit.
        """,
    )
    prover_parser.add_argument(
        "--admit",
        help="Admit all smt queries to lax typecheck.",
        action="store_true",
    )
    prover_parser.add_argument(
        "prove",
        nargs="*",
        action=proveAction,
    )
    clean_parser = subparsers.add_parser(
        "clean", help="Clean generated files from proofs/fstar/extraction directory."
    )
    clean_parser.add_argument("clean", nargs="*", action=cleanAction)

    if len(sys.argv) == 1:
        parser.print_help(sys.stderr)
        sys.exit(1)

    return parser.parse_args()


def main():
    # Don't print unnecessary Python stack traces.
    sys.tracebacklimit = 0
    parse_arguments()


if __name__ == "__main__":
    main()
