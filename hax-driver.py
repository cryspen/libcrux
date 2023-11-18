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


parser = argparse.ArgumentParser(description="Extract to F-star using Hax.")
parser.add_argument(
    "--kyber-reference",
    dest="kyber_reference",
    default=False,
    action="store_true",
    help="Extract the Kyber reference implementation.",
)
parser.add_argument(
    "--kyber-specification",
    dest="kyber_specification",
    default=False,
    action="store_true",
    help="Extract the Kyber specification.",
)
parser.add_argument(
    "--crate-path",
    type=str,
    dest="crate_path",
    nargs="?",
    default=".",
    help="Path to the crate from which to extract the code (default is path to libcrux).",
)
parser.add_argument(
    "--functions",
    type=str,
    nargs="*",
    dest="functions",
    default="",
    help="Space-separated list of functions to extract. The function names must be fully qualified.",
)

parser.add_argument(
    "--modules",
    type=str,
    dest="modules",
    nargs="*",
    default="",
    help="Space-separated list of modules to extract. The module names must be fully qualified.",
)
parser.add_argument(
    "--exclude-modules",
    type=str,
    dest="exclude_modules",
    nargs="*",
    default="",
    help="Space-separated list of modules to exclude from extraction. The module names must be fully qualified.",
)
typecheck_parser = parser.add_subparsers(
    description="Typecheck libcrux",
    dest="typecheck",
    help="Run F* etc. to typecheck the extracted libcrux code.",
)
typecheck_parser = typecheck_parser.add_parser("typecheck")
typecheck_parser.add_argument(
    "--lax",
    action="store_true",
    dest="lax",
    help="Lax typecheck the code only",
)
typecheck_parser.add_argument(
    "--admit",
    action="store_true",
    dest="admit",
    help="Set admit_smt_queries to true for typechecking",
)

options = parser.parse_args()

filter_string = ""

if options.modules:
    options.modules = " ".join(["+" + module + "::*" for module in options.modules])
    filter_string += "{}".format(options.modules)

if options.functions:
    options.functions = " ".join(["+" + function for function in options.functions])
    if not filter_string:
        filter_string += "{}".format(options.functions)
    else:
        filter_string += " {}".format(options.functions)

if options.exclude_modules:
    options.exclude_modules = " ".join(
        ["-" + module + "::*" for module in options.exclude_modules]
    )
    if not filter_string:
        filter_string += "{}".format(options.exclude_modules)
    else:
        filter_string += " {}".format(options.exclude_modules)

if options.typecheck:
    custom_env = {}
    if options.lax:
        custom_env.update({"OTHERFLAGS": "--lax"})
    if options.admit:
        custom_env.update({"OTHERFLAGS": "--admit_smt_queries true"})
    shell(["make", "-C", "proofs/fstar/extraction/"], env=custom_env)
    exit(0)

cargo_hax_into = ["cargo", "hax", "into"]
hax_env = {}

if options.kyber_reference:
    shell(
        cargo_hax_into
        + [
            "-i",
            "-** +libcrux::kem::kyber::** -libcrux::hacl::sha3::** -libcrux::digest::** -libcrux::**::types::index_impls::**",
            "fstar",
        ],
        cwd=".",
        env=hax_env,
    )
elif options.kyber_specification:
    shell(
        cargo_hax_into
        + [
            "-i",
            "-** +compress::* +ind_cpa::* +hacspec_kyber::* +matrix::* +ntt::* +parameters::* +sampling::* +serialize::* -libcrux::hacl::sha3::* -libcrux::digest::*",
            "fstar",
        ],
        cwd=os.path.join("specs", "kyber"),
        env=hax_env,
    )

else:
    if filter_string:
        shell(
            cargo_hax_into
            + [
                "-i",
                "-** {}".format(filter_string),
                "fstar",
            ],
            cwd=options.crate_path,
            env=hax_env,
        )
    else:
        shell(cargo_hax_into + ["fstar"], cwd=options.crate_path, env=hax_env)
