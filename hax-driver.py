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
parser.add_argument(
    "--verify-extraction",
    dest="verify_extraction",
    default=False,
    action="store_true",
    help="Run the make command to run the FStar typechecker on the extracted files. Some files are lax-checked whereas others are strict-typechecked.",
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

cargo_hax_into = ["cargo", "hax", "into"]
hax_env = {}

exclude_sha3_implementations = "-libcrux::hacl::sha3::** -libcrux::jasmin::sha3::**"

if options.verify_extraction:
    shell(["make", "-C", "proofs/fstar/extraction/"])
elif options.kyber_reference:
    # Delete all extracted F* files
    shell(["rm", "-f", "./proofs/fstar/extraction/Libcrux*"])
    # Extract both `libcrux` and `libcrux-platform`
    shell(
        [
            "cargo",
            "hax",
            "-C",
            "-p",
            "libcrux",
            "-p",
            "libcrux-platform",
            ";",
            "into",
            "-i",
            f"-** +libcrux::kem::kyber::** +!libcrux_platform::platform::* {exclude_sha3_implementations} -libcrux::**::types::index_impls::**",
            "fstar",
            "--interfaces",
            "+* -libcrux::kem::kyber::types +!libcrux_platform::** +!libcrux::digest::**",
        ],
        cwd=".",
        env=hax_env,
    )
    # Delete F* implementation modules for `libcrux_platform` (TODO:
    # remove this when https://github.com/hacspec/hax/issues/465 is
    # closed)
    shell(["rm", "-f", "./sys/platform/proofs/fstar/extraction/*.fst"])

elif options.kyber_specification:
    shell(
        cargo_hax_into
        + [
            "-i",
            "-** +compress::* +ind_cpa::* +hacspec_kyber::* +matrix::* +ntt::* +parameters::* +sampling::* +serialize::* {} -libcrux::digest::*".format(
                exclude_sha3_implementations
            ),
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
