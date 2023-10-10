#! /usr/bin/env python3

import os
import argparse
import subprocess
import sys


def shell(command, expect=0, cwd=None, format_selection_string=False):
    subprocess_stdout = subprocess.DEVNULL

    print("Command: ", end="")
    for i, word in enumerate(command):
        if i == 4:
            print("'{}' ".format(word), end="")
        else:
            print("{} ".format(word), end="")

    print("\nDirectory: {}".format(cwd))

    ret = subprocess.run(command, cwd=cwd)
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
    help="Space-separated list of functions to extract. The functions must be fully qualified from the crate root.",
)

parser.add_argument(
    "--modules",
    type=str,
    dest="modules",
    nargs="*",
    default="",
    help='Space-separated list of modules to extract. The modules must be fully qualified from the crate root. The special argument"root" can be used to extract the lib.rs file.',
)

options = parser.parse_args()

if options.modules or options.functions:
    if options.modules:
        options.modules = " ".join(
            [
                "+::*" if module == "root" else "+" + module + "::*"
                for module in options.modules
            ]
        )
        options.modules = " {}".format(options.modules)

    if options.functions:
        options.functions = " ".join(
            ["+" + function for function in options.functions])
        options.functions = " {}".format(options.functions)

    shell(
        [
            "cargo",
            "hax",
            "into",
            "-i",
            "-**{}{}".format(options.functions, options.modules),
            "fstar",
        ],
        cwd=options.crate_path,
        format_selection_string=True,
    )
elif options.kyber_reference:
    shell(
        [
            "cargo",
            "hax",
            "into",
            "-i",
            "-** +kem::kyber::** -kem::kyber::arithmetic::mutable_operations::**",
            "fstar",
        ],
        cwd=".",
        format_selection_string=True,
    )
else:
    shell(["cargo", "hax", "into", "fstar"], cwd=options.crate_path)
