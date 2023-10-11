#! /usr/bin/env python3

import os
import argparse
import subprocess
import sys


def shell(command, expect=0, cwd=None, format_filter_string=False):
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

options = parser.parse_args()

filter_string = ""

if options.modules:
    options.modules = " ".join(["+" + module + "::*" for module in options.modules])
    filter_string += "{}".format(options.modules)
if options.functions:
    options.functions = " ".join(["+" + function for function in options.functions])
    filter_string += " {}".format(options.functions)

if options.exclude_modules:
    options.exclude_modules = " ".join(
        ["-" + module + "::*" for module in options.exclude_modules]
    )
    filter_string += " {}".format(options.exclude_modules)


if filter_string:
    shell(
        [
            "cargo",
            "hax",
            "into",
            "-i",
            "-**{}{}".format(filter_string),
            "fstar",
        ],
        cwd=options.crate_path,
        format_filter_string=True,
    )
elif options.kyber_reference:
    shell(
        [
            "cargo",
            "hax",
            "into",
            "-i",
            "-** +libcrux::kem::kyber::** -libcrux::kem::kyber::arithmetic::mutable_operations::** -libcrux::hacl::sha3::** -libcrux::digest::**",
            "fstar",
        ],
        cwd=".",
        format_filter_string=True,
    )
else:
    shell(["cargo", "hax", "into", "fstar"], cwd=options.crate_path)
