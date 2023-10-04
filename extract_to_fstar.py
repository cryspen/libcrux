import os
import argparse
import subprocess
import sys


def shell(command, expect=0, cwd=None, format_function_string=False):
    subprocess_stdout = subprocess.DEVNULL

    command_formatted = command.copy()
    if format_function_string:
        command_formatted[4] = "'{}'".format(command_formatted[4])

    print("Command: {}".format(" ".join(command_formatted)))
    print("Directory: {}".format(cwd))

    ret = subprocess.run(
        command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=cwd
    )
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
    "--crate",
    type=str,
    dest="crate",
    nargs="?",
    default=".",
    help="Path to the crate from which to extract the code (default is path to libcrux).",
)
parser.add_argument(
    "--functions",
    type=str,
    nargs="*",
    default="",
    help="Space-separated list of functions to extract",
)
args = parser.parse_args()

if args.functions:
    args.functions = " ".join(["+" + function for function in args.functions])
    shell(
        ["cargo", "hax", "into", "-i", "-** {}".format(args.functions), "fstar"],
        cwd=args.crate,
        format_function_string=True,
    )
else:
    if args.kyber_reference:
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
            format_function_string=True,
        )
    else:
        shell(["cargo", "hax", "into", "fstar"], cwd=args.crate)
