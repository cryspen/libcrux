#! /usr/bin/env python3

import os
import subprocess
import re
import shutil
import argparse


def shell(command, expect=0, cwd=None, env={}):
    subprocess_stdout = subprocess.DEVNULL

    os_env = os.environ
    os_env.update(env)

    result = subprocess.run(
        command, cwd=cwd, env=os_env, capture_output=True, text=True
    )

    if result.returncode != expect:
        raise Exception("Error {}. Expected {}.".format(result, expect))

    return result.stdout


def add_libcrux_kyber_h(c_extraction_root, freebl_verified_root):
    path_to_header = os.path.join(c_extraction_root, "libcrux_kyber.h")
    destination = os.path.join(freebl_verified_root, "Libcrux_ML_KEM_768.h")
    shutil.copyfile(path_to_header, destination)

    shell(["clang-format", "-i", "-style=Google", destination])

    with open(destination, "r") as f:
        original = f.read()
        replaced = re.sub("extern void libcrux_digest_sha3_512.*\n", "", original)
        replaced = re.sub("extern void libcrux_digest_sha3_256.*\n", "", replaced)
    with open(destination, "w") as f:
        f.write(replaced)

    shell(["clang-format", "-i", "-style=Mozilla", destination])


def add_libcrux_kyber_c(c_extraction_root, freebl_verified_root):
    path_to_c_file = os.path.join(c_extraction_root, "libcrux_kyber.c")
    destination = os.path.join(freebl_verified_root, "Libcrux_ML_KEM_768.c")
    shutil.copyfile(path_to_c_file, destination)

    shell(["clang-format", "-i", "-style=Google", destination])

    sed_cmd = shutil.which("gsed")
    if sed_cmd is None:
        sed_cmd = shutil.which("sed")

    ctags = shell(["ctags", "--fields=+ne", "-o", "-", destination])
    sed_input = ""
    for line in ctags.splitlines():
        if (
            "libcrux_kyber_serialize_compress_then_serialize_11___320size_t" in line
            or "libcrux_kyber_serialize_compress_then_serialize_5___128size_t" in line
        ):
            line_start = re.findall(r"line:(\d+)", line)[0]
            line_end = re.findall(r"end:(\d+)", line)[0]
            sed_input = "{},{}d;{}".format(line_start, line_end, sed_input)

    shell([sed_cmd, "-i", sed_input, destination])

    with open(destination, "r") as f:
        original = f.read()
        replaced = re.sub(
            '#include "libcrux_kyber.h"',
            '#include "Libcrux_ML_KEM_768.h"',
            original,
        )
        replaced = re.sub(
            '#include "libcrux_hacl_glue.h"',
            '#include "../Libcrux_ML_KEM_Hash_Functions.h"',
            replaced,
        )
        replaced = re.sub("uu____0 = !false", "uu____0 = false", replaced)
    with open(destination, "w") as f:
        f.write(replaced)

    shell(["clang-format", "-i", "-style=Mozilla", destination])


def add_internal_core_h(c_extraction_root, freebl_verified_root):
    src_file = os.path.join(c_extraction_root, "internal", "core.h")
    destination = os.path.join(freebl_verified_root, "internal", "core.h")

    shutil.copyfile(src_file, destination)
    shell(["clang-format", "-i", "-style=Mozilla", destination])


def add_Eurydice_h(c_extraction_root, freebl_verified_root):
    src_file = os.path.join(c_extraction_root, "Eurydice.h")
    destination = os.path.join(freebl_verified_root, "eurydice", "Eurydice.h")

    shutil.copyfile(src_file, destination)
    shell(["clang-format", "-i", "-style=Mozilla", destination])


def add_eurydice_glue_h(c_extraction_root, freebl_verified_root):
    src_file = os.path.join(c_extraction_root, "eurydice_glue.h")
    destination = os.path.join(freebl_verified_root, "eurydice", "eurydice_glue.h")

    shutil.copyfile(src_file, destination)
    shell(["clang-format", "-i", "-style=Mozilla", destination])


parser = argparse.ArgumentParser()
parser.add_argument(
    "--nss-root",
    required=True,
    help="Absolute or relative path to the root directory containing the NSS source code.",
    type=os.path.abspath,
)
parser.add_argument(
    "--kyber-c-root",
    required=True,
    help="Absolute or relative path to the root directory containing the extracted Kyber C code.",
    type=os.path.abspath,
)
args = parser.parse_args()

nss_root = args.nss_root
freebl_verified_root = os.path.join(nss_root, "lib", "freebl", "verified")

c_extraction_root = args.kyber_c_root

add_libcrux_kyber_h(c_extraction_root, freebl_verified_root)
add_libcrux_kyber_c(c_extraction_root, freebl_verified_root)
add_internal_core_h(c_extraction_root, freebl_verified_root)
add_Eurydice_h(c_extraction_root, freebl_verified_root)
add_eurydice_glue_h(c_extraction_root, freebl_verified_root)
