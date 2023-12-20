#! /usr/bin/env python3

import os
import subprocess
import re
import shutil

NSS_ROOT = os.path.join("/", "Users", "wxyz", "repos", "nss", "nss")
FREEBL_VERIFIED_ROOT = os.path.join(NSS_ROOT, "lib", "freebl", "verified")

C_EXTRACTION_ROOT = os.path.join("kyber-crate", "c")


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


def add_libcrux_kyber_h():
    path_to_header = os.path.join(C_EXTRACTION_ROOT, "libcrux_kyber.h")

    shell(["clang-format", "-i", "-style=Google", path_to_header])
    destination = os.path.join(FREEBL_VERIFIED_ROOT, "internal", "Libcrux_Kyber_768.h")

    with open(path_to_header, "r") as f:
        original = f.read()
        replaced = re.sub("extern void libcrux_digest_sha3_512.*\n", "", original)
        replaced = re.sub("extern void libcrux_digest_sha3_256.*\n", "", replaced)
    with open(destination, "w") as f:
        f.write(replaced)

    shell(["clang-format", "-i", "-style=Mozilla", destination])


def add_libcrux_kyber_c():
    path_to_c_file = os.path.join(C_EXTRACTION_ROOT, "libcrux_kyber.c")

    shell(["clang-format", "-i", "-style=Google", path_to_c_file])
    destination = os.path.join(FREEBL_VERIFIED_ROOT, "Libcrux_Kyber_768.c")
    shutil.copyfile(path_to_c_file, destination)

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
        replaced = re.sub("libcrux_kyber.h", "internal/Libcrux_Kyber_768.h", original)
        replaced = re.sub(
            "libcrux_hacl_glue.h", "Libcrux_Kyber_Hash_Functions.h", replaced
        )
    with open(destination, "w") as f:
        f.write(replaced)

    shell(["clang-format", "-i", "-style=Mozilla", destination])


def add_internal_core_h():
    src_file = os.path.join(C_EXTRACTION_ROOT, "internal", "core.h")
    destination = os.path.join(FREEBL_VERIFIED_ROOT, "internal", "core.h")

    shutil.copyfile(src_file, destination)
    shell(["clang-format", "-i", "-style=Mozilla", destination])


def add_Eurydice_h():
    src_file = os.path.join(C_EXTRACTION_ROOT, "Eurydice.h")
    destination = os.path.join(FREEBL_VERIFIED_ROOT, "eurydice", "Eurydice.h")

    shutil.copyfile(src_file, destination)
    shell(["clang-format", "-i", "-style=Mozilla", destination])


def add_eurydice_glue_h():
    src_file = os.path.join(C_EXTRACTION_ROOT, "eurydice_glue.h")
    destination = os.path.join(FREEBL_VERIFIED_ROOT, "eurydice", "eurydice_glue.h")

    shutil.copyfile(src_file, destination)
    shell(["clang-format", "-i", "-style=Mozilla", destination])


add_libcrux_kyber_h()
add_libcrux_kyber_c()
add_internal_core_h()
add_Eurydice_h()
add_eurydice_glue_h()
