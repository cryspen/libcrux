#! /usr/bin/env python3

import git
from pathlib import Path
import subprocess

repo = git.Repo(".")


def shell(command, expect=0, cwd=None):
    ret = subprocess.run(command, cwd=cwd)
    if ret.returncode != expect:
        raise Exception("Error {}. Expected {}.".format(ret, expect))


format_python_files = False
format_rust_files = False
update_libcrux_kyber_fstar_extraction = False
update_spec_kyber_fstar_extraction = False

for item in repo.index.diff("HEAD"):
    path = Path(item.a_path)
    if path.suffix == ".py":
        format_python_files = True
    elif path.suffix == ".rs":
        format_rust_files = True
        if "kyber" in path.parts:
            if "src" in path.parts:
                update_libcrux_kyber_fstar_extraction = True
            if "specs" in path.parts and "src" in path.parts:
                update_spec_kyber_fstar_extraction = True

if format_python_files == True:
    shell(["black", "."])
if format_rust_files == True:
    shell(["cargo", "fmt"])
if update_libcrux_kyber_fstar_extraction == True:
    shell(["./hax-driver.py", "--kyber-reference"])
if update_spec_kyber_fstar_extraction == True:
    shell(["./hax-driver.py", "--kyber-specification"])

for item in repo.index.diff("HEAD"):
    repo.git.add(item.a_path)
