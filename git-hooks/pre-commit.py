#! /usr/bin/env python3

import git
from pathlib import Path
import subprocess

repo = git.Repo(".")


def shell(command, expect=0, cwd=None):
    ret = subprocess.run(command, cwd=cwd)
    if ret.returncode != expect:
        raise Exception("Error {}. Expected {}.".format(ret, expect))


for item in repo.index.diff("HEAD"):
    if Path(item.a_path).suffix == ".py":
        shell(["black", "."])
    elif Path(item.a_path).suffix == ".rs":
        shell(["cargo", "fmt"])

repo.git.add(update=True)
