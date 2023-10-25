#! /usr/bin/env python3

import os
import subprocess

# This path is expressed relative to the .git/hooks directory.
# See https://stackoverflow.com/questions/4592838/symbolic-link-to-a-hook-in-git#comment32655407_4594681
source_directory = os.path.join("..", "..", "git-hooks")

target_directory = os.path.join(".git", "hooks")

print("Creating symlink for pre-commit hook ...", end="")
os.symlink(
    os.path.join(source_directory, "pre-commit.py"),
    os.path.join(target_directory, "pre-commit"),
)
print(" Done.")

print("Installing required modules ...", end="")
process = subprocess.run(
    ["pip3", "install", "--requirement", os.path.join("git-hooks", "requirements.txt")],
    check=True,
)
process.check_returncode()
print(" Done.")
