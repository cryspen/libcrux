#! /usr/bin/env python3

import os

# This path is expressed relative to the .git/hooks directory.
# See https://stackoverflow.com/questions/4592838/symbolic-link-to-a-hook-in-git#comment32655407_4594681
source_directory = os.path.join("..", "..", "git_hooks")

target_directory = os.path.join(".git", "hooks")

print("Creating symlink for pre-commit hook ...")
os.symlink(
    os.path.join(source_directory, "pre-commit.py"),
    os.path.join(target_directory, "pre-commit"),
)
