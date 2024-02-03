#! /usr/bin/env python3

import argparse
import os
from pathlib import Path
import shutil
import subprocess
import tomllib


# Make path absolute
def abs_path(path):
    dir_path = os.path.dirname(os.path.realpath(__file__))
    return Path(dir_path).joinpath(path)


# build environment used for the hax world
def environment():
    hax_env = {
        "HACL_HOME": str(hax_dep_path) + "/hacl-star",
        "KRML_HOME": str(hax_dep_path) + "/karamel",
        "EURYDICE_HOME": str(hax_dep_path) + "/eurydice",
        "CHARON_HOME": str(hax_dep_path) + "/charon",
        "FSTAR_HOME": str(hax_dep_path) + "/fstar",
    }
    return hax_env


# build environment binary paths for the hax world
def path_environment():
    return "$FSTAR_HOME/bin"


# Run a shell command
def shell(command, cwd=None, env={}):
    os_env = os.environ
    os_env.update(env)
    os_env.update(environment())
    os_env["PATH"] += os.pathsep + path_environment()

    subprocess.run(command, cwd=cwd, env=os_env, check=True)


# cargo hax for target
def cargo_hax(target):
    hax_cmd = ["cargo", "hax"]

    cargo_args = target["cargo"]
    if cargo_args:
        hax_cmd.append("-C")
        hax_cmd += cargo_args.split()
        hax_cmd.append(";")

    hax_cmd.append("into")

    include_args = target["include"]
    if include_args:
        hax_cmd.append("-i")
        hax_cmd.append(include_args)

    hax_cmd.append(target["target"])

    interfaces_args = target["interfaces"]
    if interfaces_args:
        hax_cmd.append("--interfaces")
        hax_cmd.append(interfaces_args)

    shell(hax_cmd)


# download required dependencies with git for target
def get_dep(dependency, target_path):
    if os.path.exists(target_path):
        # Only do something when the path doesn't exist
        return

    if "version" in dependency:
        # versioned dependency we use a tag/branch
        git_version = [
            "git",
            "clone",
            "--depth",
            "1",
            "--branch",
            dependency["version"],
            dependency["git"],
            target_path,
        ]
        shell(git_version)
    elif "rev" in dependency:
        # with a revision we just get that git revision
        Path(target_path).mkdir()
        git_cmd = ["git", "-C", target_path, "init"]
        shell(git_cmd)
        git_cmd = [
            "git",
            "-C",
            target_path,
            "remote",
            "add",
            "origin",
            dependency["git"],
        ]
        shell(git_cmd)
        git_cmd = ["git", "-C", target_path, "fetch", "origin", dependency["rev"]]
        shell(git_cmd)
        git_cmd = ["git", "-C", target_path, "reset", "--hard", "FETCH_HEAD"]
        shell(git_cmd)


# build required dependencies for target
def build_dep(dependency, target_path):
    if "build" not in dependency:
        print(f"No build instructions.")
        return
    for cmd in dependency["build"]:
        print(f"Run {cmd} in {target_path}")
        shell(cmd.split(), cwd=target_path)


# Path for hax dependencies
hax_dep_path = abs_path("target/hax")
proof_path = abs_path("proofs")


# download all required dependencies for target
def dependencies(target):
    Path(hax_dep_path).mkdir(parents=True, exist_ok=True)
    for dependency in target["dependencies"]:
        print(f"Getting dependency {dependency} ...")
        get_dep(
            target["dependencies"][dependency], Path(hax_dep_path).joinpath(dependency)
        )
    for dependency in target["dependencies"]:
        print(f"Building dependency {dependency} ...")
        build_dep(
            target["dependencies"][dependency], Path(hax_dep_path).joinpath(dependency)
        )


# delete dependencies
def rm_deps():
    shutil.rmtree(hax_dep_path)


# extract C code
def extract_c(target):
    shell(["./kyber-crate.sh"])


# run verification for the target
def verify(target):
    dependencies(target)

    directory = proof_path.joinpath(target["target"]).joinpath("extraction")
    if not directory.exists():
        # extract if the directory doesn't exist
        cargo_hax(target)
    cmd = target["verify"]
    shell(cmd, cwd=directory)


# === Interface ===

# CLI interface
parser = argparse.ArgumentParser(description="Hax driver.")
parser.add_argument(
    "target",
    help="The target from hax.toml to extract.",
)
parser.add_argument(
    "--extract",
    action="store_true",
    help="Extract F* for the given target.",
)
parser.add_argument(
    "--verify",
    action="store_true",
    help="Verify the extracted F* code for the given target.\nExtracts if necessary",
)
parser.add_argument(
    "--extract-c",
    action="store_true",
    help="Extract C code for the given target.",
)
parser.add_argument(
    "--clean",
    action="store_true",
    help="Clean dependencies. TODO: clean extracted code",
)

args = parser.parse_args()

# Reading config
with open("hax.toml", "rb") as f:
    hax_config = tomllib.load(f)

# Getting the target
targets = hax_config.get("target")
if args.target not in targets:
    print(f"No target '{args.target}' configured!")
    print("Check your hax.toml for available targets.")
    exit(1)

target = targets[args.target]


# Dispatch actions for target
if args.clean:
    print(f"Cleaning target {args.target} ...")
    rm_deps()
if args.extract:
    print(f"Extracting target {args.target} ...")
    cargo_hax(target)
if args.verify:
    print(f"Verifying target {args.target} ...")
    verify(target)
if args.extract_c:
    print(f"Extracting C code for {args.target}")
    extract_c(target)
