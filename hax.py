#! /usr/bin/env python3

import argparse
import os
from pathlib import Path
import shutil
import subprocess
import tomllib


version = 0.1


# Make path absolute
def abs_path(path):
    dir_path = os.path.dirname(os.path.realpath(__file__))
    return Path(dir_path).joinpath(path)


# Absolute path in the home directory
def home_path(path):
    return os.path.expanduser(path)


# Path for hax dependencies
hax_dep_path = home_path("~/.hax")
proof_path = abs_path("proofs")


def target_proof_path(target):
    return proof_path.joinpath(target["target"]).joinpath("extraction")


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


# get the config as string to print
def config_str():
    config = [
        "Config:",
        f"  - Dependencies are stored in {hax_dep_path}",
        f"  - The prove code is expected in {proof_path}/target.target/extracted",
        f"  - Set environment variables",
    ]
    for key, value in environment().items():
        config.append(f"    - {key}={value}")
    config.append(f"    - PATH=$PATH{os.pathsep}{path_environment()}")
    return "\n".join(config)


# Run a shell command
def shell(command, cwd=None, env={}, stdout=None):
    os_env = os.environ
    os_env.update(env)
    os_env.update(environment())
    os_env["PATH"] += os.pathsep + path_environment()

    print("env:")
    print(os_env)

    return subprocess.run(command, cwd=cwd, env=os_env, check=True, stdout=stdout)


# The main parser to attach to with the decorator.
cli = argparse.ArgumentParser(
    description=f"Hax driver v{version}\n\n{config_str()}",
    formatter_class=argparse.RawTextHelpFormatter,
)
cli.add_argument(
    "target",
    help="The target from hax.toml to extract.",
)
subparsers = cli.add_subparsers(dest="subcommand")
cli.add_argument(
    "--clean",
    type=str,
    nargs="*",
    action="append",
    help="Clean dependencies and code.\n\
Use 'proof' or 'dep' to only clean one or the other",
)


def subcommand(args=[], parent=subparsers):
    """Decorator for sub commands."""
    # dependency_check() TODO: add

    def decorator(func):
        parser = parent.add_parser(
            func.__name__,
            description=func.__doc__,
            formatter_class=argparse.RawTextHelpFormatter,
        )
        for arg in args:
            parser.add_argument(*arg[0], **arg[1])
        parser.set_defaults(func=func)

    return decorator


def argument(*name_or_flags, **kwargs):
    """Helper for subcommand decorator"""
    return ([*name_or_flags], kwargs)


def read_config():
    """Reading config"""

    with open("hax.toml", "rb") as f:
        hax_config = tomllib.load(f)
    return hax_config


def get_target(hax_config, name):
    """Getting the target"""

    targets = hax_config.get("target")
    if name not in targets:
        print(f"No target '{name}' configured!")
        print("Check your hax.toml for available targets.")
        exit(1)

    return targets[name]


def read_target(name):
    """Get the target with the given `name`"""

    config = read_config()
    return get_target(config, name)


@subcommand()
def extract(args):
    _extract(args)


def _extract(args):
    """Extract the proof code for the given target"""

    name = args.target
    target = read_target(name)

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

    print(f"Running {' '.join(hax_cmd)}")
    shell(hax_cmd)


# download required dependencies with git for target
def get_dep(dependency, target_path):
    def get_rev():
        git_cmd = ["git", "-C", target_path, "fetch", "origin", dependency["rev"]]
        shell(git_cmd)
        git_cmd = ["git", "-C", target_path, "reset", "--hard", "FETCH_HEAD"]
        shell(git_cmd)

    if os.path.exists(target_path):
        if "version" in dependency:
            # TODO: update
            return
        elif "rev" in dependency:
            # Update to the revision in the config. This may be a no-op.
            get_rev()

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
        get_rev()


# build required dependencies for target
def build_dep(dependency, target_path):
    if "build" not in dependency:
        print(f"No build instructions.")
        return
    for cmd in dependency["build"]:
        print(f"Run {cmd} in {target_path}")
        shell(cmd.split(), cwd=target_path)


@subcommand()
def dependencies(args):
    """Download all required dependencies for target and build them"""

    _dependencies(args)


def _dependencies(args):
    name = args.target
    target = read_target(name)

    Path(hax_dep_path).mkdir(parents=True, exist_ok=True)
    for dependency in target["dependencies"]:
        print(f"Getting dependency {dependency} ...")
        get_dep(
            target["dependencies"][dependency],
            Path(hax_dep_path).joinpath(dependency),
        )
    for dependency in target["dependencies"]:
        print(f"Building dependency {dependency} ...")
        build_dep(
            target["dependencies"][dependency],
            Path(hax_dep_path).joinpath(dependency),
        )


@subcommand()
def setup(args):
    """
    Install all dependencies required to get the toolchain running.
    This includes the call to 'dependencies'.

    Note that this requires 'opam' to be installed on your system.
    """

    cmd = ["opam", "switch", "list"]
    switches = shell(cmd, stdout=subprocess.PIPE)
    # XXX: Make ocaml version configurable?
    if "4.14.1" in str(switches.stdout):
        print("ocaml 4.14.1 is already installed.")
    else:
        print("Installing ocaml 4.14.1 ...")
        cmd = [
            "opam",
            "init",
            "--bare",
            "--disable-sandboxing",
            "--yes",
            "--shell-setup",
        ]
        shell(cmd)
        cmd = ["opam", "switch", "create", "4.14.1", "--yes"]
        shell(cmd)

    cmd = ["opam", "install", "dune", "--yes"]
    shell(cmd)

    _dependencies(args)


@subcommand()
def extract_c(target):
    """Extract C code"""
    shell(["./kyber-crate.sh"])


@subcommand()
def verify(args):
    """Run verification for the target"""

    name = args.target
    _dependencies(args)

    target = read_target(name)
    directory = target_proof_path(target)
    if not directory.exists():
        # extract if the directory doesn't exist
        _extract(args)
    cmd = target["verify"]
    shell(cmd, cwd=directory)


def clean(args):
    """Remove all prove artifacts and dependencies"""

    to_clean = args.clean[0]
    if len(to_clean) == 0:
        to_clean = ["proof", "dep"]

    if "proof" in to_clean:
        name = args.target
        target = read_target(name)
        directory = target_proof_path(target)

        for cmd in target["clean"]:
            print(f"Run {cmd} in {directory}")
            shell(cmd.split(), cwd=directory)

    if "dep" in to_clean:
        shutil.rmtree(hax_dep_path, ignore_errors=True)


# === Boiler plate === #


def main():
    args = cli.parse_args()
    # print(args)
    if args.clean:
        clean(args)
    elif args.subcommand is None:
        cli.print_help()
    else:
        args.func(args)


if __name__ == "__main__":
    main()
