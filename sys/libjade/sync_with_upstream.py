# This approach was inspired by:
# https://github.com/open-quantum-safe/liboqs/blob/main/scripts/copy_from_upstream/copy_from_upstream.py

import subprocess
import shutil
import os
import jinja2
import glob

DEBUG = 0

LIBJADE_GIT_URL = "https://github.com/formosa-crypto/libjade"
LIBJADE_GIT_TAG = "release/2023.05-1"

IMPLEMENTATIONS = {
    "hash": [
        {"name": "sha256", "platforms": {"amd64": ["ref"]}},
        {"name": "sha3-224", "platforms": {"amd64": ["ref", "avx2"]}},
    ],
}


def shell(command, expect=0, cwd=None):
    subprocess_stdout = None if DEBUG > 0 else subprocess.DEVNULL

    ret = subprocess.run(
        command, stdout=subprocess_stdout, stderr=subprocess_stdout, cwd=cwd
    )
    if ret.returncode != expect:
        raise Exception(
            "'{}' failed with error {}. Expected {}.".format(
                " ".join(command), ret, expect
            )
        )


def file_get_contents(filepath, encoding=None):
    with open(filepath, mode="r", encoding=encoding) as fh:
        return fh.read()


def file_put_contents(filepath, s, encoding=None):
    with open(filepath, mode="w", encoding=encoding) as fh:
        fh.write(s)


def output_header(input_file, output_file, encoding=None):
    with open(input_file, mode="r", encoding=encoding) as in_fh, open(
        output_file, mode="w", encoding=encoding
    ) as out_fh:
        for line in in_fh:
            if line.startswith("#ifndef") or line.startswith("#define"):
                line_split = line.split()

                if len(line_split) == 3 and not ("ALGNAME" in line or "BYTES" in line):
                    continue

                line_split[1] = line_split[1].upper()
                out_fh.write(" ".join(line_split) + "\n")
            else:
                out_fh.write(line)


def fill_using_fragments(filepath, instructions, delimiter):
    fragments = glob.glob(os.path.join("fragments_for_syncing", filepath, "*.fragment"))

    contents = file_get_contents(filepath)

    for fragment in fragments:
        template = file_get_contents(fragment)

        identifier = os.path.splitext(os.path.basename(fragment))[0]
        identifier_start = "{} SYNC_WITH_UPSTREAM_GENERATE_{}_START".format(
            delimiter, identifier.upper()
        )
        identifier_end = "{} SYNC_WITH_UPSTREAM_GENERATE_{}_END".format(
            delimiter, identifier.upper()
        )

        preamble = contents[: contents.find(identifier_start)]
        postamble = contents[contents.find(identifier_end) :]
        contents = (
            preamble
            + identifier_start
            + jinja2.Template(template).render({"instructions": instructions})
            + postamble
        )

    file_put_contents(filepath, contents)


if __name__ == "__main__":
    libjade_dotgit = os.path.join("libjade", ".git")

    if not os.path.exists(libjade_dotgit):
        shell(["git", "init", "libjade"])
        shell(
            [
                "git",
                "--git-dir",
                libjade_dotgit,
                "remote",
                "add",
                "origin",
                LIBJADE_GIT_URL,
            ]
        )

    shell(
        [
            "git",
            "--git-dir",
            libjade_dotgit,
            "--work-tree",
            "libjade",
            "remote",
            "set-url",
            "origin",
            LIBJADE_GIT_URL,
        ]
    )
    shell(["git", "--git-dir", libjade_dotgit, "--work-tree", "libjade", "fetch"])
    shell(
        [
            "git",
            "--git-dir",
            libjade_dotgit,
            "--work-tree",
            "libjade",
            "checkout",
            LIBJADE_GIT_TAG,
        ]
    )

    for algorithm_type, algorithms in IMPLEMENTATIONS.items():
        for algorithm in algorithms:
            for platform, implementations in algorithm["platforms"].items():
                for implementation in implementations:
                    alg_dir = os.path.join(
                        "libjade",
                        "src",
                        "crypto_{}".format(algorithm_type),
                        algorithm["name"],
                        platform,
                        implementation,
                    )

                    # TODO: libjade errors without this sometimes; look closer into
                    # why.
                    shell(["make", "clean"], cwd=alg_dir)

                    shell(["make"], cwd=alg_dir)

                    jazz_dir = os.path.join("jazz")
                    shutil.copyfile(
                        os.path.join(alg_dir, "{}.s".format(algorithm_type)),
                        os.path.join(
                            "jazz",
                            "{}_{}.s".format(
                                algorithm["name"].replace("-", "_"), implementation
                            ),
                        ),
                    )

                    output_header(
                        os.path.join(alg_dir, "include", "api.h"),
                        os.path.join(
                            "jazz",
                            "include",
                            "{}_{}.h".format(
                                algorithm["name"].replace("-", "_"), implementation
                            ),
                        ),
                    )

    fill_using_fragments(
        os.path.join("jazz", "include", "libjade.h"), IMPLEMENTATIONS, "/////"
    )
    fill_using_fragments("build.rs", IMPLEMENTATIONS, "/////")
