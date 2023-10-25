# Contributing

Third-party contributions to libcrux are welcome, be it in the form of an issue
report or a feature request via [issues](https://github.com/cryspen/libcrux)
or in the form of new code and documentation via [pull requests](https://github.com/cryspen/libcrux/pulls).

### Coding style

In order to help contributors adhere to the style guidelines of this project,
we've provided a [Python3 script](git-hooks/pre-commit.py) that serves as a Git pre-commit hook.

In addition to Python3, you will also need to install [rustfmt](https://github.com/rust-lang/rustfmt) and the [black](https://github.com/psf/black) formatter to use this hook. Once they're installed, simply
run `./git-hooks/setup.py` in the project root directory.
