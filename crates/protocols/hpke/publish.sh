#!/bin/bash
# Helper to publish all crates in this repository.

set -e

# release all crates in the workspace in order of appearance
# in the root crate's `workspace.members`.
# sign tags and only allow the command to be run from the `main` branch. 
cargo release --workspace --sign-tag --allow-branch main
