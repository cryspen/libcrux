#!/bin/bash
# Helper to publish all crates in this repository.

set -e

cargo release --workspace --sign-tag
