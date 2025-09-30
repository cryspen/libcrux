#!/bin/bash

set -e

# Update the hacl source code.
# This is not robust and you should know what you're doing.
# Make sure that the hacl-packages repository is checked out next to the libcrux repo

cd "$(dirname "$0")"

rm -rf include karamel src vale
cp -r ../../../../hacl-packages/src .
cp -r ../../../../hacl-packages/include .
cp -r ../../../../hacl-packages/karamel .
cp -r ../../../../hacl-packages/vale .
rm -rf src/wasm
git clean -fdx vale/
git checkout main include/config.h
git checkout main include/msvc/config.h

cd - &>/dev/null
