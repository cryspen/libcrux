#!/usr/bin/env bash

set -e

cwd=$(cd $(dirname $0); pwd -P)

export LD_LIBRARY_PATH="$cwd/lib"
export LIBRARY_PATH="$cwd/lib"
export CPATH="$cwd/include"
export PATH="$cwd/bin:$PATH"

wget -m https://cpucycles.cr.yp.to/libcpucycles-latest-version.txt
version=$(cat cpucycles.cr.yp.to/libcpucycles-latest-version.txt)
wget -m https://cpucycles.cr.yp.to/libcpucycles-$version.tar.gz
tar -xzf cpucycles.cr.yp.to/libcpucycles-$version.tar.gz
cd libcpucycles-$version

./configure --prefix=$cwd && make -j8 install

cd -

wget -m https://randombytes.cr.yp.to/librandombytes-latest-version.txt
version=$(cat randombytes.cr.yp.to/librandombytes-latest-version.txt)
wget -m https://randombytes.cr.yp.to/librandombytes-$version.tar.gz
tar -xzf randombytes.cr.yp.to/librandombytes-$version.tar.gz
cd librandombytes-$version

./configure --prefix=$cwd && make -j8 install

cd -

wget -m https://lib25519.cr.yp.to/lib25519-latest-version.txt
version=$(cat lib25519.cr.yp.to/lib25519-latest-version.txt)
wget -m https://lib25519.cr.yp.to/lib25519-$version.tar.gz
tar -xzf lib25519.cr.yp.to/lib25519-$version.tar.gz
cd lib25519-$version

./configure --prefix=$cwd && make -j8 install

cd -

rm -rf lib25519* randombytes* cpucycles* librandombytes* libcpucycles*
