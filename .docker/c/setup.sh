#!/usr/bin/env bash

set -v -e -x

export DEBIAN_FRONTEND=noninteractive

apt-get -y update
apt-get install -y \
    build-essential \
    opam \
    jq \
    libgmp-dev \
    locales \
    pkg-config \
    clang-format\
    curl \
    time
curl -fsSL https://deb.nodesource.com/setup_21.x | bash -
apt-get update
apt-get install -y nodejs

locale-gen $LANG
DEBIAN_FRONTEND=noninteractive dpkg-reconfigure locales
useradd -d $HOME -s $SHELL -m $USER
echo "$USER:$USER" | chpasswd && adduser $USER sudo
