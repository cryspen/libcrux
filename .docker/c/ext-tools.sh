#!/usr/bin/env bash

set -v -e -x

source $HOME/.profile

curl -L https://github.com/AeneasVerif/charon/archive/45f5a34f336e35c6cc2253bc90cbdb8d812cefa9.zip \
    --output charon.zip
unzip charon.zip
rm -rf charon.zip
mv charon-45f5a34f336e35c6cc2253bc90cbdb8d812cefa9/ charon

curl -L https://github.com/FStarLang/karamel/archive/8c3612018c25889288da6857771be3ad03b75bcd.zip \
    --output karamel.zip
unzip karamel.zip
rm -rf karamel.zip
mv karamel-8c3612018c25889288da6857771be3ad03b75bcd/ karamel

curl -L https://github.com/AeneasVerif/eurydice/archive/1fff1c51ae6e6c87eafd28ec9d5594f54bc91c0c.zip \
    --output eurydice.zip
unzip eurydice.zip
rm -rf eurydice.zip
mv eurydice-1fff1c51ae6e6c87eafd28ec9d5594f54bc91c0c/ eurydice

echo "export KRML_HOME=$HOME/karamel" >>$HOME/.profile
echo "export EURYDICE_HOME=$HOME/eurydice" >>$HOME/.profile
echo "export CHARON_HOME=$HOME/charon" >>$HOME/.profile

source $HOME/.profile

# Build everything
cd karamel
make -j
cd -

cd charon
make -j
cd -

cd eurydice/lib
rm -f charon
ln -s $CHARON_HOME/charon-ml charon
rm -f krml
ln -s $KRML_HOME/lib krml
cd ../
make -j
cd ../
