#!/usr/bin/env bash

set -v -e -x

source $HOME/.profile

curl -L https://github.com/AeneasVerif/charon/archive/28d543bfacc902ba9cc2a734b76baae9583892a4.zip \
    --output charon.zip
unzip charon.zip
rm -rf charon.zip
mv charon-28d543bfacc902ba9cc2a734b76baae9583892a4/ charon

curl -L https://github.com/FStarLang/karamel/archive/15d4bce74a2d43e34a64f48f8311b7d9bcb0e152.zip \
    --output karamel.zip
unzip karamel.zip
rm -rf karamel.zip
mv karamel-15d4bce74a2d43e34a64f48f8311b7d9bcb0e152/ karamel

curl -L https://github.com/AeneasVerif/eurydice/archive/1a65dbf3758fe310833718c645a64266294a29ac.zip \
    --output eurydice.zip
unzip eurydice.zip
rm -rf eurydice.zip
mv eurydice-1a65dbf3758fe310833718c645a64266294a29ac/ eurydice

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
