#!/usr/bin/env bash

set -v -e -x

source $HOME/.profile

KRML_REV=97a06e07e7e423df192c40d5a88bf6c85fd4d278
EURYDICE_REV=b8ea420ccde8db516ced5db9c097d77fa558fb94
CHARON_REV=30cab88265206f4fa849736e704983e39a404d96

curl -L https://github.com/AeneasVerif/charon/archive/$CHARON_REV.zip \
    --output charon.zip
unzip charon.zip
rm -rf charon.zip
mv charon-$CHARON_REV/ charon

curl -L https://github.com/FStarLang/karamel/archive/$KRML_REV.zip \
    --output karamel.zip
unzip karamel.zip
rm -rf karamel.zip
mv karamel-$KRML_REV/ karamel

curl -L https://github.com/AeneasVerif/eurydice/archive/$EURYDICE_REV.zip \
    --output eurydice.zip
unzip eurydice.zip
rm -rf eurydice.zip
mv eurydice-$EURYDICE_REV/ eurydice

echo "export KRML_HOME=$HOME/karamel" >>$HOME/.profile
echo "export EURYDICE_HOME=$HOME/eurydice" >>$HOME/.profile
echo "export CHARON_HOME=$HOME/charon" >>$HOME/.profile

echo "export KRML_REV=$KRML_REV" >>$HOME/.profile
echo "export EURYDICE_REV=$EURYDICE_REV" >>$HOME/.profile
echo "export CHARON_REV=$CHARON_REV" >>$HOME/.profile

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
ln -s $CHARON_HOME charon
rm -f krml
ln -s $KRML_HOME/lib krml
cd ../
make -j
cd ../
