#!/usr/bin/env bash

set -v -e -x

source $HOME/.profile

curl -L https://github.com/AeneasVerif/charon/archive/b351338f6a84c7a1afc27433eb0ffdc668b3581d.zip \
    --output charon.zip
unzip charon.zip
rm -rf charon.zip
mv charon-b351338f6a84c7a1afc27433eb0ffdc668b3581d/ charon

curl -L https://github.com/FStarLang/karamel/archive/c96fb69d15693284644d6aecaa90afa37e4de8f0.zip \
    --output karamel.zip
unzip karamel.zip
rm -rf karamel.zip
mv karamel-c96fb69d15693284644d6aecaa90afa37e4de8f0/ karamel

curl -L https://github.com/AeneasVerif/eurydice/archive/7efec1624422fd5e94388ef06b9c76dfe7a48d46.zip \
    --output eurydice.zip
unzip eurydice.zip
rm -rf eurydice.zip
mv eurydice-7efec1624422fd5e94388ef06b9c76dfe7a48d46/ eurydice

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
