#!/usr/bin/env bash

set -v -e -x

source $HOME/.profile

curl -L https://github.com/AeneasVerif/charon/archive/db4e045d4597d06d854ce7a2c10e8dcfda6ecd25.zip \
    --output charon.zip
unzip charon.zip
rm -rf charon.zip
mv charon-db4e045d4597d06d854ce7a2c10e8dcfda6ecd25/ charon

curl -L https://github.com/FStarLang/karamel/archive/3823e3d82fa0b271d799b61c59ffb4742ddc1e65.zip \
    --output karamel.zip
unzip karamel.zip
rm -rf karamel.zip
mv karamel-3823e3d82fa0b271d799b61c59ffb4742ddc1e65/ karamel

curl -L https://github.com/AeneasVerif/eurydice/archive/83ab5654d49df0603797bf510475d52d67ca24d8.zip \
    --output eurydice.zip
unzip eurydice.zip
rm -rf eurydice.zip
mv eurydice-83ab5654d49df0603797bf510475d52d67ca24d8/ eurydice

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
ln -s $CHARON_HOME charon
rm -f krml
ln -s $KRML_HOME/lib krml
cd ../
make -j
cd ../
