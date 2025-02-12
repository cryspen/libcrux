# This Dockerfile should be run from this directory
# `docker build . -t franziskus/libcrux-c`

FROM ubuntu:24.04
LABEL maintainer="Franziskus Kiefer <franziskuskiefer@gmail.com>"

ENV SHELL=/bin/bash
ENV USER=user
ENV LOGNAME=$USER
ENV HOME=/home/$USER
ENV LANG=en_US.UTF-8
ENV LC_ALL=$LANG
ENV PATH="$HOME/.cargo/bin:${PATH}"

# Install dependencies.
ADD setup.sh /tmp/setup.sh
RUN bash /tmp/setup.sh

WORKDIR $HOME
USER $USER
COPY --chown=$USER:$USER . $HOME/$USER

ENV FSTAR_HOME=$HOME/fstar
ENV HACL_HOME=$HOME/hacl-star
ENV KRML_HOME=$HOME/karamel
ENV EURYDICE_HOME=$HOME/eurydice
ENV CHARON_HOME=$HOME/charon
ENV KRML_REV=97a06e07e7e423df192c40d5a88bf6c85fd4d278
ENV EURYDICE_REV=b8ea420ccde8db516ced5db9c097d77fa558fb94
ENV CHARON_REV=30cab88265206f4fa849736e704983e39a404d96
ENV PATH="${PATH}:$HOME/fstar/bin:$HOME/z3/bin"

# Setup & install.
ADD install.sh /tmp/install.sh
RUN bash /tmp/install.sh
ADD ext-tools.sh /tmp/ext-tools.sh
RUN bash /tmp/ext-tools.sh
