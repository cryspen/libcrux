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
ENV KRML_REV=354791911c6b40d15a41cda7a0e3560da1cf31a1
ENV EURYDICE_REV=657e10870ab75432c50542cf5d9ec94e640c528d
ENV CHARON_REV=d02f05ccb8b90d1312b8caa446003ba9f6ad13a0
ENV PATH="${PATH}:$HOME/fstar/bin:$HOME/z3/bin"

# Setup & install.
ADD install.sh /tmp/install.sh
RUN bash /tmp/install.sh
ADD ext-tools.sh /tmp/ext-tools.sh
RUN bash /tmp/ext-tools.sh
