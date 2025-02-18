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
ENV KRML_REV=1d81d757d5d9e16dd6463ccc72324e587c707959
ENV EURYDICE_REV=788c5abefac3a9c7f79abae6a30fa8558e39764c
ENV CHARON_REV=a8f2211d1b95e0462a96382023b164a4116c7ca4
ENV PATH="${PATH}:$HOME/fstar/bin:$HOME/z3/bin"

# Setup & install.
ADD install.sh /tmp/install.sh
RUN bash /tmp/install.sh
ADD ext-tools.sh /tmp/ext-tools.sh
RUN bash /tmp/ext-tools.sh
