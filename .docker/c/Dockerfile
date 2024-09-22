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

# Setup & install.
ADD install.sh /tmp/install.sh
RUN bash /tmp/install.sh
ADD ext-tools.sh /tmp/ext-tools.sh
RUN bash /tmp/ext-tools.sh

ENV FSTAR_HOME=$HOME/fstar
ENV HACL_HOME=$HOME/hacl-star
ENV KRML_HOME=$HOME/karamel
ENV EURYDICE_HOME=$HOME/eurydice
ENV CHARON_HOME=$HOME/charon
ENV PATH="${PATH}:$HOME/fstar/bin:$HOME/z3/bin"
