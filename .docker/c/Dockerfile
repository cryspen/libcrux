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
ENV KRML_REV=3275bf4ad9dc8c25965dc5da6122653fc43c4287
ENV EURYDICE_REV=46cef5d58a855ed049fa89bfe99c959b5d9d0d4b
ENV CHARON_REV=bb62a9b39db4ea8c6d536fe61b7d26663751bf3c
ENV PATH="${PATH}:$HOME/fstar/bin:$HOME/z3/bin"

# Setup & install.
ADD install.sh /tmp/install.sh
RUN bash /tmp/install.sh
ADD ext-tools.sh /tmp/ext-tools.sh
RUN bash /tmp/ext-tools.sh
