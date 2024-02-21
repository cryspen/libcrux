# This Dockerfile should be run from this directory
# `docker build . -t franziskus/libcrux-c`

FROM ubuntu:24.04
LABEL maintainer="Franziskus Kiefer <franziskuskiefer@gmail.com>"

ENV SHELL /bin/bash
ENV USER user
ENV LOGNAME $USER
ENV HOME /home/$USER
ENV LANG en_US.UTF-8
ENV LC_ALL $LANG
ENV PATH="$HOME/.cargo/bin:${PATH}"

# Install dependencies.
ADD setup.sh /tmp/setup.sh
RUN bash /tmp/setup.sh

WORKDIR $HOME
USER $USER
COPY --chown=$USER:$USER . $HOME/$USER

# Setup & install.
ADD lang-setup.sh /tmp/lang-setup.sh
RUN bash /tmp/lang-setup.sh

ADD install.sh /tmp/install.sh
RUN bash /tmp/install.sh
