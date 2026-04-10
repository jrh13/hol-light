FROM ubuntu:22.04

ARG DEBIAN_FRONTEND=noninteractive
ARG OCAML_VERSION=4.14.0
ARG CAMLP5_VERSION=8.03.00

# System dependencies
RUN apt-get update && apt-get install -y \
    build-essential \
    git \
    expect \
    opam \
    m4 \
    pkg-config \
    libgmp-dev \
    xdot \
    curl \
    wget \
    sudo \
    software-properties-common \
    && rm -rf /var/lib/apt/lists/*

# Install Python 3.11
RUN add-apt-repository ppa:deadsnakes/ppa && \
    apt-get update && apt-get install -y \
    python3.11 \
    python3.11-venv \
    python3.11-dev \
    && rm -rf /var/lib/apt/lists/* && \
    update-alternatives --install /usr/bin/python3 python3 /usr/bin/python3.11 1

# Create non-root user (DMTCP works better as non-root)
RUN useradd -m -s /bin/bash hol && echo "hol ALL=(ALL) NOPASSWD:ALL" >> /etc/sudoers
USER hol
WORKDIR /home/hol

# Install uv (Python package manager for MCP server)
ENV PATH="/home/hol/.local/bin:${PATH}"
RUN curl -LsSf https://astral.sh/uv/install.sh | sh

# Install DMTCP from source
RUN git clone https://github.com/dmtcp/dmtcp.git /home/hol/dmtcp && \
    cd /home/hol/dmtcp && \
    ./configure --prefix=/usr/local && \
    make -j"$(nproc)" && \
    sudo make install && \
    rm -rf /home/hol/dmtcp

# Install OCaml via opam
RUN opam init --auto-setup --disable-sandboxing --yes && \
    opam switch create ${OCAML_VERSION} && \
    eval $(opam env) && \
    opam install -y camlp5.${CAMLP5_VERSION} zarith ocamlfind ledit ocamlformat && \
    opam clean -a -c -s --logs

# Activate opam env in .bashrc so every shell has it
RUN echo 'eval $(opam env)' >> /home/hol/.bashrc

# Set HOL Light environment
ENV HOLLIGHT_DIR=/home/hol/hol-light
WORKDIR /home/hol/hol-light

CMD ["bash"]
