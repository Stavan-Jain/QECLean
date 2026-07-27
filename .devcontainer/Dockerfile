# Mirrors mathlib4's devcontainer image: a plain Ubuntu devcontainer base with
# elan installed but no toolchain baked in. The toolchain is resolved from the
# repo's `lean-toolchain` on first `lake` invocation, so this image does not go
# stale when the project bumps Lean.
FROM mcr.microsoft.com/devcontainers/base:ubuntu

USER vscode
WORKDIR /home/vscode

RUN curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain none

ENV PATH="/home/vscode/.elan/bin:${PATH}"
