#!/usr/bin/env bash
# Devcontainer / Codespace provisioning for QECLean.
#
# Three steps, in this order for a reason:
#   1. install the toolchain pinned in `lean-toolchain`
#   2. pull mathlib's prebuilt oleans from the cache (never build mathlib)
#   3. build `QECLight`, the library minus the BivariateBicycle leaves
#
# Step 3 is the one that would OOM if it were a plain `lake build`: the
# gross-code safe-floor leaves peak ~3.75 GB each under `native_decide` and CI
# only survives them by adding 12 GB of swap. See QECLight.lean.
set -euo pipefail

cd "$(dirname "$0")/.."

echo "==> Installing Lean toolchain ($(cat lean-toolchain))"
elan toolchain install "$(cat lean-toolchain)"
elan override set "$(cat lean-toolchain)"

echo "==> Fetching mathlib cache"
# `cache` ships with mathlib; lake builds that one small exe first, then this
# downloads mathlib's oleans instead of compiling them (~hours saved).
lake exe cache get

echo "==> Building QECLight"
lake build QECLight

echo "==> Ready. Open Playground.lean to begin."
