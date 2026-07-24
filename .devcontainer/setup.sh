#!/usr/bin/env bash
# Codespace / devcontainer provisioning for the QCE26 tutorial.
#
# Three steps, in this order for a reason:
#   1. install the toolchain pinned in `lean-toolchain`
#   2. pull mathlib's prebuilt oleans from the cache (never build mathlib)
#   3. build only `QECTutorial`, which excludes the BivariateBicycle leaves
#
# Step 3 is the one that would OOM if it were `lake build`: the gross-code
# safe-floor leaves peak ~3.75 GB each under `native_decide` and CI only
# survives them by adding 12 GB of swap. See QECTutorial.lean.
set -euo pipefail

cd "$(dirname "$0")/.."

echo "==> Installing Lean toolchain ($(cat lean-toolchain))"
elan toolchain install "$(cat lean-toolchain)"
elan override set "$(cat lean-toolchain)"

echo "==> Fetching mathlib cache"
# `cache` ships with mathlib; lake builds that one small exe first, then this
# downloads mathlib's oleans instead of compiling them (~hours saved).
lake exe cache get

echo "==> Building tutorial target (QECTutorial)"
lake build QECTutorial

echo "==> Ready. Open Scratch.lean to begin."
