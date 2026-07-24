#!/usr/bin/env bash
# Invoked by lean4web's `npm run build:server` for this project.
#
# Builds ONLY `QECTutorial`, never the default target: a plain `lake build`
# would pull in the BivariateBicycle safe-floor leaves (~3.75 GB each under
# `native_decide`) and take the box down. See QECTutorial.lean.
set -euo pipefail

cd "$(dirname "$0")"

elan toolchain install "$(cat lean-toolchain)"
lake exe cache get
lake build QECTutorial
