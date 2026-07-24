import QEC.Foundations.Foundations
import QEC.RepetitionCode.RepetitionCode
import QEC.Stabilizer.Foundations
import QEC.Stabilizer.Geometry
import QEC.Stabilizer.Framework
import QEC.Stabilizer.Codes.Toric
import QEC.Stabilizer.Codes.RotatedSurface
import QEC.Stabilizer.Codes.Repetition
import QEC.Stabilizer.Codes.Iceberg
import QEC.Stabilizer.Codes.Small
import QEC.Stabilizer.Codes.Concat

/-!
# QECLight — the library minus the memory-heavy code families

An import surface for environments that cannot afford the full build:
Codespaces, the hosted web editor (see `deploy/`), a laptop with 8 GB, or
anyone who wants to explore the stabilizer development without waiting on the
bivariate-bicycle proofs.

`QEC.lean` remains the umbrella that imports everything. This is a strict
subset, not a replacement, and it is deliberately absent from `defaultTargets`
so `lake build` still means the whole library.

## What is left out, and why

`import QEC` transitively pulls in `QEC.Stabilizer.Codes.BivariateBicycle`,
whose gross-code safe-floor leaves (`MImFloorY0/Y1/Y4`) each peak around
3.75 GB under `native_decide` — `.github/workflows/lean_action_ci.yml` has to
add 12 GB of swap to get through them. That is a reasonable price for a
release build on a dedicated runner, and prohibitive for a 4-core container or
a shared server hosting many concurrent sessions.

`BivariateBicycle` is a leaf: outside its own directory, the only module that
imports it is the `QEC.Stabilizer.Codes` umbrella. So this file re-lists that
umbrella without it (and without `_TEMPLATE`, which is scaffolding rather than
content). That drops 47 of the library's 59 `native_decide` files.

Everything else is here: the Pauli and binary-symplectic layer, the stabilizer
and homological framework, the toric and rotated-surface families, Steane,
Shor, `[[5,1,3]]`, and the concatenation instances.

## Keeping this in sync

`scripts/check-umbrellas.sh` only walks directories under `QEC/`, so this
root-level file is outside its remit and will not be flagged if it drifts from
the `Codes` umbrella. The `hosted-env` workflow builds this target on every
change under `QEC/`, which is what catches a module added to `Codes/` but not
reflected here.

If a new code family turns out to be similarly expensive, exclude it here too.
-/
