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
# QECTutorial — light import surface for the hosted tutorial environment

This is the entry point used by the QCE26 tutorial environments (the
devcontainer in `.devcontainer/` and the lean4web instance in
`deploy/lean4web/`). It is *not* part of the library proper: `QEC.lean`
remains the umbrella that imports everything.

## Why a separate target

`import QEC` transitively pulls in `QEC.Stabilizer.Codes.BivariateBicycle`,
whose gross-code safe-floor leaves (`MImFloorY0/Y1/Y4`) each peak around
3.75 GB under `native_decide` — CI has to add 12 GB of swap to survive them
(see `.github/workflows/lean_action_ci.yml`). That is fine for a release
build on a dedicated runner and hopeless for a 4-core / 8 GB Codespace or a
shared web-editor session.

`BivariateBicycle` is a leaf: outside its own directory the only module that
imports it is the `QEC.Stabilizer.Codes` umbrella. So this file re-lists the
`Codes` umbrella minus that one import (and minus `_TEMPLATE`, which is
scaffolding rather than content) and is otherwise identical in reach to
`QEC`. Everything a tutorial attendee touches — the Pauli and binary-symplectic
layer, the stabilizer framework, the toric and rotated-surface codes, Steane,
Shor, `[[5,1,3]]`, and the concatenation instances — is still here.

## Keeping this in sync

`scripts/check-umbrellas.sh` only walks directories under `QEC/`, so this
root-level file is outside its remit and will not be flagged if it drifts.
The `tutorial-env` workflow builds this target on every push that touches
`QEC/`, which catches a module added to `Codes/` but not reflected here.

If you add a new heavy code family, exclude it here as well.
-/
