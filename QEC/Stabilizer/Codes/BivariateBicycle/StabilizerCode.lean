/-
# The gross BB code as a `StabilizerCode 144 12`, with `HasCodeDistance`

Phase 5 of the gross `[[144, 12, 12]]` formalization: package
`grossComplex` (the `bbChainComplex grossA grossB` from `Defs.lean`) as a
genuine `StabilizerCode 144 12`, and transport the Phase-2 (`≥ 6`,
unconditional) and Phase-4 (`= 12`, conditional on the two CRT-engine Props)
distance theorems — stated against `grossComplex.homologicalStabilizerGroup`
— onto the packaged `HasCodeDistance` predicate via
`IsNontrivialLogicalOperator_of_toSubgroup_eq`.

This file embeds offline-validated `𝔽₂` linear-algebra data
(`experiments/bb_lab/phase5/`, `data.json`):
* `dropSet` — 6 faces / 6 vertices dropped to trim 144 generators to 132;
* `redP2` / `redCM` — reduced bases of `ker ∂₂` / `ker cutMap` (6 each),
  satisfying `redP2 j (dropSet i) = [i=j]`, giving both the closure relations
  and the independence kernel-collapse;
* `phiX` / `phiZ` — left-inverse "syndrome decoder" certificates proving the
  trimmed rows are independent (no rank theorem; see `decoder_identity_*`);
* `logX` / `logZ` — a symplectic basis of 12 X-cycles + 12 Z-dual-cycles
  with identity `12×12` intersection matrix (the 12 logical qubits).

Status: WIP skeleton. The two `native_decide` decoder identities (the
independence hard-core) are proven; the framework wiring is `sorry`-stubbed.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.BaseDistance
import QEC.Stabilizer.Codes.BivariateBicycle.SafeSector
import QEC.Stabilizer.Framework.Homological.LogicalCorrespondence
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance
import Mathlib.Data.List.GetD

namespace Quantum.Stabilizer.Homological.BB

open scoped BigOperators
open Quantum.Stabilizer.Homological NQubitPauliGroupElement

/-! ## §1  Offline-validated data (see `experiments/bb_lab/phase5/data.json`) -/

/-- The 6 faces / 6 vertices dropped to trim 144 generators down to 132. -/
def dropSet : List GrossGroup := [((0 : ZMod 12), (0 : ZMod 6)), ((0 : ZMod 12), (1 : ZMod 6)),
  ((0 : ZMod 12), (2 : ZMod 6)), ((0 : ZMod 12), (3 : ZMod 6)), ((1 : ZMod 12), (0 : ZMod 6)),
  ((1 : ZMod 12), (1 : ZMod 6))]

/-- Reduced `ker ∂₂` basis (6 face-supports). `∂₂(redP2 j) = 0` and
`(redP2 j)(dropSet i) = [i=j]`. -/
def redP2 : List (List GrossGroup) := [[((0 : ZMod 12), (0 : ZMod 6)), ((0 : ZMod 12),
  (4 : ZMod 6)), ((1 : ZMod 12), (2 : ZMod 6)), ((1 : ZMod 12), (4 : ZMod 6)), ((2 : ZMod 12),
  (3 : ZMod 6)), ((2 : ZMod 12), (5 : ZMod 6)), ((3 : ZMod 12), (0 : ZMod 6)), ((3 : ZMod 12),
  (1 : ZMod 6)), ((3 : ZMod 12), (2 : ZMod 6)), ((3 : ZMod 12), (5 : ZMod 6)), ((4 : ZMod 12),
  (0 : ZMod 6)), ((4 : ZMod 12), (3 : ZMod 6)), ((4 : ZMod 12), (4 : ZMod 6)), ((4 : ZMod 12),
  (5 : ZMod 6)), ((5 : ZMod 12), (0 : ZMod 6)), ((5 : ZMod 12), (1 : ZMod 6)), ((5 : ZMod 12),
  (4 : ZMod 6)), ((5 : ZMod 12), (5 : ZMod 6)), ((6 : ZMod 12), (0 : ZMod 6)), ((6 : ZMod 12),
  (4 : ZMod 6)), ((7 : ZMod 12), (2 : ZMod 6)), ((7 : ZMod 12), (4 : ZMod 6)), ((8 : ZMod 12),
  (3 : ZMod 6)), ((8 : ZMod 12), (5 : ZMod 6)), ((9 : ZMod 12), (0 : ZMod 6)), ((9 : ZMod 12),
  (1 : ZMod 6)), ((9 : ZMod 12), (2 : ZMod 6)), ((9 : ZMod 12), (5 : ZMod 6)), ((10 : ZMod 12),
  (0 : ZMod 6)), ((10 : ZMod 12), (3 : ZMod 6)), ((10 : ZMod 12), (4 : ZMod 6)), ((10 : ZMod 12),
  (5 : ZMod 6)), ((11 : ZMod 12), (0 : ZMod 6)), ((11 : ZMod 12), (1 : ZMod 6)), ((11 : ZMod 12),
  (4 : ZMod 6)), ((11 : ZMod 12), (5 : ZMod 6))], [((0 : ZMod 12), (1 : ZMod 6)), ((0 : ZMod 12),
  (5 : ZMod 6)), ((1 : ZMod 12), (3 : ZMod 6)), ((1 : ZMod 12), (5 : ZMod 6)), ((2 : ZMod 12),
  (0 : ZMod 6)), ((2 : ZMod 12), (4 : ZMod 6)), ((3 : ZMod 12), (0 : ZMod 6)), ((3 : ZMod 12),
  (1 : ZMod 6)), ((3 : ZMod 12), (2 : ZMod 6)), ((3 : ZMod 12), (3 : ZMod 6)), ((4 : ZMod 12),
  (0 : ZMod 6)), ((4 : ZMod 12), (1 : ZMod 6)), ((4 : ZMod 12), (4 : ZMod 6)), ((4 : ZMod 12),
  (5 : ZMod 6)), ((5 : ZMod 12), (0 : ZMod 6)), ((5 : ZMod 12), (1 : ZMod 6)), ((5 : ZMod 12),
  (2 : ZMod 6)), ((5 : ZMod 12), (5 : ZMod 6)), ((6 : ZMod 12), (1 : ZMod 6)), ((6 : ZMod 12),
  (5 : ZMod 6)), ((7 : ZMod 12), (3 : ZMod 6)), ((7 : ZMod 12), (5 : ZMod 6)), ((8 : ZMod 12),
  (0 : ZMod 6)), ((8 : ZMod 12), (4 : ZMod 6)), ((9 : ZMod 12), (0 : ZMod 6)), ((9 : ZMod 12),
  (1 : ZMod 6)), ((9 : ZMod 12), (2 : ZMod 6)), ((9 : ZMod 12), (3 : ZMod 6)), ((10 : ZMod 12),
  (0 : ZMod 6)), ((10 : ZMod 12), (1 : ZMod 6)), ((10 : ZMod 12), (4 : ZMod 6)), ((10 : ZMod 12),
  (5 : ZMod 6)), ((11 : ZMod 12), (0 : ZMod 6)), ((11 : ZMod 12), (1 : ZMod 6)), ((11 : ZMod 12),
  (2 : ZMod 6)), ((11 : ZMod 12), (5 : ZMod 6))], [((0 : ZMod 12), (2 : ZMod 6)), ((0 : ZMod 12),
  (4 : ZMod 6)), ((1 : ZMod 12), (3 : ZMod 6)), ((1 : ZMod 12), (5 : ZMod 6)), ((2 : ZMod 12),
  (0 : ZMod 6)), ((2 : ZMod 12), (1 : ZMod 6)), ((2 : ZMod 12), (2 : ZMod 6)), ((2 : ZMod 12),
  (5 : ZMod 6)), ((3 : ZMod 12), (0 : ZMod 6)), ((3 : ZMod 12), (3 : ZMod 6)), ((3 : ZMod 12),
  (4 : ZMod 6)), ((3 : ZMod 12), (5 : ZMod 6)), ((4 : ZMod 12), (0 : ZMod 6)), ((4 : ZMod 12),
  (1 : ZMod 6)), ((4 : ZMod 12), (4 : ZMod 6)), ((4 : ZMod 12), (5 : ZMod 6)), ((5 : ZMod 12),
  (0 : ZMod 6)), ((5 : ZMod 12), (4 : ZMod 6)), ((6 : ZMod 12), (2 : ZMod 6)), ((6 : ZMod 12),
  (4 : ZMod 6)), ((7 : ZMod 12), (3 : ZMod 6)), ((7 : ZMod 12), (5 : ZMod 6)), ((8 : ZMod 12),
  (0 : ZMod 6)), ((8 : ZMod 12), (1 : ZMod 6)), ((8 : ZMod 12), (2 : ZMod 6)), ((8 : ZMod 12),
  (5 : ZMod 6)), ((9 : ZMod 12), (0 : ZMod 6)), ((9 : ZMod 12), (3 : ZMod 6)), ((9 : ZMod 12),
  (4 : ZMod 6)), ((9 : ZMod 12), (5 : ZMod 6)), ((10 : ZMod 12), (0 : ZMod 6)), ((10 : ZMod 12),
  (1 : ZMod 6)), ((10 : ZMod 12), (4 : ZMod 6)), ((10 : ZMod 12), (5 : ZMod 6)), ((11 : ZMod 12),
  (0 : ZMod 6)), ((11 : ZMod 12), (4 : ZMod 6))], [((0 : ZMod 12), (3 : ZMod 6)), ((0 : ZMod 12),
  (5 : ZMod 6)), ((1 : ZMod 12), (2 : ZMod 6)), ((1 : ZMod 12), (3 : ZMod 6)), ((1 : ZMod 12),
  (4 : ZMod 6)), ((1 : ZMod 12), (5 : ZMod 6)), ((2 : ZMod 12), (1 : ZMod 6)), ((2 : ZMod 12),
  (5 : ZMod 6)), ((3 : ZMod 12), (0 : ZMod 6)), ((3 : ZMod 12), (1 : ZMod 6)), ((3 : ZMod 12),
  (4 : ZMod 6)), ((3 : ZMod 12), (5 : ZMod 6)), ((4 : ZMod 12), (1 : ZMod 6)), ((4 : ZMod 12),
  (3 : ZMod 6)), ((5 : ZMod 12), (0 : ZMod 6)), ((5 : ZMod 12), (1 : ZMod 6)), ((5 : ZMod 12),
  (2 : ZMod 6)), ((5 : ZMod 12), (3 : ZMod 6)), ((6 : ZMod 12), (3 : ZMod 6)), ((6 : ZMod 12),
  (5 : ZMod 6)), ((7 : ZMod 12), (2 : ZMod 6)), ((7 : ZMod 12), (3 : ZMod 6)), ((7 : ZMod 12),
  (4 : ZMod 6)), ((7 : ZMod 12), (5 : ZMod 6)), ((8 : ZMod 12), (1 : ZMod 6)), ((8 : ZMod 12),
  (5 : ZMod 6)), ((9 : ZMod 12), (0 : ZMod 6)), ((9 : ZMod 12), (1 : ZMod 6)), ((9 : ZMod 12),
  (4 : ZMod 6)), ((9 : ZMod 12), (5 : ZMod 6)), ((10 : ZMod 12), (1 : ZMod 6)), ((10 : ZMod 12),
  (3 : ZMod 6)), ((11 : ZMod 12), (0 : ZMod 6)), ((11 : ZMod 12), (1 : ZMod 6)), ((11 : ZMod 12),
  (2 : ZMod 6)), ((11 : ZMod 12), (3 : ZMod 6))], [((1 : ZMod 12), (0 : ZMod 6)), ((1 : ZMod 12),
  (2 : ZMod 6)), ((1 : ZMod 12), (3 : ZMod 6)), ((1 : ZMod 12), (5 : ZMod 6)), ((2 : ZMod 12),
  (0 : ZMod 6)), ((2 : ZMod 12), (2 : ZMod 6)), ((2 : ZMod 12), (3 : ZMod 6)), ((2 : ZMod 12),
  (5 : ZMod 6)), ((4 : ZMod 12), (0 : ZMod 6)), ((4 : ZMod 12), (2 : ZMod 6)), ((4 : ZMod 12),
  (3 : ZMod 6)), ((4 : ZMod 12), (5 : ZMod 6)), ((5 : ZMod 12), (0 : ZMod 6)), ((5 : ZMod 12),
  (2 : ZMod 6)), ((5 : ZMod 12), (3 : ZMod 6)), ((5 : ZMod 12), (5 : ZMod 6)), ((7 : ZMod 12),
  (0 : ZMod 6)), ((7 : ZMod 12), (2 : ZMod 6)), ((7 : ZMod 12), (3 : ZMod 6)), ((7 : ZMod 12),
  (5 : ZMod 6)), ((8 : ZMod 12), (0 : ZMod 6)), ((8 : ZMod 12), (2 : ZMod 6)), ((8 : ZMod 12),
  (3 : ZMod 6)), ((8 : ZMod 12), (5 : ZMod 6)), ((10 : ZMod 12), (0 : ZMod 6)), ((10 : ZMod 12),
  (2 : ZMod 6)), ((10 : ZMod 12), (3 : ZMod 6)), ((10 : ZMod 12), (5 : ZMod 6)), ((11 : ZMod 12),
  (0 : ZMod 6)), ((11 : ZMod 12), (2 : ZMod 6)), ((11 : ZMod 12), (3 : ZMod 6)), ((11 : ZMod 12),
  (5 : ZMod 6))], [((1 : ZMod 12), (1 : ZMod 6)), ((1 : ZMod 12), (2 : ZMod 6)), ((1 : ZMod 12),
  (4 : ZMod 6)), ((1 : ZMod 12), (5 : ZMod 6)), ((2 : ZMod 12), (1 : ZMod 6)), ((2 : ZMod 12),
  (2 : ZMod 6)), ((2 : ZMod 12), (4 : ZMod 6)), ((2 : ZMod 12), (5 : ZMod 6)), ((4 : ZMod 12),
  (1 : ZMod 6)), ((4 : ZMod 12), (2 : ZMod 6)), ((4 : ZMod 12), (4 : ZMod 6)), ((4 : ZMod 12),
  (5 : ZMod 6)), ((5 : ZMod 12), (1 : ZMod 6)), ((5 : ZMod 12), (2 : ZMod 6)), ((5 : ZMod 12),
  (4 : ZMod 6)), ((5 : ZMod 12), (5 : ZMod 6)), ((7 : ZMod 12), (1 : ZMod 6)), ((7 : ZMod 12),
  (2 : ZMod 6)), ((7 : ZMod 12), (4 : ZMod 6)), ((7 : ZMod 12), (5 : ZMod 6)), ((8 : ZMod 12),
  (1 : ZMod 6)), ((8 : ZMod 12), (2 : ZMod 6)), ((8 : ZMod 12), (4 : ZMod 6)), ((8 : ZMod 12),
  (5 : ZMod 6)), ((10 : ZMod 12), (1 : ZMod 6)), ((10 : ZMod 12), (2 : ZMod 6)), ((10 : ZMod 12),
  (4 : ZMod 6)), ((10 : ZMod 12), (5 : ZMod 6)), ((11 : ZMod 12), (1 : ZMod 6)), ((11 : ZMod 12),
  (2 : ZMod 6)), ((11 : ZMod 12), (4 : ZMod 6)), ((11 : ZMod 12), (5 : ZMod 6))]]

/-- Reduced `ker cutMap` basis (6 vertex-supports). -/
def redCM : List (List GrossGroup) := [[((0 : ZMod 12), (0 : ZMod 6)), ((0 : ZMod 12),
  (4 : ZMod 6)), ((1 : ZMod 12), (2 : ZMod 6)), ((1 : ZMod 12), (4 : ZMod 6)), ((2 : ZMod 12),
  (1 : ZMod 6)), ((2 : ZMod 12), (2 : ZMod 6)), ((2 : ZMod 12), (3 : ZMod 6)), ((2 : ZMod 12),
  (4 : ZMod 6)), ((3 : ZMod 12), (2 : ZMod 6)), ((3 : ZMod 12), (3 : ZMod 6)), ((3 : ZMod 12),
  (4 : ZMod 6)), ((3 : ZMod 12), (5 : ZMod 6)), ((4 : ZMod 12), (0 : ZMod 6)), ((4 : ZMod 12),
  (1 : ZMod 6)), ((4 : ZMod 12), (2 : ZMod 6)), ((4 : ZMod 12), (3 : ZMod 6)), ((5 : ZMod 12),
  (3 : ZMod 6)), ((5 : ZMod 12), (5 : ZMod 6)), ((6 : ZMod 12), (0 : ZMod 6)), ((6 : ZMod 12),
  (4 : ZMod 6)), ((7 : ZMod 12), (2 : ZMod 6)), ((7 : ZMod 12), (4 : ZMod 6)), ((8 : ZMod 12),
  (1 : ZMod 6)), ((8 : ZMod 12), (2 : ZMod 6)), ((8 : ZMod 12), (3 : ZMod 6)), ((8 : ZMod 12),
  (4 : ZMod 6)), ((9 : ZMod 12), (2 : ZMod 6)), ((9 : ZMod 12), (3 : ZMod 6)), ((9 : ZMod 12),
  (4 : ZMod 6)), ((9 : ZMod 12), (5 : ZMod 6)), ((10 : ZMod 12), (0 : ZMod 6)), ((10 : ZMod 12),
  (1 : ZMod 6)), ((10 : ZMod 12), (2 : ZMod 6)), ((10 : ZMod 12), (3 : ZMod 6)), ((11 : ZMod 12),
  (3 : ZMod 6)), ((11 : ZMod 12), (5 : ZMod 6))], [((0 : ZMod 12), (1 : ZMod 6)), ((0 : ZMod 12),
  (5 : ZMod 6)), ((1 : ZMod 12), (3 : ZMod 6)), ((1 : ZMod 12), (5 : ZMod 6)), ((2 : ZMod 12),
  (2 : ZMod 6)), ((2 : ZMod 12), (3 : ZMod 6)), ((2 : ZMod 12), (4 : ZMod 6)), ((2 : ZMod 12),
  (5 : ZMod 6)), ((3 : ZMod 12), (0 : ZMod 6)), ((3 : ZMod 12), (3 : ZMod 6)), ((3 : ZMod 12),
  (4 : ZMod 6)), ((3 : ZMod 12), (5 : ZMod 6)), ((4 : ZMod 12), (1 : ZMod 6)), ((4 : ZMod 12),
  (2 : ZMod 6)), ((4 : ZMod 12), (3 : ZMod 6)), ((4 : ZMod 12), (4 : ZMod 6)), ((5 : ZMod 12),
  (0 : ZMod 6)), ((5 : ZMod 12), (4 : ZMod 6)), ((6 : ZMod 12), (1 : ZMod 6)), ((6 : ZMod 12),
  (5 : ZMod 6)), ((7 : ZMod 12), (3 : ZMod 6)), ((7 : ZMod 12), (5 : ZMod 6)), ((8 : ZMod 12),
  (2 : ZMod 6)), ((8 : ZMod 12), (3 : ZMod 6)), ((8 : ZMod 12), (4 : ZMod 6)), ((8 : ZMod 12),
  (5 : ZMod 6)), ((9 : ZMod 12), (0 : ZMod 6)), ((9 : ZMod 12), (3 : ZMod 6)), ((9 : ZMod 12),
  (4 : ZMod 6)), ((9 : ZMod 12), (5 : ZMod 6)), ((10 : ZMod 12), (1 : ZMod 6)), ((10 : ZMod 12),
  (2 : ZMod 6)), ((10 : ZMod 12), (3 : ZMod 6)), ((10 : ZMod 12), (4 : ZMod 6)), ((11 : ZMod 12),
  (0 : ZMod 6)), ((11 : ZMod 12), (4 : ZMod 6))], [((0 : ZMod 12), (2 : ZMod 6)), ((0 : ZMod 12),
  (4 : ZMod 6)), ((1 : ZMod 12), (3 : ZMod 6)), ((1 : ZMod 12), (5 : ZMod 6)), ((2 : ZMod 12),
  (1 : ZMod 6)), ((2 : ZMod 12), (3 : ZMod 6)), ((3 : ZMod 12), (0 : ZMod 6)), ((3 : ZMod 12),
  (1 : ZMod 6)), ((3 : ZMod 12), (2 : ZMod 6)), ((3 : ZMod 12), (3 : ZMod 6)), ((4 : ZMod 12),
  (1 : ZMod 6)), ((4 : ZMod 12), (2 : ZMod 6)), ((4 : ZMod 12), (3 : ZMod 6)), ((4 : ZMod 12),
  (4 : ZMod 6)), ((5 : ZMod 12), (0 : ZMod 6)), ((5 : ZMod 12), (1 : ZMod 6)), ((5 : ZMod 12),
  (2 : ZMod 6)), ((5 : ZMod 12), (5 : ZMod 6)), ((6 : ZMod 12), (2 : ZMod 6)), ((6 : ZMod 12),
  (4 : ZMod 6)), ((7 : ZMod 12), (3 : ZMod 6)), ((7 : ZMod 12), (5 : ZMod 6)), ((8 : ZMod 12),
  (1 : ZMod 6)), ((8 : ZMod 12), (3 : ZMod 6)), ((9 : ZMod 12), (0 : ZMod 6)), ((9 : ZMod 12),
  (1 : ZMod 6)), ((9 : ZMod 12), (2 : ZMod 6)), ((9 : ZMod 12), (3 : ZMod 6)), ((10 : ZMod 12),
  (1 : ZMod 6)), ((10 : ZMod 12), (2 : ZMod 6)), ((10 : ZMod 12), (3 : ZMod 6)), ((10 : ZMod 12),
  (4 : ZMod 6)), ((11 : ZMod 12), (0 : ZMod 6)), ((11 : ZMod 12), (1 : ZMod 6)), ((11 : ZMod 12),
  (2 : ZMod 6)), ((11 : ZMod 12), (5 : ZMod 6))], [((0 : ZMod 12), (3 : ZMod 6)), ((0 : ZMod 12),
  (5 : ZMod 6)), ((1 : ZMod 12), (2 : ZMod 6)), ((1 : ZMod 12), (3 : ZMod 6)), ((1 : ZMod 12),
  (4 : ZMod 6)), ((1 : ZMod 12), (5 : ZMod 6)), ((2 : ZMod 12), (0 : ZMod 6)), ((2 : ZMod 12),
  (3 : ZMod 6)), ((2 : ZMod 12), (4 : ZMod 6)), ((2 : ZMod 12), (5 : ZMod 6)), ((3 : ZMod 12),
  (1 : ZMod 6)), ((3 : ZMod 12), (2 : ZMod 6)), ((3 : ZMod 12), (3 : ZMod 6)), ((3 : ZMod 12),
  (4 : ZMod 6)), ((4 : ZMod 12), (0 : ZMod 6)), ((4 : ZMod 12), (4 : ZMod 6)), ((5 : ZMod 12),
  (1 : ZMod 6)), ((5 : ZMod 12), (5 : ZMod 6)), ((6 : ZMod 12), (3 : ZMod 6)), ((6 : ZMod 12),
  (5 : ZMod 6)), ((7 : ZMod 12), (2 : ZMod 6)), ((7 : ZMod 12), (3 : ZMod 6)), ((7 : ZMod 12),
  (4 : ZMod 6)), ((7 : ZMod 12), (5 : ZMod 6)), ((8 : ZMod 12), (0 : ZMod 6)), ((8 : ZMod 12),
  (3 : ZMod 6)), ((8 : ZMod 12), (4 : ZMod 6)), ((8 : ZMod 12), (5 : ZMod 6)), ((9 : ZMod 12),
  (1 : ZMod 6)), ((9 : ZMod 12), (2 : ZMod 6)), ((9 : ZMod 12), (3 : ZMod 6)), ((9 : ZMod 12),
  (4 : ZMod 6)), ((10 : ZMod 12), (0 : ZMod 6)), ((10 : ZMod 12), (4 : ZMod 6)), ((11 : ZMod 12),
  (1 : ZMod 6)), ((11 : ZMod 12), (5 : ZMod 6))], [((1 : ZMod 12), (0 : ZMod 6)), ((1 : ZMod 12),
  (2 : ZMod 6)), ((1 : ZMod 12), (3 : ZMod 6)), ((1 : ZMod 12), (5 : ZMod 6)), ((2 : ZMod 12),
  (0 : ZMod 6)), ((2 : ZMod 12), (2 : ZMod 6)), ((2 : ZMod 12), (3 : ZMod 6)), ((2 : ZMod 12),
  (5 : ZMod 6)), ((4 : ZMod 12), (0 : ZMod 6)), ((4 : ZMod 12), (2 : ZMod 6)), ((4 : ZMod 12),
  (3 : ZMod 6)), ((4 : ZMod 12), (5 : ZMod 6)), ((5 : ZMod 12), (0 : ZMod 6)), ((5 : ZMod 12),
  (2 : ZMod 6)), ((5 : ZMod 12), (3 : ZMod 6)), ((5 : ZMod 12), (5 : ZMod 6)), ((7 : ZMod 12),
  (0 : ZMod 6)), ((7 : ZMod 12), (2 : ZMod 6)), ((7 : ZMod 12), (3 : ZMod 6)), ((7 : ZMod 12),
  (5 : ZMod 6)), ((8 : ZMod 12), (0 : ZMod 6)), ((8 : ZMod 12), (2 : ZMod 6)), ((8 : ZMod 12),
  (3 : ZMod 6)), ((8 : ZMod 12), (5 : ZMod 6)), ((10 : ZMod 12), (0 : ZMod 6)), ((10 : ZMod 12),
  (2 : ZMod 6)), ((10 : ZMod 12), (3 : ZMod 6)), ((10 : ZMod 12), (5 : ZMod 6)), ((11 : ZMod 12),
  (0 : ZMod 6)), ((11 : ZMod 12), (2 : ZMod 6)), ((11 : ZMod 12), (3 : ZMod 6)), ((11 : ZMod 12),
  (5 : ZMod 6))], [((1 : ZMod 12), (1 : ZMod 6)), ((1 : ZMod 12), (2 : ZMod 6)), ((1 : ZMod 12),
  (4 : ZMod 6)), ((1 : ZMod 12), (5 : ZMod 6)), ((2 : ZMod 12), (1 : ZMod 6)), ((2 : ZMod 12),
  (2 : ZMod 6)), ((2 : ZMod 12), (4 : ZMod 6)), ((2 : ZMod 12), (5 : ZMod 6)), ((4 : ZMod 12),
  (1 : ZMod 6)), ((4 : ZMod 12), (2 : ZMod 6)), ((4 : ZMod 12), (4 : ZMod 6)), ((4 : ZMod 12),
  (5 : ZMod 6)), ((5 : ZMod 12), (1 : ZMod 6)), ((5 : ZMod 12), (2 : ZMod 6)), ((5 : ZMod 12),
  (4 : ZMod 6)), ((5 : ZMod 12), (5 : ZMod 6)), ((7 : ZMod 12), (1 : ZMod 6)), ((7 : ZMod 12),
  (2 : ZMod 6)), ((7 : ZMod 12), (4 : ZMod 6)), ((7 : ZMod 12), (5 : ZMod 6)), ((8 : ZMod 12),
  (1 : ZMod 6)), ((8 : ZMod 12), (2 : ZMod 6)), ((8 : ZMod 12), (4 : ZMod 6)), ((8 : ZMod 12),
  (5 : ZMod 6)), ((10 : ZMod 12), (1 : ZMod 6)), ((10 : ZMod 12), (2 : ZMod 6)), ((10 : ZMod 12),
  (4 : ZMod 6)), ((10 : ZMod 12), (5 : ZMod 6)), ((11 : ZMod 12), (1 : ZMod 6)), ((11 : ZMod 12),
  (2 : ZMod 6)), ((11 : ZMod 12), (4 : ZMod 6)), ((11 : ZMod 12), (5 : ZMod 6))]]

/-- Face-independence syndrome decoder: support list of (output-coord, qubit). -/
def phiX : List (GrossGroup × (GrossGroup × Fin 2)) := [(((0 : ZMod 12), (4 : ZMod 6)),
  (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((0 : ZMod 12), (4 : ZMod 6)), (((3 : ZMod 12),
  (2 : ZMod 6)), (0 : Fin 2))), (((0 : ZMod 12), (4 : ZMod 6)), (((3 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((0 : ZMod 12), (4 : ZMod 6)), (((6 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((0 : ZMod 12), (4 : ZMod 6)), (((6 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((0 : ZMod 12),
  (4 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((0 : ZMod 12), (4 : ZMod 6)),
  (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((0 : ZMod 12), (4 : ZMod 6)), (((6 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((0 : ZMod 12), (4 : ZMod 6)), (((6 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((0 : ZMod 12), (5 : ZMod 6)), (((3 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((0 : ZMod 12), (5 : ZMod 6)), (((3 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((0 : ZMod 12),
  (5 : ZMod 6)), (((3 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((0 : ZMod 12), (5 : ZMod 6)),
  (((6 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((0 : ZMod 12), (5 : ZMod 6)), (((6 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((0 : ZMod 12), (5 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((0 : ZMod 12), (5 : ZMod 6)), (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((0 : ZMod 12), (5 : ZMod 6)), (((6 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((0 : ZMod 12),
  (5 : ZMod 6)), (((6 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (2 : ZMod 6)),
  (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (2 : ZMod 6)), (((4 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (2 : ZMod 6)), (((4 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((1 : ZMod 12), (2 : ZMod 6)), (((4 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((1 : ZMod 12), (2 : ZMod 6)), (((4 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12),
  (2 : ZMod 6)), (((4 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (2 : ZMod 6)),
  (((4 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12),
  (0 : ZMod 6)), (1 : Fin 2))), (((1 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)),
  (1 : Fin 2))), (((1 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((1 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12),
  (3 : ZMod 6)), (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (3 : ZMod 6)),
  (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (3 : ZMod 6)), (((3 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (3 : ZMod 6)), (((6 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((1 : ZMod 12), (3 : ZMod 6)), (((6 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((1 : ZMod 12), (3 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12),
  (3 : ZMod 6)), (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (3 : ZMod 6)),
  (((6 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (3 : ZMod 6)), (((6 : ZMod 12),
  (5 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (3 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)),
  (1 : Fin 2))), (((1 : ZMod 12), (3 : ZMod 6)), (((0 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))),
  (((1 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((1 : ZMod 12),
  (3 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((1 : ZMod 12), (4 : ZMod 6)),
  (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (4 : ZMod 6)), (((4 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (4 : ZMod 6)), (((4 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((1 : ZMod 12), (4 : ZMod 6)), (((4 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((1 : ZMod 12), (4 : ZMod 6)), (((7 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12),
  (4 : ZMod 6)), (((7 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (4 : ZMod 6)),
  (((7 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (4 : ZMod 6)), (((7 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (4 : ZMod 6)), (((7 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((1 : ZMod 12), (4 : ZMod 6)), (((7 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((1 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((1 : ZMod 12),
  (4 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((1 : ZMod 12), (5 : ZMod 6)),
  (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (5 : ZMod 6)), (((3 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((1 : ZMod 12), (5 : ZMod 6)), (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((1 : ZMod 12), (5 : ZMod 6)), (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12),
  (5 : ZMod 6)), (((4 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (5 : ZMod 6)),
  (((4 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (5 : ZMod 6)), (((4 : ZMod 12),
  (5 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (5 : ZMod 6)), (((6 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((1 : ZMod 12), (5 : ZMod 6)), (((6 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((1 : ZMod 12), (5 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12),
  (5 : ZMod 6)), (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (5 : ZMod 6)),
  (((6 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (5 : ZMod 6)), (((6 : ZMod 12),
  (5 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (5 : ZMod 6)), (((7 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((1 : ZMod 12), (5 : ZMod 6)), (((7 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((1 : ZMod 12), (5 : ZMod 6)), (((7 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12),
  (5 : ZMod 6)), (((7 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (5 : ZMod 6)),
  (((7 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (5 : ZMod 6)), (((7 : ZMod 12),
  (5 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)),
  (1 : Fin 2))), (((1 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))),
  (((1 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((1 : ZMod 12),
  (5 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((2 : ZMod 12), (0 : ZMod 6)),
  (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (0 : ZMod 6)), (((1 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (0 : ZMod 6)), (((1 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (0 : ZMod 6)), (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (0 : ZMod 6)), (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (0 : ZMod 6)), (((2 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (0 : ZMod 6)),
  (((2 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (0 : ZMod 6)), (((2 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (0 : ZMod 6)), (((3 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (0 : ZMod 6)), (((3 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (0 : ZMod 6)), (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (0 : ZMod 6)), (((3 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (0 : ZMod 6)),
  (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (0 : ZMod 6)), (((3 : ZMod 12),
  (5 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (0 : ZMod 6)), (((4 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (0 : ZMod 6)), (((4 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (0 : ZMod 6)), (((4 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (0 : ZMod 6)), (((5 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (0 : ZMod 6)),
  (((5 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (0 : ZMod 6)), (((5 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (0 : ZMod 6)), (((7 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (0 : ZMod 6)), (((7 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (0 : ZMod 6)), (((7 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (0 : ZMod 6)), (((7 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (0 : ZMod 6)),
  (((7 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (0 : ZMod 6)), (((7 : ZMod 12),
  (5 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (0 : ZMod 6)), (((8 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (0 : ZMod 6)), (((8 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (0 : ZMod 6)), (((8 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (0 : ZMod 6)), (((8 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (0 : ZMod 6)),
  (((8 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (0 : ZMod 6)), (((8 : ZMod 12),
  (5 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (0 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)),
  (1 : Fin 2))), (((2 : ZMod 12), (0 : ZMod 6)), (((0 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))),
  (((2 : ZMod 12), (0 : ZMod 6)), (((0 : ZMod 12), (2 : ZMod 6)), (1 : Fin 2))), (((2 : ZMod 12),
  (0 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2))), (((2 : ZMod 12), (1 : ZMod 6)),
  (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (1 : ZMod 6)), (((1 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (1 : ZMod 6)), (((1 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (1 : ZMod 6)), (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (1 : ZMod 6)), (((2 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (1 : ZMod 6)), (((2 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (1 : ZMod 6)),
  (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (1 : ZMod 6)), (((3 : ZMod 12),
  (2 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (1 : ZMod 6)), (((3 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (1 : ZMod 6)), (((4 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (1 : ZMod 6)), (((4 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (1 : ZMod 6)), (((4 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (1 : ZMod 6)),
  (((5 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (1 : ZMod 6)), (((5 : ZMod 12),
  (2 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (1 : ZMod 6)), (((5 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (1 : ZMod 6)), (((6 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (1 : ZMod 6)), (((6 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (1 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (1 : ZMod 6)),
  (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (1 : ZMod 6)), (((6 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (1 : ZMod 6)), (((6 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (1 : ZMod 6)), (((7 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (1 : ZMod 6)), (((7 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (1 : ZMod 6)), (((7 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (1 : ZMod 6)),
  (((7 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (1 : ZMod 6)), (((7 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (1 : ZMod 6)), (((7 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (1 : ZMod 6)), (((8 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (1 : ZMod 6)), (((8 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (1 : ZMod 6)), (((8 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (1 : ZMod 6)),
  (((8 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (1 : ZMod 6)), (((8 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (1 : ZMod 6)), (((8 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (1 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))),
  (((2 : ZMod 12), (1 : ZMod 6)), (((0 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((2 : ZMod 12),
  (1 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2))), (((2 : ZMod 12), (2 : ZMod 6)),
  (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (2 : ZMod 6)), (((2 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (2 : ZMod 6)), (((2 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (2 : ZMod 6)), (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (2 : ZMod 6)), (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (2 : ZMod 6)), (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (2 : ZMod 6)),
  (((4 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (2 : ZMod 6)), (((4 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (2 : ZMod 6)), (((4 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (2 : ZMod 6)), (((5 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (2 : ZMod 6)), (((5 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (2 : ZMod 6)), (((5 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (2 : ZMod 6)),
  (((6 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (2 : ZMod 6)), (((6 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (2 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (2 : ZMod 6)), (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (2 : ZMod 6)), (((6 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (2 : ZMod 6)), (((6 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (2 : ZMod 6)),
  (((7 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (2 : ZMod 6)), (((7 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (2 : ZMod 6)), (((7 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (2 : ZMod 6)), (((7 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (2 : ZMod 6)), (((7 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (2 : ZMod 6)), (((7 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (2 : ZMod 6)),
  (((8 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (2 : ZMod 6)), (((8 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (2 : ZMod 6)), (((8 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (2 : ZMod 6)), (((8 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (2 : ZMod 6)), (((8 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (2 : ZMod 6)), (((8 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (2 : ZMod 6)),
  (((0 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((2 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12),
  (0 : ZMod 6)), (1 : Fin 2))), (((2 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (3 : ZMod 6)), (((2 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (3 : ZMod 6)), (((2 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (3 : ZMod 6)),
  (((3 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (3 : ZMod 6)), (((3 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (3 : ZMod 6)), (((3 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (3 : ZMod 6)), (((4 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (3 : ZMod 6)), (((4 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (3 : ZMod 6)), (((4 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (3 : ZMod 6)),
  (((5 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (3 : ZMod 6)), (((5 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (3 : ZMod 6)), (((5 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (3 : ZMod 6)), (((6 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (3 : ZMod 6)), (((6 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (3 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (3 : ZMod 6)),
  (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (3 : ZMod 6)), (((6 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (3 : ZMod 6)), (((6 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (3 : ZMod 6)), (((7 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (3 : ZMod 6)), (((7 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (3 : ZMod 6)), (((7 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (3 : ZMod 6)),
  (((7 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (3 : ZMod 6)), (((7 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (3 : ZMod 6)), (((7 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (3 : ZMod 6)), (((8 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (3 : ZMod 6)), (((8 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (3 : ZMod 6)), (((8 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (3 : ZMod 6)),
  (((8 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (3 : ZMod 6)), (((8 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (3 : ZMod 6)), (((8 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (3 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))),
  (((2 : ZMod 12), (3 : ZMod 6)), (((0 : ZMod 12), (2 : ZMod 6)), (1 : Fin 2))), (((2 : ZMod 12),
  (3 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((2 : ZMod 12), (3 : ZMod 6)),
  (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((2 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (4 : ZMod 6)), (((2 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (4 : ZMod 6)), (((2 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (4 : ZMod 6)),
  (((3 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (4 : ZMod 6)), (((3 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (4 : ZMod 6)), (((3 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (4 : ZMod 6)), (((4 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (4 : ZMod 6)), (((4 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (4 : ZMod 6)), (((4 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (4 : ZMod 6)),
  (((4 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (4 : ZMod 6)), (((4 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (4 : ZMod 6)), (((4 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (4 : ZMod 6)), (((5 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (4 : ZMod 6)), (((5 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (4 : ZMod 6)), (((5 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (4 : ZMod 6)),
  (((6 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (4 : ZMod 6)), (((6 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (4 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (4 : ZMod 6)), (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (4 : ZMod 6)), (((6 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (4 : ZMod 6)), (((6 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (4 : ZMod 6)),
  (((8 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (4 : ZMod 6)), (((8 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (4 : ZMod 6)), (((8 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (4 : ZMod 6)), (((8 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (4 : ZMod 6)), (((8 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (4 : ZMod 6)), (((8 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (4 : ZMod 6)),
  (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((2 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12),
  (2 : ZMod 6)), (1 : Fin 2))), (((2 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)),
  (1 : Fin 2))), (((2 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))),
  (((2 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (5 : ZMod 6)), (((1 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (5 : ZMod 6)),
  (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (5 : ZMod 6)), (((2 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (5 : ZMod 6)), (((2 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (5 : ZMod 6)), (((2 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (5 : ZMod 6)), (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (5 : ZMod 6)), (((3 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (5 : ZMod 6)),
  (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (5 : ZMod 6)), (((3 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (5 : ZMod 6)), (((3 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (5 : ZMod 6)), (((3 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (5 : ZMod 6)), (((4 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (5 : ZMod 6)), (((4 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (5 : ZMod 6)),
  (((4 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (5 : ZMod 6)), (((4 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (5 : ZMod 6)), (((4 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (5 : ZMod 6)), (((4 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (5 : ZMod 6)), (((5 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (5 : ZMod 6)), (((5 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (5 : ZMod 6)),
  (((5 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (5 : ZMod 6)), (((8 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (5 : ZMod 6)), (((8 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (5 : ZMod 6)), (((8 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (5 : ZMod 6)), (((8 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (5 : ZMod 6)), (((8 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (5 : ZMod 6)),
  (((8 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12),
  (1 : ZMod 6)), (1 : Fin 2))), (((2 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (2 : ZMod 6)),
  (1 : Fin 2))), (((2 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2))),
  (((2 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((2 : ZMod 12),
  (5 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((3 : ZMod 12), (0 : ZMod 6)),
  (((0 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (0 : ZMod 6)), (((0 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (0 : ZMod 6)), (((3 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((3 : ZMod 12), (0 : ZMod 6)), (((3 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((3 : ZMod 12), (0 : ZMod 6)), (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12),
  (0 : ZMod 6)), (((3 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (0 : ZMod 6)),
  (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (0 : ZMod 6)), (((9 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (0 : ZMod 6)), (((9 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((3 : ZMod 12), (1 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((3 : ZMod 12), (1 : ZMod 6)), (((0 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12),
  (1 : ZMod 6)), (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (1 : ZMod 6)),
  (((3 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (1 : ZMod 6)), (((3 : ZMod 12),
  (2 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (1 : ZMod 6)), (((3 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((3 : ZMod 12), (1 : ZMod 6)), (((3 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((3 : ZMod 12), (1 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12),
  (1 : ZMod 6)), (((9 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (1 : ZMod 6)),
  (((9 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((3 : ZMod 12), (2 : ZMod 6)), (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((3 : ZMod 12), (2 : ZMod 6)), (((3 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12),
  (2 : ZMod 6)), (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (2 : ZMod 6)),
  (((3 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (2 : ZMod 6)), (((3 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (2 : ZMod 6)), (((3 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((3 : ZMod 12), (2 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((3 : ZMod 12), (2 : ZMod 6)), (((9 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12),
  (2 : ZMod 6)), (((9 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (3 : ZMod 6)),
  (((0 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (3 : ZMod 6)), (((0 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (3 : ZMod 6)), (((3 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((3 : ZMod 12), (3 : ZMod 6)), (((3 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((3 : ZMod 12), (3 : ZMod 6)), (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12),
  (3 : ZMod 6)), (((3 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (3 : ZMod 6)),
  (((6 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (3 : ZMod 6)), (((6 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (3 : ZMod 6)), (((6 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((3 : ZMod 12), (3 : ZMod 6)), (((6 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))),
  (((3 : ZMod 12), (3 : ZMod 6)), (((6 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12),
  (3 : ZMod 6)), (((9 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (3 : ZMod 6)),
  (((9 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((3 : ZMod 12), (4 : ZMod 6)), (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))),
  (((3 : ZMod 12), (4 : ZMod 6)), (((3 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12),
  (4 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (4 : ZMod 6)),
  (((9 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (4 : ZMod 6)), (((9 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((3 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))),
  (((3 : ZMod 12), (5 : ZMod 6)), (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12),
  (5 : ZMod 6)), (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (5 : ZMod 6)),
  (((3 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (5 : ZMod 6)), (((6 : ZMod 12),
  (2 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (5 : ZMod 6)), (((9 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((3 : ZMod 12), (5 : ZMod 6)), (((9 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((4 : ZMod 12), (0 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12),
  (0 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (0 : ZMod 6)),
  (((1 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (0 : ZMod 6)), (((3 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (0 : ZMod 6)), (((3 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((4 : ZMod 12), (0 : ZMod 6)), (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))),
  (((4 : ZMod 12), (0 : ZMod 6)), (((4 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12),
  (0 : ZMod 6)), (((4 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (0 : ZMod 6)),
  (((6 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (0 : ZMod 6)), (((6 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (0 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((4 : ZMod 12), (0 : ZMod 6)), (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((4 : ZMod 12), (0 : ZMod 6)), (((6 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12),
  (0 : ZMod 6)), (((6 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (0 : ZMod 6)),
  (((7 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (0 : ZMod 6)), (((10 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (0 : ZMod 6)), (((10 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((4 : ZMod 12), (0 : ZMod 6)), (((0 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))),
  (((4 : ZMod 12), (0 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((4 : ZMod 12),
  (1 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (1 : ZMod 6)),
  (((1 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (1 : ZMod 6)), (((3 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (1 : ZMod 6)), (((3 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((4 : ZMod 12), (1 : ZMod 6)), (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))),
  (((4 : ZMod 12), (1 : ZMod 6)), (((4 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12),
  (1 : ZMod 6)), (((4 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (1 : ZMod 6)),
  (((4 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (1 : ZMod 6)), (((4 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (1 : ZMod 6)), (((4 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((4 : ZMod 12), (1 : ZMod 6)), (((6 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((4 : ZMod 12), (1 : ZMod 6)), (((6 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12),
  (1 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (1 : ZMod 6)),
  (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (1 : ZMod 6)), (((6 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (1 : ZMod 6)), (((6 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((4 : ZMod 12), (1 : ZMod 6)), (((7 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((4 : ZMod 12), (1 : ZMod 6)), (((10 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12),
  (1 : ZMod 6)), (((10 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (1 : ZMod 6)),
  (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((4 : ZMod 12), (1 : ZMod 6)), (((0 : ZMod 12),
  (1 : ZMod 6)), (1 : Fin 2))), (((4 : ZMod 12), (1 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)),
  (1 : Fin 2))), (((4 : ZMod 12), (1 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))),
  (((4 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12),
  (2 : ZMod 6)), (((1 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (2 : ZMod 6)),
  (((4 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (2 : ZMod 6)), (((4 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (2 : ZMod 6)), (((4 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((4 : ZMod 12), (2 : ZMod 6)), (((4 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((4 : ZMod 12), (2 : ZMod 6)), (((4 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12),
  (2 : ZMod 6)), (((4 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (2 : ZMod 6)),
  (((7 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (2 : ZMod 6)), (((10 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (2 : ZMod 6)), (((10 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((4 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))),
  (((4 : ZMod 12), (3 : ZMod 6)), (((4 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12),
  (3 : ZMod 6)), (((4 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (3 : ZMod 6)),
  (((7 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (3 : ZMod 6)), (((7 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (3 : ZMod 6)), (((7 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((4 : ZMod 12), (3 : ZMod 6)), (((7 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))),
  (((4 : ZMod 12), (3 : ZMod 6)), (((7 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12),
  (3 : ZMod 6)), (((10 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (3 : ZMod 6)),
  (((10 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (3 : ZMod 6)), (((0 : ZMod 12),
  (0 : ZMod 6)), (1 : Fin 2))), (((4 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)),
  (1 : Fin 2))), (((4 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((4 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12),
  (4 : ZMod 6)), (((1 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (4 : ZMod 6)),
  (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (4 : ZMod 6)), (((3 : ZMod 12),
  (2 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (4 : ZMod 6)), (((3 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((4 : ZMod 12), (4 : ZMod 6)), (((4 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((4 : ZMod 12), (4 : ZMod 6)), (((4 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12),
  (4 : ZMod 6)), (((4 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (4 : ZMod 6)),
  (((4 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (4 : ZMod 6)), (((6 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (4 : ZMod 6)), (((6 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((4 : ZMod 12), (4 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((4 : ZMod 12), (4 : ZMod 6)), (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12),
  (4 : ZMod 6)), (((6 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (4 : ZMod 6)),
  (((6 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (4 : ZMod 6)), (((7 : ZMod 12),
  (2 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (4 : ZMod 6)), (((10 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((4 : ZMod 12), (4 : ZMod 6)), (((10 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((4 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((4 : ZMod 12),
  (4 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((4 : ZMod 12), (5 : ZMod 6)),
  (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((4 : ZMod 12), (5 : ZMod 6)), (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((4 : ZMod 12), (5 : ZMod 6)), (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12),
  (5 : ZMod 6)), (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (5 : ZMod 6)),
  (((4 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (5 : ZMod 6)), (((4 : ZMod 12),
  (2 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (5 : ZMod 6)), (((4 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((4 : ZMod 12), (5 : ZMod 6)), (((6 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((4 : ZMod 12), (5 : ZMod 6)), (((6 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12),
  (5 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (5 : ZMod 6)),
  (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (5 : ZMod 6)), (((6 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (5 : ZMod 6)), (((6 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((4 : ZMod 12), (5 : ZMod 6)), (((7 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((4 : ZMod 12), (5 : ZMod 6)), (((10 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12),
  (5 : ZMod 6)), (((10 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (5 : ZMod 6)),
  (((0 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((4 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12),
  (1 : ZMod 6)), (1 : Fin 2))), (((5 : ZMod 12), (0 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((5 : ZMod 12), (0 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((5 : ZMod 12), (0 : ZMod 6)), (((2 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12),
  (0 : ZMod 6)), (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (0 : ZMod 6)),
  (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (0 : ZMod 6)), (((3 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (0 : ZMod 6)), (((5 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((5 : ZMod 12), (0 : ZMod 6)), (((5 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((5 : ZMod 12), (0 : ZMod 6)), (((6 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12),
  (0 : ZMod 6)), (((6 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (0 : ZMod 6)),
  (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (0 : ZMod 6)), (((6 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (0 : ZMod 6)), (((6 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((5 : ZMod 12), (0 : ZMod 6)), (((6 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((5 : ZMod 12), (0 : ZMod 6)), (((8 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12),
  (0 : ZMod 6)), (((11 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (0 : ZMod 6)),
  (((11 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (0 : ZMod 6)), (((0 : ZMod 12),
  (0 : ZMod 6)), (1 : Fin 2))), (((5 : ZMod 12), (0 : ZMod 6)), (((0 : ZMod 12), (1 : ZMod 6)),
  (1 : Fin 2))), (((5 : ZMod 12), (0 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))),
  (((5 : ZMod 12), (1 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12),
  (1 : ZMod 6)), (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (1 : ZMod 6)),
  (((2 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (1 : ZMod 6)), (((2 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (1 : ZMod 6)), (((4 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((5 : ZMod 12), (1 : ZMod 6)), (((4 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((5 : ZMod 12), (1 : ZMod 6)), (((4 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12),
  (1 : ZMod 6)), (((5 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (1 : ZMod 6)),
  (((5 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (1 : ZMod 6)), (((5 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (1 : ZMod 6)), (((5 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((5 : ZMod 12), (1 : ZMod 6)), (((7 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((5 : ZMod 12), (1 : ZMod 6)), (((7 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12),
  (1 : ZMod 6)), (((7 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (1 : ZMod 6)),
  (((7 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (1 : ZMod 6)), (((7 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (1 : ZMod 6)), (((7 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((5 : ZMod 12), (1 : ZMod 6)), (((8 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((5 : ZMod 12), (1 : ZMod 6)), (((8 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12),
  (1 : ZMod 6)), (((8 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (1 : ZMod 6)),
  (((8 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (1 : ZMod 6)), (((8 : ZMod 12),
  (5 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (1 : ZMod 6)), (((11 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((5 : ZMod 12), (1 : ZMod 6)), (((11 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((5 : ZMod 12), (1 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((5 : ZMod 12),
  (1 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((5 : ZMod 12), (1 : ZMod 6)),
  (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((5 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12),
  (2 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (2 : ZMod 6)), (((2 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((5 : ZMod 12), (2 : ZMod 6)), (((2 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((5 : ZMod 12), (2 : ZMod 6)), (((2 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12),
  (2 : ZMod 6)), (((3 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (2 : ZMod 6)),
  (((3 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (2 : ZMod 6)), (((3 : ZMod 12),
  (5 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (2 : ZMod 6)), (((5 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((5 : ZMod 12), (2 : ZMod 6)), (((5 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((5 : ZMod 12), (2 : ZMod 6)), (((5 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12),
  (2 : ZMod 6)), (((5 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (2 : ZMod 6)),
  (((5 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (2 : ZMod 6)), (((5 : ZMod 12),
  (5 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (2 : ZMod 6)), (((6 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((5 : ZMod 12), (2 : ZMod 6)), (((6 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((5 : ZMod 12), (2 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12),
  (2 : ZMod 6)), (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (2 : ZMod 6)),
  (((6 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (2 : ZMod 6)), (((6 : ZMod 12),
  (5 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (2 : ZMod 6)), (((8 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((5 : ZMod 12), (2 : ZMod 6)), (((11 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((5 : ZMod 12), (2 : ZMod 6)), (((11 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12),
  (2 : ZMod 6)), (((0 : ZMod 12), (2 : ZMod 6)), (1 : Fin 2))), (((5 : ZMod 12), (3 : ZMod 6)),
  (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (3 : ZMod 6)), (((2 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((5 : ZMod 12), (3 : ZMod 6)), (((2 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((5 : ZMod 12), (3 : ZMod 6)), (((2 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12),
  (3 : ZMod 6)), (((4 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (3 : ZMod 6)),
  (((4 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (3 : ZMod 6)), (((4 : ZMod 12),
  (2 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (3 : ZMod 6)), (((4 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((5 : ZMod 12), (3 : ZMod 6)), (((4 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))),
  (((5 : ZMod 12), (3 : ZMod 6)), (((4 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12),
  (3 : ZMod 6)), (((5 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (3 : ZMod 6)),
  (((5 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (3 : ZMod 6)), (((5 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (3 : ZMod 6)), (((5 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((5 : ZMod 12), (3 : ZMod 6)), (((8 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((5 : ZMod 12), (3 : ZMod 6)), (((8 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12),
  (3 : ZMod 6)), (((8 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (3 : ZMod 6)),
  (((8 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (3 : ZMod 6)), (((8 : ZMod 12),
  (5 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (3 : ZMod 6)), (((11 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((5 : ZMod 12), (3 : ZMod 6)), (((11 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((5 : ZMod 12), (3 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((5 : ZMod 12),
  (3 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2))), (((5 : ZMod 12), (3 : ZMod 6)),
  (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((5 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((5 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((5 : ZMod 12), (4 : ZMod 6)), (((2 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12),
  (4 : ZMod 6)), (((2 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (4 : ZMod 6)),
  (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (4 : ZMod 6)), (((3 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (4 : ZMod 6)), (((3 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((5 : ZMod 12), (4 : ZMod 6)), (((3 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((5 : ZMod 12), (4 : ZMod 6)), (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12),
  (4 : ZMod 6)), (((3 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (4 : ZMod 6)),
  (((5 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (4 : ZMod 6)), (((5 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (4 : ZMod 6)), (((5 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((5 : ZMod 12), (4 : ZMod 6)), (((5 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((5 : ZMod 12), (4 : ZMod 6)), (((8 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12),
  (4 : ZMod 6)), (((11 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (4 : ZMod 6)),
  (((11 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12),
  (0 : ZMod 6)), (1 : Fin 2))), (((5 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (1 : ZMod 6)),
  (1 : Fin 2))), (((5 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (2 : ZMod 6)), (1 : Fin 2))),
  (((5 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((5 : ZMod 12),
  (5 : ZMod 6)), (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (5 : ZMod 6)),
  (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (5 : ZMod 6)), (((2 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (5 : ZMod 6)), (((2 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((5 : ZMod 12), (5 : ZMod 6)), (((2 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))),
  (((5 : ZMod 12), (5 : ZMod 6)), (((4 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12),
  (5 : ZMod 6)), (((4 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (5 : ZMod 6)),
  (((4 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (5 : ZMod 6)), (((5 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (5 : ZMod 6)), (((5 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((5 : ZMod 12), (5 : ZMod 6)), (((5 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((5 : ZMod 12), (5 : ZMod 6)), (((5 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12),
  (5 : ZMod 6)), (((7 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (5 : ZMod 6)),
  (((7 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (5 : ZMod 6)), (((7 : ZMod 12),
  (2 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (5 : ZMod 6)), (((7 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((5 : ZMod 12), (5 : ZMod 6)), (((7 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))),
  (((5 : ZMod 12), (5 : ZMod 6)), (((7 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12),
  (5 : ZMod 6)), (((8 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (5 : ZMod 6)),
  (((8 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (5 : ZMod 6)), (((8 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (5 : ZMod 6)), (((8 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((5 : ZMod 12), (5 : ZMod 6)), (((8 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((5 : ZMod 12), (5 : ZMod 6)), (((11 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12),
  (5 : ZMod 6)), (((11 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (5 : ZMod 6)),
  (((0 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2))), (((5 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12),
  (1 : ZMod 6)), (1 : Fin 2))), (((6 : ZMod 12), (0 : ZMod 6)), (((0 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((6 : ZMod 12), (0 : ZMod 6)), (((0 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((6 : ZMod 12), (0 : ZMod 6)), (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12),
  (0 : ZMod 6)), (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (0 : ZMod 6)),
  (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (0 : ZMod 6)), (((6 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (0 : ZMod 6)), (((6 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((6 : ZMod 12), (0 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((6 : ZMod 12), (0 : ZMod 6)), (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12),
  (0 : ZMod 6)), (((6 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (0 : ZMod 6)),
  (((6 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (0 : ZMod 6)), (((9 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (1 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((6 : ZMod 12), (1 : ZMod 6)), (((0 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((6 : ZMod 12), (1 : ZMod 6)), (((3 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12),
  (1 : ZMod 6)), (((3 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (1 : ZMod 6)),
  (((3 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (1 : ZMod 6)), (((6 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (1 : ZMod 6)), (((6 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((6 : ZMod 12), (1 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((6 : ZMod 12), (1 : ZMod 6)), (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12),
  (1 : ZMod 6)), (((6 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (1 : ZMod 6)),
  (((6 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (1 : ZMod 6)), (((9 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((6 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((6 : ZMod 12), (2 : ZMod 6)), (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12),
  (2 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (2 : ZMod 6)),
  (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (2 : ZMod 6)), (((9 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (3 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((6 : ZMod 12), (3 : ZMod 6)), (((0 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((6 : ZMod 12), (3 : ZMod 6)), (((3 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12),
  (3 : ZMod 6)), (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (3 : ZMod 6)),
  (((6 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (3 : ZMod 6)), (((9 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((6 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((6 : ZMod 12), (4 : ZMod 6)), (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12),
  (4 : ZMod 6)), (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (4 : ZMod 6)),
  (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (4 : ZMod 6)), (((6 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (4 : ZMod 6)), (((6 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((6 : ZMod 12), (4 : ZMod 6)), (((6 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((6 : ZMod 12), (4 : ZMod 6)), (((9 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12),
  (5 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (5 : ZMod 6)),
  (((0 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (5 : ZMod 6)), (((3 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (5 : ZMod 6)), (((3 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((6 : ZMod 12), (5 : ZMod 6)), (((6 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((6 : ZMod 12), (5 : ZMod 6)), (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12),
  (5 : ZMod 6)), (((6 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (5 : ZMod 6)),
  (((6 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (5 : ZMod 6)), (((9 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (0 : ZMod 6)), (((1 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((7 : ZMod 12), (0 : ZMod 6)), (((1 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((7 : ZMod 12), (0 : ZMod 6)), (((4 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12),
  (0 : ZMod 6)), (((4 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (0 : ZMod 6)),
  (((4 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (0 : ZMod 6)), (((7 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (0 : ZMod 6)), (((7 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((7 : ZMod 12), (0 : ZMod 6)), (((7 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((7 : ZMod 12), (0 : ZMod 6)), (((7 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12),
  (0 : ZMod 6)), (((7 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (0 : ZMod 6)),
  (((7 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (0 : ZMod 6)), (((10 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (1 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((7 : ZMod 12), (1 : ZMod 6)), (((1 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((7 : ZMod 12), (1 : ZMod 6)), (((4 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12),
  (1 : ZMod 6)), (((4 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (1 : ZMod 6)),
  (((4 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (1 : ZMod 6)), (((7 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (1 : ZMod 6)), (((7 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((7 : ZMod 12), (1 : ZMod 6)), (((7 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((7 : ZMod 12), (1 : ZMod 6)), (((7 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12),
  (1 : ZMod 6)), (((7 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (1 : ZMod 6)),
  (((7 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (1 : ZMod 6)), (((10 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((7 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))),
  (((7 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12),
  (2 : ZMod 6)), (((4 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (2 : ZMod 6)),
  (((4 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (2 : ZMod 6)), (((4 : ZMod 12),
  (2 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (2 : ZMod 6)), (((4 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((7 : ZMod 12), (2 : ZMod 6)), (((4 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((7 : ZMod 12), (2 : ZMod 6)), (((7 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12),
  (2 : ZMod 6)), (((7 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (2 : ZMod 6)),
  (((10 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12),
  (0 : ZMod 6)), (1 : Fin 2))), (((7 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)),
  (1 : Fin 2))), (((7 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((7 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12),
  (3 : ZMod 6)), (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (3 : ZMod 6)),
  (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (3 : ZMod 6)), (((3 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (3 : ZMod 6)), (((4 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((7 : ZMod 12), (3 : ZMod 6)), (((6 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((7 : ZMod 12), (3 : ZMod 6)), (((6 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12),
  (3 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (3 : ZMod 6)),
  (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (3 : ZMod 6)), (((6 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (3 : ZMod 6)), (((6 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((7 : ZMod 12), (3 : ZMod 6)), (((7 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((7 : ZMod 12), (3 : ZMod 6)), (((7 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12),
  (3 : ZMod 6)), (((10 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (3 : ZMod 6)),
  (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((7 : ZMod 12), (3 : ZMod 6)), (((0 : ZMod 12),
  (1 : ZMod 6)), (1 : Fin 2))), (((7 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)),
  (1 : Fin 2))), (((7 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))),
  (((7 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12),
  (4 : ZMod 6)), (((1 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (4 : ZMod 6)),
  (((1 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (4 : ZMod 6)), (((4 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (4 : ZMod 6)), (((4 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((7 : ZMod 12), (4 : ZMod 6)), (((4 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((7 : ZMod 12), (4 : ZMod 6)), (((4 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12),
  (4 : ZMod 6)), (((7 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (4 : ZMod 6)),
  (((7 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (4 : ZMod 6)), (((7 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (4 : ZMod 6)), (((7 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((7 : ZMod 12), (4 : ZMod 6)), (((10 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((7 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((7 : ZMod 12),
  (4 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((7 : ZMod 12), (5 : ZMod 6)),
  (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12),
  (5 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (5 : ZMod 6)), (((3 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((7 : ZMod 12), (5 : ZMod 6)), (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((7 : ZMod 12), (5 : ZMod 6)), (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12),
  (5 : ZMod 6)), (((4 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (5 : ZMod 6)),
  (((4 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (5 : ZMod 6)), (((6 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (5 : ZMod 6)), (((6 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((7 : ZMod 12), (5 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((7 : ZMod 12), (5 : ZMod 6)), (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12),
  (5 : ZMod 6)), (((6 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (5 : ZMod 6)),
  (((6 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (5 : ZMod 6)), (((7 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (5 : ZMod 6)), (((7 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((7 : ZMod 12), (5 : ZMod 6)), (((7 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))),
  (((7 : ZMod 12), (5 : ZMod 6)), (((7 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12),
  (5 : ZMod 6)), (((10 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (5 : ZMod 6)),
  (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((7 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12),
  (1 : ZMod 6)), (1 : Fin 2))), (((7 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)),
  (1 : Fin 2))), (((7 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))),
  (((8 : ZMod 12), (0 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (0 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (0 : ZMod 6)),
  (((1 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (0 : ZMod 6)), (((1 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (0 : ZMod 6)), (((2 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (0 : ZMod 6)), (((2 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (0 : ZMod 6)), (((2 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (0 : ZMod 6)), (((2 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (0 : ZMod 6)),
  (((2 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (0 : ZMod 6)), (((2 : ZMod 12),
  (5 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (0 : ZMod 6)), (((3 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (0 : ZMod 6)), (((3 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (0 : ZMod 6)), (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (0 : ZMod 6)), (((3 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (0 : ZMod 6)),
  (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (0 : ZMod 6)), (((3 : ZMod 12),
  (5 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (0 : ZMod 6)), (((4 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (0 : ZMod 6)), (((4 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (0 : ZMod 6)), (((4 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (0 : ZMod 6)), (((7 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (0 : ZMod 6)),
  (((7 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (0 : ZMod 6)), (((7 : ZMod 12),
  (2 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (0 : ZMod 6)), (((7 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (0 : ZMod 6)), (((7 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (0 : ZMod 6)), (((7 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (0 : ZMod 6)), (((11 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (0 : ZMod 6)),
  (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((8 : ZMod 12), (0 : ZMod 6)), (((0 : ZMod 12),
  (1 : ZMod 6)), (1 : Fin 2))), (((8 : ZMod 12), (0 : ZMod 6)), (((0 : ZMod 12), (2 : ZMod 6)),
  (1 : Fin 2))), (((8 : ZMod 12), (0 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2))),
  (((8 : ZMod 12), (1 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (1 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)),
  (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)), (((2 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)), (((2 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)), (((2 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (1 : ZMod 6)), (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (1 : ZMod 6)), (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)),
  (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)), (((4 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)), (((4 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)), (((4 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (1 : ZMod 6)), (((5 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (1 : ZMod 6)), (((5 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)),
  (((5 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)), (((5 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)), (((5 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)), (((5 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (1 : ZMod 6)), (((6 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (1 : ZMod 6)), (((6 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)),
  (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)), (((6 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)), (((6 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)), (((6 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (1 : ZMod 6)), (((7 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (1 : ZMod 6)), (((7 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)),
  (((7 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)), (((7 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)), (((7 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)), (((7 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (1 : ZMod 6)), (((11 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (1 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)),
  (((0 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)), (((0 : ZMod 12),
  (3 : ZMod 6)), (1 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)), (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (2 : ZMod 6)), (((2 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (2 : ZMod 6)), (((2 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)),
  (((2 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)), (((3 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)), (((3 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)), (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (2 : ZMod 6)), (((4 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (2 : ZMod 6)), (((4 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)),
  (((4 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)), (((5 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)), (((5 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)), (((6 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (2 : ZMod 6)), (((6 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (2 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)),
  (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)), (((6 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)), (((6 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)), (((7 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (2 : ZMod 6)), (((7 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (2 : ZMod 6)), (((7 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)),
  (((7 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)), (((7 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)), (((7 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)), (((8 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (2 : ZMod 6)), (((8 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (2 : ZMod 6)), (((8 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)),
  (((8 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)), (((11 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12), (1 : ZMod 6)),
  (1 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))),
  (((8 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (3 : ZMod 6)), (((1 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (3 : ZMod 6)),
  (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (3 : ZMod 6)), (((2 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (3 : ZMod 6)), (((2 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (3 : ZMod 6)), (((2 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (3 : ZMod 6)), (((3 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (3 : ZMod 6)), (((3 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (3 : ZMod 6)),
  (((3 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (3 : ZMod 6)), (((4 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (3 : ZMod 6)), (((4 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (3 : ZMod 6)), (((4 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (3 : ZMod 6)), (((5 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (3 : ZMod 6)), (((5 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (3 : ZMod 6)),
  (((6 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (3 : ZMod 6)), (((6 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (3 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (3 : ZMod 6)), (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (3 : ZMod 6)), (((6 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (3 : ZMod 6)), (((6 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (3 : ZMod 6)),
  (((7 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (3 : ZMod 6)), (((7 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (3 : ZMod 6)), (((7 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (3 : ZMod 6)), (((7 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (3 : ZMod 6)), (((7 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (3 : ZMod 6)), (((7 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (3 : ZMod 6)),
  (((8 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (3 : ZMod 6)), (((8 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (3 : ZMod 6)), (((8 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (3 : ZMod 6)), (((8 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (3 : ZMod 6)), (((11 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (3 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((8 : ZMod 12), (3 : ZMod 6)),
  (((0 : ZMod 12), (2 : ZMod 6)), (1 : Fin 2))), (((8 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12),
  (0 : ZMod 6)), (1 : Fin 2))), (((8 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)),
  (1 : Fin 2))), (((8 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (4 : ZMod 6)), (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (4 : ZMod 6)),
  (((2 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (4 : ZMod 6)), (((2 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (4 : ZMod 6)), (((2 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (4 : ZMod 6)), (((2 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (4 : ZMod 6)), (((3 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (4 : ZMod 6)), (((3 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (4 : ZMod 6)),
  (((3 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (4 : ZMod 6)), (((4 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (4 : ZMod 6)), (((4 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (4 : ZMod 6)), (((4 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (4 : ZMod 6)), (((4 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (4 : ZMod 6)), (((4 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (4 : ZMod 6)),
  (((4 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (4 : ZMod 6)), (((5 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (4 : ZMod 6)), (((5 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (4 : ZMod 6)), (((6 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (4 : ZMod 6)), (((6 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (4 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (4 : ZMod 6)),
  (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (4 : ZMod 6)), (((6 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (4 : ZMod 6)), (((6 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (4 : ZMod 6)), (((8 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (4 : ZMod 6)), (((8 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (4 : ZMod 6)), (((8 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (4 : ZMod 6)),
  (((8 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (4 : ZMod 6)), (((11 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)),
  (1 : Fin 2))), (((8 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (2 : ZMod 6)), (1 : Fin 2))),
  (((8 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2))), (((8 : ZMod 12),
  (4 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)),
  (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12),
  (2 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)), (((2 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (5 : ZMod 6)), (((2 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (5 : ZMod 6)), (((2 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)),
  (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)), (((3 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)), (((3 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)), (((3 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (5 : ZMod 6)), (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (5 : ZMod 6)), (((3 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)),
  (((4 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)), (((4 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)), (((4 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)), (((4 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (5 : ZMod 6)), (((4 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (5 : ZMod 6)), (((4 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)),
  (((5 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)), (((5 : ZMod 12),
  (2 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)), (((5 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)), (((5 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (5 : ZMod 6)), (((8 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (5 : ZMod 6)), (((8 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)),
  (((8 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)), (((8 : ZMod 12),
  (5 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)), (((11 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))),
  (((8 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (2 : ZMod 6)), (1 : Fin 2))), (((8 : ZMod 12),
  (5 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)),
  (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12),
  (1 : ZMod 6)), (1 : Fin 2))), (((9 : ZMod 12), (0 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((9 : ZMod 12), (0 : ZMod 6)), (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((9 : ZMod 12), (0 : ZMod 6)), (((3 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12),
  (0 : ZMod 6)), (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (0 : ZMod 6)),
  (((3 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (0 : ZMod 6)), (((3 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (0 : ZMod 6)), (((3 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((9 : ZMod 12), (1 : ZMod 6)), (((0 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((9 : ZMod 12), (1 : ZMod 6)), (((3 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12),
  (1 : ZMod 6)), (((3 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (1 : ZMod 6)),
  (((3 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (1 : ZMod 6)), (((6 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (1 : ZMod 6)), (((6 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((9 : ZMod 12), (1 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((9 : ZMod 12), (1 : ZMod 6)), (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12),
  (1 : ZMod 6)), (((6 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (1 : ZMod 6)),
  (((6 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12),
  (2 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (3 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((9 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))),
  (((9 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12),
  (5 : ZMod 6)), (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (5 : ZMod 6)),
  (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (5 : ZMod 6)), (((3 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (5 : ZMod 6)), (((6 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((9 : ZMod 12), (5 : ZMod 6)), (((6 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((9 : ZMod 12), (5 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12),
  (5 : ZMod 6)), (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (5 : ZMod 6)),
  (((6 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (5 : ZMod 6)), (((6 : ZMod 12),
  (5 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (0 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((10 : ZMod 12), (0 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((10 : ZMod 12), (0 : ZMod 6)), (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12),
  (0 : ZMod 6)), (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (0 : ZMod 6)),
  (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (0 : ZMod 6)), (((6 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (0 : ZMod 6)), (((6 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((10 : ZMod 12), (0 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((10 : ZMod 12), (0 : ZMod 6)), (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12),
  (0 : ZMod 6)), (((6 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (0 : ZMod 6)),
  (((6 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (0 : ZMod 6)), (((0 : ZMod 12),
  (1 : ZMod 6)), (1 : Fin 2))), (((10 : ZMod 12), (0 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)),
  (1 : Fin 2))), (((10 : ZMod 12), (1 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((10 : ZMod 12), (1 : ZMod 6)), (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12),
  (1 : ZMod 6)), (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (1 : ZMod 6)),
  (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (1 : ZMod 6)), (((4 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (1 : ZMod 6)), (((4 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((10 : ZMod 12), (1 : ZMod 6)), (((4 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((10 : ZMod 12), (1 : ZMod 6)), (((6 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12),
  (1 : ZMod 6)), (((6 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (1 : ZMod 6)),
  (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (1 : ZMod 6)), (((6 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (1 : ZMod 6)), (((6 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((10 : ZMod 12), (1 : ZMod 6)), (((6 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((10 : ZMod 12), (1 : ZMod 6)), (((7 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12),
  (1 : ZMod 6)), (((7 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (1 : ZMod 6)),
  (((7 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (1 : ZMod 6)), (((7 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (1 : ZMod 6)), (((7 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((10 : ZMod 12), (1 : ZMod 6)), (((7 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((10 : ZMod 12), (1 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((10 : ZMod 12),
  (1 : ZMod 6)), (((0 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((10 : ZMod 12), (1 : ZMod 6)),
  (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((10 : ZMod 12), (1 : ZMod 6)), (((1 : ZMod 12),
  (1 : ZMod 6)), (1 : Fin 2))), (((10 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((10 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((10 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12),
  (3 : ZMod 6)), (((4 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (3 : ZMod 6)),
  (((4 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (3 : ZMod 6)), (((4 : ZMod 12),
  (2 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (3 : ZMod 6)), (((4 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((10 : ZMod 12), (3 : ZMod 6)), (((4 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))),
  (((10 : ZMod 12), (3 : ZMod 6)), (((4 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12),
  (3 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((10 : ZMod 12), (3 : ZMod 6)),
  (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((10 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((10 : ZMod 12), (4 : ZMod 6)), (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((10 : ZMod 12), (4 : ZMod 6)), (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12),
  (4 : ZMod 6)), (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (4 : ZMod 6)),
  (((4 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (4 : ZMod 6)), (((4 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (4 : ZMod 6)), (((4 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((10 : ZMod 12), (4 : ZMod 6)), (((4 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((10 : ZMod 12), (4 : ZMod 6)), (((4 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12),
  (4 : ZMod 6)), (((4 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (4 : ZMod 6)),
  (((6 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (4 : ZMod 6)), (((6 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (4 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((10 : ZMod 12), (4 : ZMod 6)), (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((10 : ZMod 12), (4 : ZMod 6)), (((6 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12),
  (4 : ZMod 6)), (((6 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (4 : ZMod 6)),
  (((0 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((10 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12),
  (1 : ZMod 6)), (1 : Fin 2))), (((10 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((10 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((10 : ZMod 12), (5 : ZMod 6)), (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12),
  (5 : ZMod 6)), (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (5 : ZMod 6)),
  (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (5 : ZMod 6)), (((4 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (5 : ZMod 6)), (((4 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((10 : ZMod 12), (5 : ZMod 6)), (((4 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((10 : ZMod 12), (5 : ZMod 6)), (((6 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12),
  (5 : ZMod 6)), (((6 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (5 : ZMod 6)),
  (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (5 : ZMod 6)), (((6 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (5 : ZMod 6)), (((6 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((10 : ZMod 12), (5 : ZMod 6)), (((6 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((10 : ZMod 12), (5 : ZMod 6)), (((7 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12),
  (5 : ZMod 6)), (((7 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (5 : ZMod 6)),
  (((7 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (5 : ZMod 6)), (((7 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (5 : ZMod 6)), (((7 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((10 : ZMod 12), (5 : ZMod 6)), (((7 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((10 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((10 : ZMod 12),
  (5 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((11 : ZMod 12), (0 : ZMod 6)),
  (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (0 : ZMod 6)), (((1 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (0 : ZMod 6)), (((3 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((11 : ZMod 12), (0 : ZMod 6)), (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((11 : ZMod 12), (0 : ZMod 6)), (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12),
  (0 : ZMod 6)), (((6 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (0 : ZMod 6)),
  (((6 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (0 : ZMod 6)), (((6 : ZMod 12),
  (2 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (0 : ZMod 6)), (((6 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((11 : ZMod 12), (0 : ZMod 6)), (((6 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))),
  (((11 : ZMod 12), (0 : ZMod 6)), (((6 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12),
  (0 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((11 : ZMod 12), (0 : ZMod 6)),
  (((0 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((11 : ZMod 12), (0 : ZMod 6)), (((1 : ZMod 12),
  (1 : ZMod 6)), (1 : Fin 2))), (((11 : ZMod 12), (1 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((11 : ZMod 12), (1 : ZMod 6)), (((4 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((11 : ZMod 12), (1 : ZMod 6)), (((4 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12),
  (1 : ZMod 6)), (((4 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (1 : ZMod 6)),
  (((7 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (1 : ZMod 6)), (((7 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (1 : ZMod 6)), (((7 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((11 : ZMod 12), (1 : ZMod 6)), (((7 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((11 : ZMod 12), (1 : ZMod 6)), (((7 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12),
  (1 : ZMod 6)), (((7 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (1 : ZMod 6)),
  (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((11 : ZMod 12), (1 : ZMod 6)), (((1 : ZMod 12),
  (0 : ZMod 6)), (1 : Fin 2))), (((11 : ZMod 12), (1 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)),
  (1 : Fin 2))), (((11 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((11 : ZMod 12), (2 : ZMod 6)), (((3 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12),
  (2 : ZMod 6)), (((3 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (2 : ZMod 6)),
  (((3 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (2 : ZMod 6)), (((6 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (2 : ZMod 6)), (((6 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((11 : ZMod 12), (2 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((11 : ZMod 12), (2 : ZMod 6)), (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12),
  (2 : ZMod 6)), (((6 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (2 : ZMod 6)),
  (((6 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12),
  (2 : ZMod 6)), (1 : Fin 2))), (((11 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((11 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((11 : ZMod 12), (3 : ZMod 6)), (((4 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12),
  (3 : ZMod 6)), (((4 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (3 : ZMod 6)),
  (((4 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (3 : ZMod 6)), (((4 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (3 : ZMod 6)), (((4 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((11 : ZMod 12), (3 : ZMod 6)), (((4 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((11 : ZMod 12), (3 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((11 : ZMod 12),
  (3 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2))), (((11 : ZMod 12), (3 : ZMod 6)),
  (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((11 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((11 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((11 : ZMod 12), (4 : ZMod 6)), (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12),
  (4 : ZMod 6)), (((2 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (4 : ZMod 6)),
  (((2 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (4 : ZMod 6)), (((3 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (4 : ZMod 6)), (((3 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((11 : ZMod 12), (4 : ZMod 6)), (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((11 : ZMod 12), (4 : ZMod 6)), (((3 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12),
  (4 : ZMod 6)), (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (4 : ZMod 6)),
  (((3 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (4 : ZMod 6)), (((5 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (4 : ZMod 6)), (((5 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((11 : ZMod 12), (4 : ZMod 6)), (((5 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((11 : ZMod 12), (4 : ZMod 6)), (((5 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12),
  (4 : ZMod 6)), (((5 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (4 : ZMod 6)),
  (((5 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12),
  (0 : ZMod 6)), (1 : Fin 2))), (((11 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (1 : ZMod 6)),
  (1 : Fin 2))), (((11 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (2 : ZMod 6)), (1 : Fin 2))),
  (((11 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((11 : ZMod 12),
  (5 : ZMod 6)), (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (5 : ZMod 6)),
  (((2 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (5 : ZMod 6)), (((2 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (5 : ZMod 6)), (((2 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((11 : ZMod 12), (5 : ZMod 6)), (((4 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((11 : ZMod 12), (5 : ZMod 6)), (((4 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12),
  (5 : ZMod 6)), (((4 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (5 : ZMod 6)),
  (((5 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (5 : ZMod 6)), (((5 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (5 : ZMod 6)), (((5 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((11 : ZMod 12), (5 : ZMod 6)), (((5 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((11 : ZMod 12), (5 : ZMod 6)), (((5 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12),
  (5 : ZMod 6)), (((5 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (5 : ZMod 6)),
  (((7 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (5 : ZMod 6)), (((7 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (5 : ZMod 6)), (((7 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((11 : ZMod 12), (5 : ZMod 6)), (((7 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((11 : ZMod 12), (5 : ZMod 6)), (((7 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12),
  (5 : ZMod 6)), (((7 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (5 : ZMod 6)),
  (((0 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2))), (((11 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12),
  (1 : ZMod 6)), (1 : Fin 2)))]

/-- Vertex-independence syndrome decoder. -/
def phiZ : List (GrossGroup × (GrossGroup × Fin 2)) := [(((0 : ZMod 12), (4 : ZMod 6)),
  (((0 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((0 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((0 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((0 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((0 : ZMod 12), (4 : ZMod 6)), (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((0 : ZMod 12),
  (4 : ZMod 6)), (((2 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((0 : ZMod 12), (4 : ZMod 6)),
  (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((0 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12),
  (0 : ZMod 6)), (1 : Fin 2))), (((0 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)),
  (1 : Fin 2))), (((0 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((0 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((0 : ZMod 12),
  (5 : ZMod 6)), (((0 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((0 : ZMod 12), (5 : ZMod 6)),
  (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((0 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((0 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((0 : ZMod 12), (5 : ZMod 6)), (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((0 : ZMod 12), (5 : ZMod 6)), (((2 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((0 : ZMod 12),
  (5 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2))), (((0 : ZMod 12), (5 : ZMod 6)),
  (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((0 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12),
  (1 : ZMod 6)), (1 : Fin 2))), (((1 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((1 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((1 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12),
  (2 : ZMod 6)), (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (2 : ZMod 6)),
  (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((1 : ZMod 12), (3 : ZMod 6)), (((0 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((1 : ZMod 12), (3 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))),
  (((1 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12),
  (4 : ZMod 6)), (((0 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (4 : ZMod 6)),
  (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (4 : ZMod 6)), (((2 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)),
  (1 : Fin 2))), (((1 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))),
  (((1 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((1 : ZMod 12),
  (4 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((1 : ZMod 12), (5 : ZMod 6)),
  (((0 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12),
  (2 : ZMod 6)), (0 : Fin 2))), (((1 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((1 : ZMod 12), (5 : ZMod 6)), (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((1 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((1 : ZMod 12),
  (5 : ZMod 6)), (((0 : ZMod 12), (2 : ZMod 6)), (1 : Fin 2))), (((1 : ZMod 12), (5 : ZMod 6)),
  (((0 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2))), (((1 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12),
  (0 : ZMod 6)), (1 : Fin 2))), (((2 : ZMod 12), (0 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (1 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (1 : ZMod 6)), (((0 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (1 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (1 : ZMod 6)),
  (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (1 : ZMod 6)), (((2 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (1 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)),
  (1 : Fin 2))), (((2 : ZMod 12), (1 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))),
  (((2 : ZMod 12), (1 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((2 : ZMod 12),
  (2 : ZMod 6)), (((0 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (2 : ZMod 6)),
  (((0 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (2 : ZMod 6)), (((2 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (2 : ZMod 6)),
  (((0 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2))), (((2 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12),
  (1 : ZMod 6)), (1 : Fin 2))), (((2 : ZMod 12), (3 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (3 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (3 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((2 : ZMod 12), (4 : ZMod 6)),
  (((0 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (4 : ZMod 6)), (((2 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (4 : ZMod 6)), (((2 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))),
  (((2 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((2 : ZMod 12),
  (4 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((2 : ZMod 12), (4 : ZMod 6)),
  (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((2 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12),
  (2 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((2 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((2 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12),
  (5 : ZMod 6)), (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((2 : ZMod 12), (5 : ZMod 6)),
  (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((2 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12),
  (2 : ZMod 6)), (1 : Fin 2))), (((2 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)),
  (1 : Fin 2))), (((2 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))),
  (((3 : ZMod 12), (0 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((3 : ZMod 12),
  (1 : ZMod 6)), (((0 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((3 : ZMod 12), (2 : ZMod 6)),
  (((0 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((3 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((3 : ZMod 12), (2 : ZMod 6)), (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12),
  (2 : ZMod 6)), (((2 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (2 : ZMod 6)),
  (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((3 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12),
  (2 : ZMod 6)), (1 : Fin 2))), (((3 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)),
  (1 : Fin 2))), (((3 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))),
  (((3 : ZMod 12), (3 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12),
  (3 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (3 : ZMod 6)),
  (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (3 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)),
  (1 : Fin 2))), (((3 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((3 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12),
  (4 : ZMod 6)), (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (4 : ZMod 6)),
  (((2 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12),
  (0 : ZMod 6)), (1 : Fin 2))), (((3 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (1 : ZMod 6)),
  (1 : Fin 2))), (((3 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))),
  (((3 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((3 : ZMod 12),
  (5 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (5 : ZMod 6)),
  (((0 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((3 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((3 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12),
  (5 : ZMod 6)), (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (5 : ZMod 6)),
  (((1 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((3 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12),
  (0 : ZMod 6)), (1 : Fin 2))), (((3 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (2 : ZMod 6)),
  (1 : Fin 2))), (((3 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2))),
  (((4 : ZMod 12), (0 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12),
  (0 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (0 : ZMod 6)),
  (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (0 : ZMod 6)), (((2 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (1 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((4 : ZMod 12), (1 : ZMod 6)), (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((4 : ZMod 12), (1 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((4 : ZMod 12),
  (1 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((4 : ZMod 12), (1 : ZMod 6)),
  (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((4 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((4 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((4 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12),
  (2 : ZMod 6)), (((0 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (2 : ZMod 6)),
  (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12),
  (2 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((4 : ZMod 12), (2 : ZMod 6)), (((2 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((4 : ZMod 12), (2 : ZMod 6)), (((2 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12),
  (2 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2))), (((4 : ZMod 12), (2 : ZMod 6)),
  (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((4 : ZMod 12), (3 : ZMod 6)), (((0 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((4 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((4 : ZMod 12), (3 : ZMod 6)), (((2 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12),
  (3 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((4 : ZMod 12), (4 : ZMod 6)),
  (((0 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((4 : ZMod 12), (4 : ZMod 6)), (((2 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))),
  (((4 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((4 : ZMod 12),
  (5 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (5 : ZMod 6)),
  (((0 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((4 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((4 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12),
  (5 : ZMod 6)), (((1 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (5 : ZMod 6)),
  (((1 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (5 : ZMod 6)), (((2 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((4 : ZMod 12), (5 : ZMod 6)), (((2 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((4 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))),
  (((4 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (2 : ZMod 6)), (1 : Fin 2))), (((4 : ZMod 12),
  (5 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((5 : ZMod 12), (0 : ZMod 6)),
  (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (0 : ZMod 6)), (((2 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (0 : ZMod 6)), (((3 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((5 : ZMod 12), (0 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))),
  (((5 : ZMod 12), (1 : ZMod 6)), (((1 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12),
  (1 : ZMod 6)), (((2 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (1 : ZMod 6)),
  (((3 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (1 : ZMod 6)), (((0 : ZMod 12),
  (1 : ZMod 6)), (1 : Fin 2))), (((5 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((5 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((5 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12),
  (2 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (2 : ZMod 6)),
  (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12),
  (5 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (2 : ZMod 6)), (((2 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((5 : ZMod 12), (2 : ZMod 6)), (((2 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((5 : ZMod 12), (2 : ZMod 6)), (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12),
  (2 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((5 : ZMod 12), (2 : ZMod 6)),
  (((0 : ZMod 12), (2 : ZMod 6)), (1 : Fin 2))), (((5 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12),
  (1 : ZMod 6)), (1 : Fin 2))), (((5 : ZMod 12), (3 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((5 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((5 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12),
  (3 : ZMod 6)), (((2 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (3 : ZMod 6)),
  (((3 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((5 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))),
  (((5 : ZMod 12), (4 : ZMod 6)), (((2 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12),
  (4 : ZMod 6)), (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (5 : ZMod 6)),
  (((0 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((5 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((5 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12),
  (5 : ZMod 6)), (((1 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (5 : ZMod 6)),
  (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (5 : ZMod 6)), (((2 : ZMod 12),
  (5 : ZMod 6)), (0 : Fin 2))), (((5 : ZMod 12), (5 : ZMod 6)), (((3 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((5 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))),
  (((6 : ZMod 12), (0 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12),
  (0 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (0 : ZMod 6)),
  (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (0 : ZMod 6)), (((2 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (0 : ZMod 6)), (((3 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((6 : ZMod 12), (0 : ZMod 6)), (((4 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((6 : ZMod 12), (1 : ZMod 6)), (((0 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12),
  (1 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (1 : ZMod 6)),
  (((2 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (1 : ZMod 6)), (((2 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (1 : ZMod 6)), (((3 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((6 : ZMod 12), (1 : ZMod 6)), (((4 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((6 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12),
  (2 : ZMod 6)), (((1 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (2 : ZMod 6)),
  (((2 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (2 : ZMod 6)), (((2 : ZMod 12),
  (5 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (2 : ZMod 6)), (((3 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((6 : ZMod 12), (2 : ZMod 6)), (((4 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((6 : ZMod 12), (3 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12),
  (3 : ZMod 6)), (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (3 : ZMod 6)),
  (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (3 : ZMod 6)), (((2 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (3 : ZMod 6)), (((3 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((6 : ZMod 12), (3 : ZMod 6)), (((4 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((6 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12),
  (4 : ZMod 6)), (((0 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (4 : ZMod 6)),
  (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (4 : ZMod 6)), (((2 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((6 : ZMod 12), (4 : ZMod 6)), (((2 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))),
  (((6 : ZMod 12), (4 : ZMod 6)), (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12),
  (4 : ZMod 6)), (((4 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (4 : ZMod 6)),
  (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((6 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12),
  (0 : ZMod 6)), (1 : Fin 2))), (((6 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)),
  (1 : Fin 2))), (((6 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((6 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12),
  (5 : ZMod 6)), (((0 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (5 : ZMod 6)),
  (((0 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((6 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((6 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12),
  (5 : ZMod 6)), (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (5 : ZMod 6)),
  (((2 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (5 : ZMod 6)), (((2 : ZMod 12),
  (2 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12), (5 : ZMod 6)), (((2 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((6 : ZMod 12), (5 : ZMod 6)), (((3 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((6 : ZMod 12), (5 : ZMod 6)), (((4 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((6 : ZMod 12),
  (5 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2))), (((6 : ZMod 12), (5 : ZMod 6)),
  (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((6 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12),
  (1 : ZMod 6)), (1 : Fin 2))), (((7 : ZMod 12), (0 : ZMod 6)), (((1 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((7 : ZMod 12), (0 : ZMod 6)), (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((7 : ZMod 12), (0 : ZMod 6)), (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12),
  (0 : ZMod 6)), (((3 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (0 : ZMod 6)),
  (((4 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (0 : ZMod 6)), (((5 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (1 : ZMod 6)), (((1 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((7 : ZMod 12), (1 : ZMod 6)), (((2 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((7 : ZMod 12), (1 : ZMod 6)), (((3 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12),
  (1 : ZMod 6)), (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (1 : ZMod 6)),
  (((4 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (1 : ZMod 6)), (((5 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((7 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((7 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12),
  (2 : ZMod 6)), (((1 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (2 : ZMod 6)),
  (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (2 : ZMod 6)), (((2 : ZMod 12),
  (2 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (2 : ZMod 6)), (((3 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((7 : ZMod 12), (2 : ZMod 6)), (((3 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((7 : ZMod 12), (2 : ZMod 6)), (((4 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12),
  (2 : ZMod 6)), (((5 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (2 : ZMod 6)),
  (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((7 : ZMod 12), (3 : ZMod 6)), (((0 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (3 : ZMod 6)), (((2 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((7 : ZMod 12), (3 : ZMod 6)), (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((7 : ZMod 12), (3 : ZMod 6)), (((3 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12),
  (3 : ZMod 6)), (((4 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (3 : ZMod 6)),
  (((5 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (3 : ZMod 6)), (((0 : ZMod 12),
  (0 : ZMod 6)), (1 : Fin 2))), (((7 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((7 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))),
  (((7 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12),
  (4 : ZMod 6)), (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (4 : ZMod 6)),
  (((2 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (4 : ZMod 6)), (((2 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (4 : ZMod 6)), (((3 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((7 : ZMod 12), (4 : ZMod 6)), (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))),
  (((7 : ZMod 12), (4 : ZMod 6)), (((4 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12),
  (4 : ZMod 6)), (((5 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (4 : ZMod 6)),
  (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((7 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12),
  (1 : ZMod 6)), (1 : Fin 2))), (((7 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)),
  (1 : Fin 2))), (((7 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))),
  (((7 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12),
  (5 : ZMod 6)), (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (5 : ZMod 6)),
  (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (5 : ZMod 6)), (((2 : ZMod 12),
  (5 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (5 : ZMod 6)), (((3 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((7 : ZMod 12), (5 : ZMod 6)), (((3 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((7 : ZMod 12), (5 : ZMod 6)), (((4 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12),
  (5 : ZMod 6)), (((5 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((7 : ZMod 12), (5 : ZMod 6)),
  (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((7 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12),
  (2 : ZMod 6)), (1 : Fin 2))), (((7 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)),
  (1 : Fin 2))), (((7 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))),
  (((8 : ZMod 12), (0 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (0 : ZMod 6)), (((2 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (0 : ZMod 6)),
  (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (0 : ZMod 6)), (((4 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (0 : ZMod 6)), (((4 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (0 : ZMod 6)), (((5 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (0 : ZMod 6)), (((6 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (1 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)),
  (((0 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)), (((1 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)), (((2 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)), (((2 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (1 : ZMod 6)), (((2 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (1 : ZMod 6)), (((3 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)),
  (((4 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)), (((4 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)), (((5 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)), (((6 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (1 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((8 : ZMod 12),
  (1 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((8 : ZMod 12), (1 : ZMod 6)),
  (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (2 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)),
  (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)), (((2 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)), (((2 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)), (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (2 : ZMod 6)), (((4 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (2 : ZMod 6)), (((4 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)),
  (((5 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)), (((6 : ZMod 12),
  (2 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)),
  (1 : Fin 2))), (((8 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))),
  (((8 : ZMod 12), (3 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (3 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (3 : ZMod 6)),
  (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (3 : ZMod 6)), (((2 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (3 : ZMod 6)), (((3 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (3 : ZMod 6)), (((4 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (3 : ZMod 6)), (((4 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (3 : ZMod 6)), (((5 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (3 : ZMod 6)),
  (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (3 : ZMod 6)), (((0 : ZMod 12),
  (0 : ZMod 6)), (1 : Fin 2))), (((8 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (4 : ZMod 6)), (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (4 : ZMod 6)), (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (4 : ZMod 6)), (((4 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (4 : ZMod 6)),
  (((4 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (4 : ZMod 6)), (((5 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (4 : ZMod 6)), (((6 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))),
  (((8 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((8 : ZMod 12),
  (4 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((8 : ZMod 12), (4 : ZMod 6)),
  (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12),
  (2 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (5 : ZMod 6)), (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)),
  (((2 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)), (((3 : ZMod 12),
  (5 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)), (((4 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)), (((4 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((8 : ZMod 12), (5 : ZMod 6)), (((5 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12),
  (5 : ZMod 6)), (((6 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)),
  (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12),
  (2 : ZMod 6)), (1 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)),
  (1 : Fin 2))), (((8 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))),
  (((9 : ZMod 12), (0 : ZMod 6)), (((3 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12),
  (0 : ZMod 6)), (((4 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (0 : ZMod 6)),
  (((5 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (0 : ZMod 6)), (((5 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (0 : ZMod 6)), (((6 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((9 : ZMod 12), (0 : ZMod 6)), (((7 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((9 : ZMod 12), (0 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((9 : ZMod 12),
  (1 : ZMod 6)), (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (1 : ZMod 6)),
  (((4 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (1 : ZMod 6)), (((5 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (1 : ZMod 6)), (((5 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((9 : ZMod 12), (1 : ZMod 6)), (((6 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((9 : ZMod 12), (1 : ZMod 6)), (((7 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12),
  (1 : ZMod 6)), (((0 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((9 : ZMod 12), (2 : ZMod 6)),
  (((0 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((9 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((9 : ZMod 12), (2 : ZMod 6)), (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12),
  (2 : ZMod 6)), (((2 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (2 : ZMod 6)),
  (((3 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (2 : ZMod 6)), (((4 : ZMod 12),
  (2 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (2 : ZMod 6)), (((5 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((9 : ZMod 12), (2 : ZMod 6)), (((5 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))),
  (((9 : ZMod 12), (2 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12),
  (2 : ZMod 6)), (((7 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (2 : ZMod 6)),
  (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((9 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12),
  (2 : ZMod 6)), (1 : Fin 2))), (((9 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)),
  (1 : Fin 2))), (((9 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))),
  (((9 : ZMod 12), (3 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12),
  (3 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (3 : ZMod 6)),
  (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (3 : ZMod 6)), (((3 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((9 : ZMod 12), (3 : ZMod 6)), (((4 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((9 : ZMod 12), (3 : ZMod 6)), (((5 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12),
  (3 : ZMod 6)), (((5 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (3 : ZMod 6)),
  (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (3 : ZMod 6)), (((7 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (3 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)),
  (1 : Fin 2))), (((9 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((9 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12),
  (4 : ZMod 6)), (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (4 : ZMod 6)),
  (((2 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (4 : ZMod 6)), (((3 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (4 : ZMod 6)), (((4 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((9 : ZMod 12), (4 : ZMod 6)), (((5 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((9 : ZMod 12), (4 : ZMod 6)), (((5 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12),
  (4 : ZMod 6)), (((6 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (4 : ZMod 6)),
  (((7 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12),
  (0 : ZMod 6)), (1 : Fin 2))), (((9 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (1 : ZMod 6)),
  (1 : Fin 2))), (((9 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))),
  (((9 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((9 : ZMod 12),
  (5 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (5 : ZMod 6)),
  (((0 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((9 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((9 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12),
  (5 : ZMod 6)), (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (5 : ZMod 6)),
  (((1 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (5 : ZMod 6)), (((3 : ZMod 12),
  (2 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (5 : ZMod 6)), (((4 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((9 : ZMod 12), (5 : ZMod 6)), (((5 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((9 : ZMod 12), (5 : ZMod 6)), (((5 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12),
  (5 : ZMod 6)), (((6 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (5 : ZMod 6)),
  (((7 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((9 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12),
  (0 : ZMod 6)), (1 : Fin 2))), (((9 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (2 : ZMod 6)),
  (1 : Fin 2))), (((9 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2))),
  (((10 : ZMod 12), (0 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12),
  (0 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (0 : ZMod 6)),
  (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (0 : ZMod 6)), (((2 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (0 : ZMod 6)), (((4 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((10 : ZMod 12), (0 : ZMod 6)), (((5 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((10 : ZMod 12), (0 : ZMod 6)), (((6 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12),
  (0 : ZMod 6)), (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (0 : ZMod 6)),
  (((7 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (0 : ZMod 6)), (((8 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (1 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((10 : ZMod 12), (1 : ZMod 6)), (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((10 : ZMod 12), (1 : ZMod 6)), (((4 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12),
  (1 : ZMod 6)), (((5 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (1 : ZMod 6)),
  (((6 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (1 : ZMod 6)), (((6 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (1 : ZMod 6)), (((7 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((10 : ZMod 12), (1 : ZMod 6)), (((8 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((10 : ZMod 12), (1 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((10 : ZMod 12),
  (1 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((10 : ZMod 12), (1 : ZMod 6)),
  (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((10 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12), (2 : ZMod 6)),
  (0 : Fin 2))), (((10 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((10 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12),
  (2 : ZMod 6)), (((0 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (2 : ZMod 6)),
  (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12),
  (2 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((10 : ZMod 12), (2 : ZMod 6)), (((2 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((10 : ZMod 12), (2 : ZMod 6)), (((2 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12),
  (2 : ZMod 6)), (((4 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (2 : ZMod 6)),
  (((5 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (2 : ZMod 6)), (((6 : ZMod 12),
  (2 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (2 : ZMod 6)), (((6 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((10 : ZMod 12), (2 : ZMod 6)), (((7 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((10 : ZMod 12), (2 : ZMod 6)), (((8 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12),
  (2 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2))), (((10 : ZMod 12), (2 : ZMod 6)),
  (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((10 : ZMod 12), (3 : ZMod 6)), (((0 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((10 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((10 : ZMod 12), (3 : ZMod 6)), (((2 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12),
  (3 : ZMod 6)), (((4 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (3 : ZMod 6)),
  (((5 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (3 : ZMod 6)), (((6 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (3 : ZMod 6)), (((6 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((10 : ZMod 12), (3 : ZMod 6)), (((7 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((10 : ZMod 12), (3 : ZMod 6)), (((8 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12),
  (3 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((10 : ZMod 12), (4 : ZMod 6)),
  (((0 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((10 : ZMod 12), (4 : ZMod 6)), (((2 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))),
  (((10 : ZMod 12), (4 : ZMod 6)), (((4 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12),
  (4 : ZMod 6)), (((5 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (4 : ZMod 6)),
  (((6 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (4 : ZMod 6)), (((6 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (4 : ZMod 6)), (((7 : ZMod 12), (4 : ZMod 6)),
  (0 : Fin 2))), (((10 : ZMod 12), (4 : ZMod 6)), (((8 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))),
  (((10 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((10 : ZMod 12),
  (5 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (5 : ZMod 6)),
  (((0 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((10 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((10 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12),
  (5 : ZMod 6)), (((1 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (5 : ZMod 6)),
  (((1 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (5 : ZMod 6)), (((2 : ZMod 12),
  (1 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (5 : ZMod 6)), (((2 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((10 : ZMod 12), (5 : ZMod 6)), (((4 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((10 : ZMod 12), (5 : ZMod 6)), (((5 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12),
  (5 : ZMod 6)), (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (5 : ZMod 6)),
  (((6 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (5 : ZMod 6)), (((7 : ZMod 12),
  (5 : ZMod 6)), (0 : Fin 2))), (((10 : ZMod 12), (5 : ZMod 6)), (((8 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((10 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))),
  (((10 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (2 : ZMod 6)), (1 : Fin 2))), (((10 : ZMod 12),
  (5 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2))), (((11 : ZMod 12), (0 : ZMod 6)),
  (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (0 : ZMod 6)), (((2 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (0 : ZMod 6)), (((3 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((11 : ZMod 12), (0 : ZMod 6)), (((5 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))),
  (((11 : ZMod 12), (0 : ZMod 6)), (((6 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12),
  (0 : ZMod 6)), (((7 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (0 : ZMod 6)),
  (((7 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (0 : ZMod 6)), (((8 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (0 : ZMod 6)), (((9 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((11 : ZMod 12), (0 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))),
  (((11 : ZMod 12), (1 : ZMod 6)), (((1 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12),
  (1 : ZMod 6)), (((2 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (1 : ZMod 6)),
  (((3 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (1 : ZMod 6)), (((5 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (1 : ZMod 6)), (((6 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((11 : ZMod 12), (1 : ZMod 6)), (((7 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((11 : ZMod 12), (1 : ZMod 6)), (((7 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12),
  (1 : ZMod 6)), (((8 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (1 : ZMod 6)),
  (((9 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (1 : ZMod 6)), (((0 : ZMod 12),
  (1 : ZMod 6)), (1 : Fin 2))), (((11 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)),
  (0 : Fin 2))), (((11 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))),
  (((11 : ZMod 12), (2 : ZMod 6)), (((0 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12),
  (2 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (2 : ZMod 6)),
  (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12),
  (5 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (2 : ZMod 6)), (((2 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((11 : ZMod 12), (2 : ZMod 6)), (((2 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((11 : ZMod 12), (2 : ZMod 6)), (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12),
  (2 : ZMod 6)), (((5 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (2 : ZMod 6)),
  (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (2 : ZMod 6)), (((7 : ZMod 12),
  (2 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (2 : ZMod 6)), (((7 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((11 : ZMod 12), (2 : ZMod 6)), (((8 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((11 : ZMod 12), (2 : ZMod 6)), (((9 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12),
  (2 : ZMod 6)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2))), (((11 : ZMod 12), (2 : ZMod 6)),
  (((0 : ZMod 12), (2 : ZMod 6)), (1 : Fin 2))), (((11 : ZMod 12), (2 : ZMod 6)), (((1 : ZMod 12),
  (1 : ZMod 6)), (1 : Fin 2))), (((11 : ZMod 12), (3 : ZMod 6)), (((0 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((11 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((11 : ZMod 12), (3 : ZMod 6)), (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12),
  (3 : ZMod 6)), (((2 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (3 : ZMod 6)),
  (((3 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (3 : ZMod 6)), (((5 : ZMod 12),
  (0 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (3 : ZMod 6)), (((6 : ZMod 12), (3 : ZMod 6)),
  (0 : Fin 2))), (((11 : ZMod 12), (3 : ZMod 6)), (((7 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((11 : ZMod 12), (3 : ZMod 6)), (((7 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12),
  (3 : ZMod 6)), (((8 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (3 : ZMod 6)),
  (((9 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (4 : ZMod 6)), (((0 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((11 : ZMod 12), (4 : ZMod 6)), (((1 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))),
  (((11 : ZMod 12), (4 : ZMod 6)), (((2 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12),
  (4 : ZMod 6)), (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (4 : ZMod 6)),
  (((5 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (4 : ZMod 6)), (((6 : ZMod 12),
  (4 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (4 : ZMod 6)), (((7 : ZMod 12), (1 : ZMod 6)),
  (0 : Fin 2))), (((11 : ZMod 12), (4 : ZMod 6)), (((7 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))),
  (((11 : ZMod 12), (4 : ZMod 6)), (((8 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12),
  (4 : ZMod 6)), (((9 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (5 : ZMod 6)),
  (((0 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12),
  (3 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (5 : ZMod 6)), (((0 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((11 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))),
  (((11 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12),
  (5 : ZMod 6)), (((1 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (5 : ZMod 6)),
  (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (5 : ZMod 6)), (((2 : ZMod 12),
  (5 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (5 : ZMod 6)), (((3 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((11 : ZMod 12), (5 : ZMod 6)), (((5 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))),
  (((11 : ZMod 12), (5 : ZMod 6)), (((6 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12),
  (5 : ZMod 6)), (((7 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (5 : ZMod 6)),
  (((7 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (5 : ZMod 6)), (((8 : ZMod 12),
  (5 : ZMod 6)), (0 : Fin 2))), (((11 : ZMod 12), (5 : ZMod 6)), (((9 : ZMod 12), (5 : ZMod 6)),
  (0 : Fin 2))), (((11 : ZMod 12), (5 : ZMod 6)), (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2)))]

/-- 12 X-logical cycle representatives (qubit supports). -/
def logX : List (List (GrossGroup × Fin 2)) := [[(((0 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)), (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((2 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)), (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((4 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)), (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((7 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)), (((8 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((8 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)), (((9 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((10 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))], [(((0 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)),
  (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((2 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)),
  (((2 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)), (((3 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)),
  (((4 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((6 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)),
  (((7 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((8 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)),
  (((8 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)), (((9 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)),
  (((10 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))], [(((0 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)),
  (((1 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)), (((2 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((2 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((4 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)), (((6 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)),
  (((7 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)), (((8 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((8 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((9 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((10 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))], [(((0 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)), (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((2 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)), (((3 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((4 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)), (((6 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((7 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)), (((8 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((8 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)), (((9 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((10 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))], [(((0 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)), (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((2 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)), (((3 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((5 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)), (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((7 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)), (((7 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((8 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)), (((9 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((11 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2))], [(((0 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)),
  (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((1 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)),
  (((2 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)), (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)),
  (((5 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((6 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)),
  (((7 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((7 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)),
  (((8 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)), (((9 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)),
  (((11 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2))], [(((0 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((0 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((0 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((0 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((1 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2)),
  (((0 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2)), (((0 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2)),
  (((0 : ZMod 12), (4 : ZMod 6)), (1 : Fin 2))], [(((0 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((0 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)), (((0 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((0 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((1 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)), (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((1 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2)),
  (((0 : ZMod 12), (2 : ZMod 6)), (1 : Fin 2)), (((0 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2)),
  (((0 : ZMod 12), (5 : ZMod 6)), (1 : Fin 2))], [(((0 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((0 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((0 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((0 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((1 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)), (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((2 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)), (((0 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2)),
  (((0 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2)), (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2)),
  (((1 : ZMod 12), (2 : ZMod 6)), (1 : Fin 2))], [(((0 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((0 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((1 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)), (((2 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)),
  (((2 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2)),
  (((0 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2)), (((0 : ZMod 12), (2 : ZMod 6)), (1 : Fin 2)),
  (((0 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2)), (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2)),
  (((1 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2))], [(((0 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((0 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)), (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)),
  (((1 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)), (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((1 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)), (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((2 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2)),
  (((0 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2)), (((0 : ZMod 12), (2 : ZMod 6)), (1 : Fin 2)),
  (((0 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2)), (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2)),
  (((1 : ZMod 12), (4 : ZMod 6)), (1 : Fin 2))], [(((0 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((0 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((0 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)),
  (((0 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((1 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((1 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((2 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)),
  (((2 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2)),
  (((0 : ZMod 12), (2 : ZMod 6)), (1 : Fin 2)), (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2)),
  (((1 : ZMod 12), (5 : ZMod 6)), (1 : Fin 2))]]

/-- 12 Z-logical dual-cycle representatives (qubit supports). -/
def logZ : List (List (GrossGroup × Fin 2)) := [[(((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((2 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((2 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)), (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)), (((4 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((4 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)), (((4 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)),
  (((5 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)), (((5 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)),
  (((5 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)), (((5 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((5 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)), (((5 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)),
  (((6 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)), (((6 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)),
  (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)), (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((6 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)), (((6 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)),
  (((7 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)), (((7 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)),
  (((7 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)), (((7 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((7 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)), (((7 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)),
  (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2)), (((0 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2)),
  (((1 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2)), (((2 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2)),
  (((2 : ZMod 12), (2 : ZMod 6)), (1 : Fin 2))], [(((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)),
  (((1 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)), (((2 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)), (((3 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)),
  (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)), (((3 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)), (((3 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)),
  (((4 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)), (((4 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)),
  (((4 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)), (((4 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((4 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)), (((4 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)),
  (((5 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((5 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((5 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((8 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((8 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((8 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((8 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)), (((8 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)),
  (((8 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((0 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2)),
  (((0 : ZMod 12), (2 : ZMod 6)), (1 : Fin 2)), (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2)),
  (((2 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2)), (((2 : ZMod 12), (2 : ZMod 6)), (1 : Fin 2)),
  (((2 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2))], [(((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((1 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)), (((2 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)), (((3 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)),
  (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)), (((3 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)), (((3 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)),
  (((5 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((5 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((5 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((8 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((8 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((8 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((8 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)), (((8 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)),
  (((8 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2)),
  (((0 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2)), (((0 : ZMod 12), (2 : ZMod 6)), (1 : Fin 2)),
  (((0 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2)), (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2)),
  (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2)), (((1 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2)),
  (((2 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2)), (((2 : ZMod 12), (2 : ZMod 6)), (1 : Fin 2)),
  (((2 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2))], [(((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((1 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)), (((2 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)),
  (((2 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)), (((2 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)), (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)), (((4 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((4 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((4 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((4 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)), (((4 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)),
  (((4 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((5 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((5 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)), (((5 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)),
  (((6 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)), (((6 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)),
  (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)), (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((6 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)), (((6 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)),
  (((8 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)), (((8 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)),
  (((8 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)), (((8 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((8 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)), (((8 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)),
  (((0 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2)), (((0 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2)),
  (((0 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2)), (((1 : ZMod 12), (2 : ZMod 6)), (1 : Fin 2)),
  (((2 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2))], [(((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((2 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((2 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((4 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)), (((4 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)),
  (((4 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)), (((4 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((4 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)), (((4 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)),
  (((5 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((5 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((5 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((8 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((8 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((8 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((8 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)), (((8 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)),
  (((8 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2)),
  (((1 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2)), (((1 : ZMod 12), (2 : ZMod 6)), (1 : Fin 2)),
  (((2 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2)), (((2 : ZMod 12), (1 : ZMod 6)), (1 : Fin 2)),
  (((2 : ZMod 12), (2 : ZMod 6)), (1 : Fin 2))], [(((2 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((2 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)), (((5 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((5 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((5 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((5 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)), (((5 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)),
  (((5 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((1 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2)),
  (((1 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2)), (((2 : ZMod 12), (0 : ZMod 6)), (1 : Fin 2)),
  (((2 : ZMod 12), (3 : ZMod 6)), (1 : Fin 2))], [(((0 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)),
  (((0 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)), (((0 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((0 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)), (((3 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((3 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((6 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)),
  (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)), (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((6 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)), (((9 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)),
  (((9 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2))], [(((0 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((0 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)), (((0 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)),
  (((0 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)), (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)), (((6 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)),
  (((6 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((9 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((9 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2))], [(((0 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((0 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)), (((0 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)),
  (((0 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((1 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((1 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)), (((4 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)),
  (((4 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)), (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)), (((6 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)),
  (((6 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((7 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((7 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((7 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((7 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((9 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((9 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)), (((10 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)),
  (((10 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))], [(((0 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((0 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)), (((1 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((1 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)), (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((3 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((3 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)), (((4 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((4 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((4 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((4 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)), (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((6 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)), (((7 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((7 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)), (((9 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((9 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((9 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((9 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)), (((10 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((10 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((10 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((10 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))], [(((0 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((0 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((1 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)),
  (((1 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((3 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((3 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)),
  (((3 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((4 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((4 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)), (((6 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((6 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)), (((7 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((7 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((7 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)),
  (((7 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((9 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((9 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((9 : ZMod 12), (4 : ZMod 6)), (0 : Fin 2)),
  (((9 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((10 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((10 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2))], [(((0 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)),
  (((0 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)), (((1 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((1 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((1 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((1 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((3 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((3 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((3 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((3 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((4 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)),
  (((4 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)), (((6 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)),
  (((6 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2)), (((7 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((7 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((7 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((7 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((9 : ZMod 12), (0 : ZMod 6)), (0 : Fin 2)),
  (((9 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)), (((9 : ZMod 12), (2 : ZMod 6)), (0 : Fin 2)),
  (((9 : ZMod 12), (5 : ZMod 6)), (0 : Fin 2)), (((10 : ZMod 12), (1 : ZMod 6)), (0 : Fin 2)),
  (((10 : ZMod 12), (3 : ZMod 6)), (0 : Fin 2))]]

/-! ## §2  Sparse boundary terms and the decoder identities

`∂₂(δ_f)` and `cutMap(δ_v)` are sparse point-mass images; evaluating them
through these few-term forms (rather than `conv`) keeps the `native_decide`
sweeps cheap. -/

/-- `∂₂(δ_f)` evaluated at qubit `(h, j)`:  `A(h-f)` on the left block,
`B(h-f)` on the right. -/
def d2term (f h : GrossGroup) (j : Fin 2) : ZMod 2 :=
  if j = 0 then grossA (h - f) else grossB (h - f)

/-- `cutMap(δ_v)` evaluated at qubit `(h, j)`:  `B(v-h)` on the left block,
`A(v-h)` on the right. -/
def cmTerm (v h : GrossGroup) (j : Fin 2) : ZMod 2 :=
  if j = 0 then grossB (v - h) else grossA (v - h)

/-- Apply the `phiX` decoder to `∂₂(δ_p)`, read at output face `p'`. -/
def decodeXAt (p p' : GrossGroup) : ZMod 2 :=
  (phiX.filter (fun pr => pr.1 = p')).foldl
    (fun acc pr => acc + d2term p pr.2.1 pr.2.2) 0

/-- Apply the `phiZ` decoder to `cutMap(δ_p)`, read at output vertex `p'`. -/
def decodeZAt (p p' : GrossGroup) : ZMod 2 :=
  (phiZ.filter (fun pr => pr.1 = p')).foldl
    (fun acc pr => acc + cmTerm p pr.2.1 pr.2.2) 0

/-- Kernel-basis correction term `Σ_j [p = dropSet j] · (red j)(p')`. -/
def kerCorrection (red : List (List GrossGroup)) (p p' : GrossGroup) : ZMod 2 :=
  ((List.range 6).filter (fun j => dropSet.getD j 0 = p)).foldl
    (fun acc j => acc + (if (red.getD j []).contains p' then 1 else 0)) 0

/-- **Face decoder identity** (validated `native_decide`, ~5 s): the `phiX`
decoder inverts `∂₂` on the trimmed face subspace, modulo the `redP2` kernel
basis. Over all `72×72` basis pairs. This is the independence hard-core for
the X block — it yields `∂₂ f = 0 ∧ f|_dropSet = 0 → f = 0` by linearity. -/
theorem decoder_identity_X :
    ∀ p p' : GrossGroup,
      decodeXAt p p' + kerCorrection redP2 p p' = (if p' = p then 1 else 0) := by
  native_decide

/-- **Vertex decoder identity** (validated `native_decide`): mirror of
`decoder_identity_X` for the Z block (`cutMap`, `phiZ`, `redCM`). -/
theorem decoder_identity_Z :
    ∀ p p' : GrossGroup,
      decodeZAt p p' + kerCorrection redCM p p' = (if p' = p then 1 else 0) := by
  native_decide

/-! ## §3  Lift the decoder identities to all chains (the independence core)

`decoder_identity_X` is a per-basis-vector fact; here we lift it by linearity
to `face_kernel_trivial : ∂₂ f = 0 ∧ f|_dropSet = 0 → f = 0` (and the mirror
`vtx_kernel_trivial`). These feed the block-split `rowsLinearIndependent`. -/

/-- A `ZMod 2`-valued left fold with `+` from `0` is the sum of the mapped list. -/
private lemma foldl_add_eq_sum {α : Type*} (l : List α) (g : α → ZMod 2) :
    l.foldl (fun acc x => acc + g x) 0 = (l.map g).sum := by
  have gen : ∀ (a : ZMod 2), l.foldl (fun acc x => acc + g x) a = a + (l.map g).sum := by
    induction l with
    | nil => intro a; simp
    | cons x xs ih => intro a; simp [ih (a + g x), add_assoc]
  simpa using gen 0

/-- **(L1, X)** Basis expansion of `∂₂` in the sparse `d2term` form. -/
lemma boundary2_apply_eq_sum_d2term (f : GrossGroup → ZMod 2) (h : GrossGroup) (j : Fin 2) :
    grossComplex.boundary2 f (h, j) = ∑ p : GrossGroup, f p * d2term p h j := by
  have hgr : grossComplex.boundary2 f = bbBoundary2Fn grossA grossB f := rfl
  rw [hgr]
  by_cases hj : j = 0
  · subst hj
    change conv grossA f h = ∑ p : GrossGroup, f p * d2term p h 0
    rw [conv_apply]
    refine (Equiv.sum_comp (Equiv.subLeft h) (fun x => grossA x * f (h - x))).symm.trans ?_
    refine Finset.sum_congr rfl fun p _ => ?_
    have hp : h - (h - p) = p := by abel
    simp [d2term, Equiv.subLeft_apply, hp, mul_comm]
  · have hj1 : j = 1 := by omega
    subst hj1
    change conv grossB f h = ∑ p : GrossGroup, f p * d2term p h 1
    rw [conv_apply]
    refine (Equiv.sum_comp (Equiv.subLeft h) (fun x => grossB x * f (h - x))).symm.trans ?_
    refine Finset.sum_congr rfl fun p _ => ?_
    have hp : h - (h - p) = p := by abel
    simp [d2term, Equiv.subLeft_apply, hp, mul_comm]

/-- **(L1, Z)** `cutMap(δ_v)` per qubit, in the sparse `cmTerm` form. -/
lemma cmTerm_eq (v h : GrossGroup) (j : Fin 2) :
    grossComplex.boundary1 (Pi.single (h, j) 1) v = cmTerm v h j := by
  have hgr : grossComplex.boundary1 (Pi.single (h, j) (1:ZMod 2))
      = bbBoundary1Fn grossA grossB (Pi.single (h, j) 1) := rfl
  rw [hgr, bbBoundary1Fn]
  by_cases hj : j = 0
  · subst hj
    have hL : leftHalf (Pi.single ((h, (0:Fin 2))) (1:ZMod 2)) = Pi.single h 1 := by
      funext g; simp [leftHalf, Pi.single_apply, Prod.ext_iff]
    have hR : rightHalf (Pi.single ((h, (0:Fin 2))) (1:ZMod 2)) = 0 := by
      funext g; simp [rightHalf, Prod.ext_iff]
    rw [hL, hR, conv_comm grossB (Pi.single h 1), conv_single_left_apply]
    simp [cmTerm, conv_apply]
  · have hj1 : j = 1 := by omega
    subst hj1
    have hL : leftHalf (Pi.single ((h, (1:Fin 2))) (1:ZMod 2)) = 0 := by
      funext g; simp [leftHalf, Prod.ext_iff]
    have hR : rightHalf (Pi.single ((h, (1:Fin 2))) (1:ZMod 2)) = Pi.single h 1 := by
      funext g; simp [rightHalf, Pi.single_apply, Prod.ext_iff]
    rw [hL, hR, conv_comm grossA (Pi.single h 1), conv_single_left_apply]
    simp [cmTerm, conv_apply]

lemma cutMap_apply_eq_sum_cmTerm (s : GrossGroup → ZMod 2) (h : GrossGroup) (j : Fin 2) :
    grossComplex.cutMap s (h, j) = ∑ v : GrossGroup, s v * cmTerm v h j := by
  rw [HomologicalCode.cutMap_apply]
  exact Finset.sum_congr rfl fun v _ => by rw [cmTerm_eq]

/-- Interchange a `Fintype` sum with a `List` sum (over `ZMod 2`). -/
private lemma finset_sum_list_sum_comm {ι α : Type*} [Fintype ι] (l : List α)
    (k : ι → α → ZMod 2) :
    ∑ p : ι, (l.map (k p)).sum = (l.map (fun x => ∑ p : ι, k p x)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

/-- `kerCorrection` vanishes off the drop-set. -/
private lemma kerCorrection_eq_zero_of_not_mem (red : List (List GrossGroup)) {p : GrossGroup}
    (hp : p ∉ dropSet) (p' : GrossGroup) : kerCorrection red p p' = 0 := by
  have hempty : (List.range 6).filter (fun j => dropSet.getD j 0 = p) = [] := by
    rw [List.filter_eq_nil_iff]
    intro j hj hcond
    rw [List.mem_range] at hj
    have hlen : dropSet.length = 6 := by decide
    have hmem : dropSet.getD j 0 ∈ dropSet := by
      rw [List.getD_eq_getElem dropSet 0 (by omega)]; exact List.getElem_mem _
    have : dropSet.getD j 0 = p := by simpa using hcond
    exact hp (this ▸ hmem)
  rw [kerCorrection, hempty]; rfl

/-- **(A, X)** A `∂₂`-cycle makes the `phiX`-decoder sum vanish. -/
lemma sum_decodeXAt_eq_zero_of_boundary {f : GrossGroup → ZMod 2}
    (hf : grossComplex.boundary2 f = 0) (p' : GrossGroup) :
    ∑ p : GrossGroup, f p * decodeXAt p p' = 0 := by
  have hstep : ∀ p : GrossGroup, f p * decodeXAt p p'
      = ((phiX.filter (fun pr => pr.1 = p')).map
          (fun pr => f p * d2term p pr.2.1 pr.2.2)).sum := fun p => by
    rw [decodeXAt, foldl_add_eq_sum, List.sum_map_mul_left]
  simp_rw [hstep]
  rw [finset_sum_list_sum_comm]
  have hz : ∀ pr : GrossGroup × (GrossGroup × Fin 2),
      (∑ p : GrossGroup, f p * d2term p pr.2.1 pr.2.2) = 0 := fun pr => by
    rw [← boundary2_apply_eq_sum_d2term, hf]; rfl
  simp [hz]

/-- **(A, Z)** A `cutMap`-kernel chain makes the `phiZ`-decoder sum vanish. -/
lemma sum_decodeZAt_eq_zero_of_cutMap {s : GrossGroup → ZMod 2}
    (hs : grossComplex.cutMap s = 0) (p' : GrossGroup) :
    ∑ v : GrossGroup, s v * decodeZAt v p' = 0 := by
  have hstep : ∀ v : GrossGroup, s v * decodeZAt v p'
      = ((phiZ.filter (fun pr => pr.1 = p')).map
          (fun pr => s v * cmTerm v pr.2.1 pr.2.2)).sum := fun v => by
    rw [decodeZAt, foldl_add_eq_sum, List.sum_map_mul_left]
  simp_rw [hstep]
  rw [finset_sum_list_sum_comm]
  have hz : ∀ pr : GrossGroup × (GrossGroup × Fin 2),
      (∑ v : GrossGroup, s v * cmTerm v pr.2.1 pr.2.2) = 0 := fun pr => by
    rw [← cutMap_apply_eq_sum_cmTerm, hs]; rfl
  simp [hz]

/-- **Face block independence core**: a `∂₂`-cycle vanishing on `dropSet` is `0`. -/
lemma face_kernel_trivial {f : GrossGroup → ZMod 2}
    (hf : grossComplex.boundary2 f = 0) (hd : ∀ d ∈ dropSet, f d = 0) : f = 0 := by
  funext p'
  have hId : ∀ p, decodeXAt p p' = (if p' = p then 1 else 0) + kerCorrection redP2 p p' :=
    fun p => by rw [← decoder_identity_X p p', add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hA := sum_decodeXAt_eq_zero_of_boundary hf p'
  simp_rw [hId, mul_add, Finset.sum_add_distrib] at hA
  have hfirst : (∑ p : GrossGroup, f p * (if p' = p then (1:ZMod 2) else 0)) = f p' := by
    rw [Finset.sum_eq_single p']
    · simp
    · intro b _ hb; rw [if_neg (Ne.symm hb)]; ring
    · intro h; exact absurd (Finset.mem_univ p') h
  have hsecond : (∑ p : GrossGroup, f p * kerCorrection redP2 p p') = 0 := by
    refine Finset.sum_eq_zero fun p _ => ?_
    by_cases hpd : p ∈ dropSet
    · rw [hd p hpd]; ring
    · rw [kerCorrection_eq_zero_of_not_mem redP2 hpd]; ring
  rw [hfirst, hsecond, add_zero] at hA
  exact hA

/-- **Vertex block independence core**: a `cutMap`-kernel chain vanishing on
`dropSet` is `0`. -/
lemma vtx_kernel_trivial {s : GrossGroup → ZMod 2}
    (hs : grossComplex.cutMap s = 0) (hd : ∀ d ∈ dropSet, s d = 0) : s = 0 := by
  funext p'
  have hId : ∀ v, decodeZAt v p' = (if p' = v then 1 else 0) + kerCorrection redCM v p' :=
    fun v => by rw [← decoder_identity_Z v p', add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hA := sum_decodeZAt_eq_zero_of_cutMap hs p'
  simp_rw [hId, mul_add, Finset.sum_add_distrib] at hA
  have hfirst : (∑ v : GrossGroup, s v * (if p' = v then (1:ZMod 2) else 0)) = s p' := by
    rw [Finset.sum_eq_single p']
    · simp
    · intro b _ hb; rw [if_neg (Ne.symm hb)]; ring
    · intro h; exact absurd (Finset.mem_univ p') h
  have hsecond : (∑ v : GrossGroup, s v * kerCorrection redCM v p') = 0 := by
    refine Finset.sum_eq_zero fun v _ => ?_
    by_cases hvd : v ∈ dropSet
    · rw [hd v hvd]; ring
    · rw [kerCorrection_eq_zero_of_not_mem redCM hvd]; ring
  rw [hfirst, hsecond, add_zero] at hA
  exact hA

/-! ## §4  Closure equality (obligation 1)

The trimmed 132-generator list (66 kept vertex stabs ++ 66 kept face stabs)
generates the same subgroup as the full homological generator set. The dropped
generators re-enter via the reduced kernel relations `redP2` / `redCM`. -/

-- NB: list-mapped generators must be typed `List grossComplex.C2` / `.C0`, not
-- `List GrossGroup`: the projection `C2`/`C0` is defeq but not syntactically
-- `GrossGroup`, which silently breaks `rw`/`simp` list-lemma matching.

/-- Product of face stabs over a list = `chainXOperator (∂₂ (Σ indicators))`. -/
lemma faceStabOf_listProd (L : List grossComplex.C2) :
    (L.map grossComplex.faceStabOf).prod
      = grossComplex.chainXOperator
          (grossComplex.boundary2 ((L.map (fun f => grossComplex.singleFace f)).sum)) := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.sum_nil, map_zero,
      HomologicalCode.chainXOperator_zero]
  | cons f L ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.sum_cons, map_add,
      HomologicalCode.chainXOperator_add, HomologicalCode.chainXOperator_boundary2_singleFace, ih]

/-- Product of vertex stabs over a list = `chainZOperator (cutMap (Σ indicators))`. -/
lemma vertexStabOf_listProd (L : List grossComplex.C0) :
    (L.map grossComplex.vertexStabOf).prod
      = grossComplex.chainZOperator
          (grossComplex.cutMap ((L.map (fun v => grossComplex.singleVtx v)).sum)) := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.sum_nil, map_zero,
      HomologicalCode.chainZOperator_zero]
  | cons v L ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.sum_cons, map_add,
      HomologicalCode.chainZOperator_add, HomologicalCode.chainZOperator_cutMap_singleVtx, ih]

/-! ## §4b  Boundary-column bridges and the per-drop closure relations -/

lemma boundary2_singleFace_apply (d : GrossGroup) (h : GrossGroup) (j : Fin 2) :
    grossComplex.boundary2 (grossComplex.singleFace d) (h, j) = d2term d h j := by
  rw [boundary2_apply_eq_sum_d2term]
  have hpt : ∀ p : GrossGroup, grossComplex.singleFace d p = (if p = d then 1 else 0) :=
    fun p => by rw [HomologicalCode.singleFace]; exact Pi.single_apply d 1 p
  simp [hpt, Finset.sum_ite_eq']

lemma boundary2_listSum_singleFace_apply (L : List grossComplex.C2) (h : GrossGroup) (j : Fin 2) :
    grossComplex.boundary2 ((L.map (fun f => grossComplex.singleFace f)).sum) (h, j)
      = (L.map (fun f : grossComplex.C2 => d2term f h j)).sum := by
  induction L with
  | nil => simp only [List.map_nil, List.sum_nil, map_zero]; rfl
  | cons f L ih =>
    rw [List.map_cons, List.sum_cons, map_add, Pi.add_apply, boundary2_singleFace_apply, ih,
        List.map_cons, List.sum_cons]


def keptCoords : List GrossGroup := [((0 : ZMod 12), (4 : ZMod 6)), ((0 : ZMod 12), (5 : ZMod 6)),
  ((1 : ZMod 12), (2 : ZMod 6)), ((1 : ZMod 12), (3 : ZMod 6)), ((1 : ZMod 12), (4 : ZMod 6)),
  ((1 : ZMod 12), (5 : ZMod 6)), ((2 : ZMod 12), (0 : ZMod 6)), ((2 : ZMod 12), (1 : ZMod 6)),
  ((2 : ZMod 12), (2 : ZMod 6)), ((2 : ZMod 12), (3 : ZMod 6)), ((2 : ZMod 12), (4 : ZMod 6)),
  ((2 : ZMod 12), (5 : ZMod 6)), ((3 : ZMod 12), (0 : ZMod 6)), ((3 : ZMod 12), (1 : ZMod 6)),
  ((3 : ZMod 12), (2 : ZMod 6)), ((3 : ZMod 12), (3 : ZMod 6)), ((3 : ZMod 12), (4 : ZMod 6)),
  ((3 : ZMod 12), (5 : ZMod 6)), ((4 : ZMod 12), (0 : ZMod 6)), ((4 : ZMod 12), (1 : ZMod 6)),
  ((4 : ZMod 12), (2 : ZMod 6)), ((4 : ZMod 12), (3 : ZMod 6)), ((4 : ZMod 12), (4 : ZMod 6)),
  ((4 : ZMod 12), (5 : ZMod 6)), ((5 : ZMod 12), (0 : ZMod 6)), ((5 : ZMod 12), (1 : ZMod 6)),
  ((5 : ZMod 12), (2 : ZMod 6)), ((5 : ZMod 12), (3 : ZMod 6)), ((5 : ZMod 12), (4 : ZMod 6)),
  ((5 : ZMod 12), (5 : ZMod 6)), ((6 : ZMod 12), (0 : ZMod 6)), ((6 : ZMod 12), (1 : ZMod 6)),
  ((6 : ZMod 12), (2 : ZMod 6)), ((6 : ZMod 12), (3 : ZMod 6)), ((6 : ZMod 12), (4 : ZMod 6)),
  ((6 : ZMod 12), (5 : ZMod 6)), ((7 : ZMod 12), (0 : ZMod 6)), ((7 : ZMod 12), (1 : ZMod 6)),
  ((7 : ZMod 12), (2 : ZMod 6)), ((7 : ZMod 12), (3 : ZMod 6)), ((7 : ZMod 12), (4 : ZMod 6)),
  ((7 : ZMod 12), (5 : ZMod 6)), ((8 : ZMod 12), (0 : ZMod 6)), ((8 : ZMod 12), (1 : ZMod 6)),
  ((8 : ZMod 12), (2 : ZMod 6)), ((8 : ZMod 12), (3 : ZMod 6)), ((8 : ZMod 12), (4 : ZMod 6)),
  ((8 : ZMod 12), (5 : ZMod 6)), ((9 : ZMod 12), (0 : ZMod 6)), ((9 : ZMod 12), (1 : ZMod 6)),
  ((9 : ZMod 12), (2 : ZMod 6)), ((9 : ZMod 12), (3 : ZMod 6)), ((9 : ZMod 12), (4 : ZMod 6)),
  ((9 : ZMod 12), (5 : ZMod 6)), ((10 : ZMod 12), (0 : ZMod 6)), ((10 : ZMod 12), (1 : ZMod 6)),
  ((10 : ZMod 12), (2 : ZMod 6)), ((10 : ZMod 12), (3 : ZMod 6)), ((10 : ZMod 12), (4 : ZMod 6)),
  ((10 : ZMod 12), (5 : ZMod 6)), ((11 : ZMod 12), (0 : ZMod 6)), ((11 : ZMod 12), (1 : ZMod 6)),
  ((11 : ZMod 12), (2 : ZMod 6)), ((11 : ZMod 12), (3 : ZMod 6)), ((11 : ZMod 12), (4 : ZMod 6)),
  ((11 : ZMod 12), (5 : ZMod 6))]

def keptPartX : List (List GrossGroup) := [[((0 : ZMod 12), (4 : ZMod 6)), ((1 : ZMod 12),
  (2 : ZMod 6)), ((1 : ZMod 12), (4 : ZMod 6)), ((2 : ZMod 12), (3 : ZMod 6)), ((2 : ZMod 12),
  (5 : ZMod 6)), ((3 : ZMod 12), (0 : ZMod 6)), ((3 : ZMod 12), (1 : ZMod 6)), ((3 : ZMod 12),
  (2 : ZMod 6)), ((3 : ZMod 12), (5 : ZMod 6)), ((4 : ZMod 12), (0 : ZMod 6)), ((4 : ZMod 12),
  (3 : ZMod 6)), ((4 : ZMod 12), (4 : ZMod 6)), ((4 : ZMod 12), (5 : ZMod 6)), ((5 : ZMod 12),
  (0 : ZMod 6)), ((5 : ZMod 12), (1 : ZMod 6)), ((5 : ZMod 12), (4 : ZMod 6)), ((5 : ZMod 12),
  (5 : ZMod 6)), ((6 : ZMod 12), (0 : ZMod 6)), ((6 : ZMod 12), (4 : ZMod 6)), ((7 : ZMod 12),
  (2 : ZMod 6)), ((7 : ZMod 12), (4 : ZMod 6)), ((8 : ZMod 12), (3 : ZMod 6)), ((8 : ZMod 12),
  (5 : ZMod 6)), ((9 : ZMod 12), (0 : ZMod 6)), ((9 : ZMod 12), (1 : ZMod 6)), ((9 : ZMod 12),
  (2 : ZMod 6)), ((9 : ZMod 12), (5 : ZMod 6)), ((10 : ZMod 12), (0 : ZMod 6)), ((10 : ZMod 12),
  (3 : ZMod 6)), ((10 : ZMod 12), (4 : ZMod 6)), ((10 : ZMod 12), (5 : ZMod 6)), ((11 : ZMod 12),
  (0 : ZMod 6)), ((11 : ZMod 12), (1 : ZMod 6)), ((11 : ZMod 12), (4 : ZMod 6)), ((11 : ZMod 12),
  (5 : ZMod 6))], [((0 : ZMod 12), (5 : ZMod 6)), ((1 : ZMod 12), (3 : ZMod 6)), ((1 : ZMod 12),
  (5 : ZMod 6)), ((2 : ZMod 12), (0 : ZMod 6)), ((2 : ZMod 12), (4 : ZMod 6)), ((3 : ZMod 12),
  (0 : ZMod 6)), ((3 : ZMod 12), (1 : ZMod 6)), ((3 : ZMod 12), (2 : ZMod 6)), ((3 : ZMod 12),
  (3 : ZMod 6)), ((4 : ZMod 12), (0 : ZMod 6)), ((4 : ZMod 12), (1 : ZMod 6)), ((4 : ZMod 12),
  (4 : ZMod 6)), ((4 : ZMod 12), (5 : ZMod 6)), ((5 : ZMod 12), (0 : ZMod 6)), ((5 : ZMod 12),
  (1 : ZMod 6)), ((5 : ZMod 12), (2 : ZMod 6)), ((5 : ZMod 12), (5 : ZMod 6)), ((6 : ZMod 12),
  (1 : ZMod 6)), ((6 : ZMod 12), (5 : ZMod 6)), ((7 : ZMod 12), (3 : ZMod 6)), ((7 : ZMod 12),
  (5 : ZMod 6)), ((8 : ZMod 12), (0 : ZMod 6)), ((8 : ZMod 12), (4 : ZMod 6)), ((9 : ZMod 12),
  (0 : ZMod 6)), ((9 : ZMod 12), (1 : ZMod 6)), ((9 : ZMod 12), (2 : ZMod 6)), ((9 : ZMod 12),
  (3 : ZMod 6)), ((10 : ZMod 12), (0 : ZMod 6)), ((10 : ZMod 12), (1 : ZMod 6)), ((10 : ZMod 12),
  (4 : ZMod 6)), ((10 : ZMod 12), (5 : ZMod 6)), ((11 : ZMod 12), (0 : ZMod 6)), ((11 : ZMod 12),
  (1 : ZMod 6)), ((11 : ZMod 12), (2 : ZMod 6)), ((11 : ZMod 12), (5 : ZMod 6))], [((0 : ZMod 12),
  (4 : ZMod 6)), ((1 : ZMod 12), (3 : ZMod 6)), ((1 : ZMod 12), (5 : ZMod 6)), ((2 : ZMod 12),
  (0 : ZMod 6)), ((2 : ZMod 12), (1 : ZMod 6)), ((2 : ZMod 12), (2 : ZMod 6)), ((2 : ZMod 12),
  (5 : ZMod 6)), ((3 : ZMod 12), (0 : ZMod 6)), ((3 : ZMod 12), (3 : ZMod 6)), ((3 : ZMod 12),
  (4 : ZMod 6)), ((3 : ZMod 12), (5 : ZMod 6)), ((4 : ZMod 12), (0 : ZMod 6)), ((4 : ZMod 12),
  (1 : ZMod 6)), ((4 : ZMod 12), (4 : ZMod 6)), ((4 : ZMod 12), (5 : ZMod 6)), ((5 : ZMod 12),
  (0 : ZMod 6)), ((5 : ZMod 12), (4 : ZMod 6)), ((6 : ZMod 12), (2 : ZMod 6)), ((6 : ZMod 12),
  (4 : ZMod 6)), ((7 : ZMod 12), (3 : ZMod 6)), ((7 : ZMod 12), (5 : ZMod 6)), ((8 : ZMod 12),
  (0 : ZMod 6)), ((8 : ZMod 12), (1 : ZMod 6)), ((8 : ZMod 12), (2 : ZMod 6)), ((8 : ZMod 12),
  (5 : ZMod 6)), ((9 : ZMod 12), (0 : ZMod 6)), ((9 : ZMod 12), (3 : ZMod 6)), ((9 : ZMod 12),
  (4 : ZMod 6)), ((9 : ZMod 12), (5 : ZMod 6)), ((10 : ZMod 12), (0 : ZMod 6)), ((10 : ZMod 12),
  (1 : ZMod 6)), ((10 : ZMod 12), (4 : ZMod 6)), ((10 : ZMod 12), (5 : ZMod 6)), ((11 : ZMod 12),
  (0 : ZMod 6)), ((11 : ZMod 12), (4 : ZMod 6))], [((0 : ZMod 12), (5 : ZMod 6)), ((1 : ZMod 12),
  (2 : ZMod 6)), ((1 : ZMod 12), (3 : ZMod 6)), ((1 : ZMod 12), (4 : ZMod 6)), ((1 : ZMod 12),
  (5 : ZMod 6)), ((2 : ZMod 12), (1 : ZMod 6)), ((2 : ZMod 12), (5 : ZMod 6)), ((3 : ZMod 12),
  (0 : ZMod 6)), ((3 : ZMod 12), (1 : ZMod 6)), ((3 : ZMod 12), (4 : ZMod 6)), ((3 : ZMod 12),
  (5 : ZMod 6)), ((4 : ZMod 12), (1 : ZMod 6)), ((4 : ZMod 12), (3 : ZMod 6)), ((5 : ZMod 12),
  (0 : ZMod 6)), ((5 : ZMod 12), (1 : ZMod 6)), ((5 : ZMod 12), (2 : ZMod 6)), ((5 : ZMod 12),
  (3 : ZMod 6)), ((6 : ZMod 12), (3 : ZMod 6)), ((6 : ZMod 12), (5 : ZMod 6)), ((7 : ZMod 12),
  (2 : ZMod 6)), ((7 : ZMod 12), (3 : ZMod 6)), ((7 : ZMod 12), (4 : ZMod 6)), ((7 : ZMod 12),
  (5 : ZMod 6)), ((8 : ZMod 12), (1 : ZMod 6)), ((8 : ZMod 12), (5 : ZMod 6)), ((9 : ZMod 12),
  (0 : ZMod 6)), ((9 : ZMod 12), (1 : ZMod 6)), ((9 : ZMod 12), (4 : ZMod 6)), ((9 : ZMod 12),
  (5 : ZMod 6)), ((10 : ZMod 12), (1 : ZMod 6)), ((10 : ZMod 12), (3 : ZMod 6)), ((11 : ZMod 12),
  (0 : ZMod 6)), ((11 : ZMod 12), (1 : ZMod 6)), ((11 : ZMod 12), (2 : ZMod 6)), ((11 : ZMod 12),
  (3 : ZMod 6))], [((1 : ZMod 12), (2 : ZMod 6)), ((1 : ZMod 12), (3 : ZMod 6)), ((1 : ZMod 12),
  (5 : ZMod 6)), ((2 : ZMod 12), (0 : ZMod 6)), ((2 : ZMod 12), (2 : ZMod 6)), ((2 : ZMod 12),
  (3 : ZMod 6)), ((2 : ZMod 12), (5 : ZMod 6)), ((4 : ZMod 12), (0 : ZMod 6)), ((4 : ZMod 12),
  (2 : ZMod 6)), ((4 : ZMod 12), (3 : ZMod 6)), ((4 : ZMod 12), (5 : ZMod 6)), ((5 : ZMod 12),
  (0 : ZMod 6)), ((5 : ZMod 12), (2 : ZMod 6)), ((5 : ZMod 12), (3 : ZMod 6)), ((5 : ZMod 12),
  (5 : ZMod 6)), ((7 : ZMod 12), (0 : ZMod 6)), ((7 : ZMod 12), (2 : ZMod 6)), ((7 : ZMod 12),
  (3 : ZMod 6)), ((7 : ZMod 12), (5 : ZMod 6)), ((8 : ZMod 12), (0 : ZMod 6)), ((8 : ZMod 12),
  (2 : ZMod 6)), ((8 : ZMod 12), (3 : ZMod 6)), ((8 : ZMod 12), (5 : ZMod 6)), ((10 : ZMod 12),
  (0 : ZMod 6)), ((10 : ZMod 12), (2 : ZMod 6)), ((10 : ZMod 12), (3 : ZMod 6)), ((10 : ZMod 12),
  (5 : ZMod 6)), ((11 : ZMod 12), (0 : ZMod 6)), ((11 : ZMod 12), (2 : ZMod 6)), ((11 : ZMod 12),
  (3 : ZMod 6)), ((11 : ZMod 12), (5 : ZMod 6))], [((1 : ZMod 12), (2 : ZMod 6)), ((1 : ZMod 12),
  (4 : ZMod 6)), ((1 : ZMod 12), (5 : ZMod 6)), ((2 : ZMod 12), (1 : ZMod 6)), ((2 : ZMod 12),
  (2 : ZMod 6)), ((2 : ZMod 12), (4 : ZMod 6)), ((2 : ZMod 12), (5 : ZMod 6)), ((4 : ZMod 12),
  (1 : ZMod 6)), ((4 : ZMod 12), (2 : ZMod 6)), ((4 : ZMod 12), (4 : ZMod 6)), ((4 : ZMod 12),
  (5 : ZMod 6)), ((5 : ZMod 12), (1 : ZMod 6)), ((5 : ZMod 12), (2 : ZMod 6)), ((5 : ZMod 12),
  (4 : ZMod 6)), ((5 : ZMod 12), (5 : ZMod 6)), ((7 : ZMod 12), (1 : ZMod 6)), ((7 : ZMod 12),
  (2 : ZMod 6)), ((7 : ZMod 12), (4 : ZMod 6)), ((7 : ZMod 12), (5 : ZMod 6)), ((8 : ZMod 12),
  (1 : ZMod 6)), ((8 : ZMod 12), (2 : ZMod 6)), ((8 : ZMod 12), (4 : ZMod 6)), ((8 : ZMod 12),
  (5 : ZMod 6)), ((10 : ZMod 12), (1 : ZMod 6)), ((10 : ZMod 12), (2 : ZMod 6)), ((10 : ZMod 12),
  (4 : ZMod 6)), ((10 : ZMod 12), (5 : ZMod 6)), ((11 : ZMod 12), (1 : ZMod 6)), ((11 : ZMod 12),
  (2 : ZMod 6)), ((11 : ZMod 12), (4 : ZMod 6)), ((11 : ZMod 12), (5 : ZMod 6))]]

/-- Generic drop relation: if `df`'s boundary column equals the sum of `kp`'s
columns (a kernel relation) and each `kp` face stab is in `S`, then
`faceStabOf df ∈ closure S`. -/
lemma faceStab_drop_mem_closure {S : Set (NQubitPauliGroupElement grossComplex.numQubits)}
    (df : GrossGroup) (kp : List grossComplex.C2)
    (hrel : ∀ (h : GrossGroup) (j : Fin 2),
       d2term df h j = (kp.map (fun f : grossComplex.C2 => d2term f h j)).sum)
    (hkept : ∀ f ∈ kp, grossComplex.faceStabOf f ∈ S) :
    grossComplex.faceStabOf df ∈ Subgroup.closure S := by
  have hbd : grossComplex.boundary2 (grossComplex.singleFace df)
      = grossComplex.boundary2 ((kp.map (fun f => grossComplex.singleFace f)).sum) := by
    funext q; obtain ⟨h, j⟩ := q
    rw [boundary2_singleFace_apply, boundary2_listSum_singleFace_apply]
    exact hrel h j
  have heq : grossComplex.faceStabOf df = (kp.map grossComplex.faceStabOf).prod := by
    rw [faceStabOf_listProd, ← HomologicalCode.chainXOperator_boundary2_singleFace, hbd]
  rw [heq]
  exact Subgroup.list_prod_mem _ (fun g hg => by
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
    exact Subgroup.subset_closure (hkept f hf))

def keptPartZ : List (List GrossGroup) := [[((0 : ZMod 12), (4 : ZMod 6)), ((1 : ZMod 12),
  (2 : ZMod 6)), ((1 : ZMod 12), (4 : ZMod 6)), ((2 : ZMod 12), (1 : ZMod 6)), ((2 : ZMod 12),
  (2 : ZMod 6)), ((2 : ZMod 12), (3 : ZMod 6)), ((2 : ZMod 12), (4 : ZMod 6)), ((3 : ZMod 12),
  (2 : ZMod 6)), ((3 : ZMod 12), (3 : ZMod 6)), ((3 : ZMod 12), (4 : ZMod 6)), ((3 : ZMod 12),
  (5 : ZMod 6)), ((4 : ZMod 12), (0 : ZMod 6)), ((4 : ZMod 12), (1 : ZMod 6)), ((4 : ZMod 12),
  (2 : ZMod 6)), ((4 : ZMod 12), (3 : ZMod 6)), ((5 : ZMod 12), (3 : ZMod 6)), ((5 : ZMod 12),
  (5 : ZMod 6)), ((6 : ZMod 12), (0 : ZMod 6)), ((6 : ZMod 12), (4 : ZMod 6)), ((7 : ZMod 12),
  (2 : ZMod 6)), ((7 : ZMod 12), (4 : ZMod 6)), ((8 : ZMod 12), (1 : ZMod 6)), ((8 : ZMod 12),
  (2 : ZMod 6)), ((8 : ZMod 12), (3 : ZMod 6)), ((8 : ZMod 12), (4 : ZMod 6)), ((9 : ZMod 12),
  (2 : ZMod 6)), ((9 : ZMod 12), (3 : ZMod 6)), ((9 : ZMod 12), (4 : ZMod 6)), ((9 : ZMod 12),
  (5 : ZMod 6)), ((10 : ZMod 12), (0 : ZMod 6)), ((10 : ZMod 12), (1 : ZMod 6)), ((10 : ZMod 12),
  (2 : ZMod 6)), ((10 : ZMod 12), (3 : ZMod 6)), ((11 : ZMod 12), (3 : ZMod 6)), ((11 : ZMod 12),
  (5 : ZMod 6))], [((0 : ZMod 12), (5 : ZMod 6)), ((1 : ZMod 12), (3 : ZMod 6)), ((1 : ZMod 12),
  (5 : ZMod 6)), ((2 : ZMod 12), (2 : ZMod 6)), ((2 : ZMod 12), (3 : ZMod 6)), ((2 : ZMod 12),
  (4 : ZMod 6)), ((2 : ZMod 12), (5 : ZMod 6)), ((3 : ZMod 12), (0 : ZMod 6)), ((3 : ZMod 12),
  (3 : ZMod 6)), ((3 : ZMod 12), (4 : ZMod 6)), ((3 : ZMod 12), (5 : ZMod 6)), ((4 : ZMod 12),
  (1 : ZMod 6)), ((4 : ZMod 12), (2 : ZMod 6)), ((4 : ZMod 12), (3 : ZMod 6)), ((4 : ZMod 12),
  (4 : ZMod 6)), ((5 : ZMod 12), (0 : ZMod 6)), ((5 : ZMod 12), (4 : ZMod 6)), ((6 : ZMod 12),
  (1 : ZMod 6)), ((6 : ZMod 12), (5 : ZMod 6)), ((7 : ZMod 12), (3 : ZMod 6)), ((7 : ZMod 12),
  (5 : ZMod 6)), ((8 : ZMod 12), (2 : ZMod 6)), ((8 : ZMod 12), (3 : ZMod 6)), ((8 : ZMod 12),
  (4 : ZMod 6)), ((8 : ZMod 12), (5 : ZMod 6)), ((9 : ZMod 12), (0 : ZMod 6)), ((9 : ZMod 12),
  (3 : ZMod 6)), ((9 : ZMod 12), (4 : ZMod 6)), ((9 : ZMod 12), (5 : ZMod 6)), ((10 : ZMod 12),
  (1 : ZMod 6)), ((10 : ZMod 12), (2 : ZMod 6)), ((10 : ZMod 12), (3 : ZMod 6)), ((10 : ZMod 12),
  (4 : ZMod 6)), ((11 : ZMod 12), (0 : ZMod 6)), ((11 : ZMod 12), (4 : ZMod 6))], [((0 : ZMod 12),
  (4 : ZMod 6)), ((1 : ZMod 12), (3 : ZMod 6)), ((1 : ZMod 12), (5 : ZMod 6)), ((2 : ZMod 12),
  (1 : ZMod 6)), ((2 : ZMod 12), (3 : ZMod 6)), ((3 : ZMod 12), (0 : ZMod 6)), ((3 : ZMod 12),
  (1 : ZMod 6)), ((3 : ZMod 12), (2 : ZMod 6)), ((3 : ZMod 12), (3 : ZMod 6)), ((4 : ZMod 12),
  (1 : ZMod 6)), ((4 : ZMod 12), (2 : ZMod 6)), ((4 : ZMod 12), (3 : ZMod 6)), ((4 : ZMod 12),
  (4 : ZMod 6)), ((5 : ZMod 12), (0 : ZMod 6)), ((5 : ZMod 12), (1 : ZMod 6)), ((5 : ZMod 12),
  (2 : ZMod 6)), ((5 : ZMod 12), (5 : ZMod 6)), ((6 : ZMod 12), (2 : ZMod 6)), ((6 : ZMod 12),
  (4 : ZMod 6)), ((7 : ZMod 12), (3 : ZMod 6)), ((7 : ZMod 12), (5 : ZMod 6)), ((8 : ZMod 12),
  (1 : ZMod 6)), ((8 : ZMod 12), (3 : ZMod 6)), ((9 : ZMod 12), (0 : ZMod 6)), ((9 : ZMod 12),
  (1 : ZMod 6)), ((9 : ZMod 12), (2 : ZMod 6)), ((9 : ZMod 12), (3 : ZMod 6)), ((10 : ZMod 12),
  (1 : ZMod 6)), ((10 : ZMod 12), (2 : ZMod 6)), ((10 : ZMod 12), (3 : ZMod 6)), ((10 : ZMod 12),
  (4 : ZMod 6)), ((11 : ZMod 12), (0 : ZMod 6)), ((11 : ZMod 12), (1 : ZMod 6)), ((11 : ZMod 12),
  (2 : ZMod 6)), ((11 : ZMod 12), (5 : ZMod 6))], [((0 : ZMod 12), (5 : ZMod 6)), ((1 : ZMod 12),
  (2 : ZMod 6)), ((1 : ZMod 12), (3 : ZMod 6)), ((1 : ZMod 12), (4 : ZMod 6)), ((1 : ZMod 12),
  (5 : ZMod 6)), ((2 : ZMod 12), (0 : ZMod 6)), ((2 : ZMod 12), (3 : ZMod 6)), ((2 : ZMod 12),
  (4 : ZMod 6)), ((2 : ZMod 12), (5 : ZMod 6)), ((3 : ZMod 12), (1 : ZMod 6)), ((3 : ZMod 12),
  (2 : ZMod 6)), ((3 : ZMod 12), (3 : ZMod 6)), ((3 : ZMod 12), (4 : ZMod 6)), ((4 : ZMod 12),
  (0 : ZMod 6)), ((4 : ZMod 12), (4 : ZMod 6)), ((5 : ZMod 12), (1 : ZMod 6)), ((5 : ZMod 12),
  (5 : ZMod 6)), ((6 : ZMod 12), (3 : ZMod 6)), ((6 : ZMod 12), (5 : ZMod 6)), ((7 : ZMod 12),
  (2 : ZMod 6)), ((7 : ZMod 12), (3 : ZMod 6)), ((7 : ZMod 12), (4 : ZMod 6)), ((7 : ZMod 12),
  (5 : ZMod 6)), ((8 : ZMod 12), (0 : ZMod 6)), ((8 : ZMod 12), (3 : ZMod 6)), ((8 : ZMod 12),
  (4 : ZMod 6)), ((8 : ZMod 12), (5 : ZMod 6)), ((9 : ZMod 12), (1 : ZMod 6)), ((9 : ZMod 12),
  (2 : ZMod 6)), ((9 : ZMod 12), (3 : ZMod 6)), ((9 : ZMod 12), (4 : ZMod 6)), ((10 : ZMod 12),
  (0 : ZMod 6)), ((10 : ZMod 12), (4 : ZMod 6)), ((11 : ZMod 12), (1 : ZMod 6)), ((11 : ZMod 12),
  (5 : ZMod 6))], [((1 : ZMod 12), (2 : ZMod 6)), ((1 : ZMod 12), (3 : ZMod 6)), ((1 : ZMod 12),
  (5 : ZMod 6)), ((2 : ZMod 12), (0 : ZMod 6)), ((2 : ZMod 12), (2 : ZMod 6)), ((2 : ZMod 12),
  (3 : ZMod 6)), ((2 : ZMod 12), (5 : ZMod 6)), ((4 : ZMod 12), (0 : ZMod 6)), ((4 : ZMod 12),
  (2 : ZMod 6)), ((4 : ZMod 12), (3 : ZMod 6)), ((4 : ZMod 12), (5 : ZMod 6)), ((5 : ZMod 12),
  (0 : ZMod 6)), ((5 : ZMod 12), (2 : ZMod 6)), ((5 : ZMod 12), (3 : ZMod 6)), ((5 : ZMod 12),
  (5 : ZMod 6)), ((7 : ZMod 12), (0 : ZMod 6)), ((7 : ZMod 12), (2 : ZMod 6)), ((7 : ZMod 12),
  (3 : ZMod 6)), ((7 : ZMod 12), (5 : ZMod 6)), ((8 : ZMod 12), (0 : ZMod 6)), ((8 : ZMod 12),
  (2 : ZMod 6)), ((8 : ZMod 12), (3 : ZMod 6)), ((8 : ZMod 12), (5 : ZMod 6)), ((10 : ZMod 12),
  (0 : ZMod 6)), ((10 : ZMod 12), (2 : ZMod 6)), ((10 : ZMod 12), (3 : ZMod 6)), ((10 : ZMod 12),
  (5 : ZMod 6)), ((11 : ZMod 12), (0 : ZMod 6)), ((11 : ZMod 12), (2 : ZMod 6)), ((11 : ZMod 12),
  (3 : ZMod 6)), ((11 : ZMod 12), (5 : ZMod 6))], [((1 : ZMod 12), (2 : ZMod 6)), ((1 : ZMod 12),
  (4 : ZMod 6)), ((1 : ZMod 12), (5 : ZMod 6)), ((2 : ZMod 12), (1 : ZMod 6)), ((2 : ZMod 12),
  (2 : ZMod 6)), ((2 : ZMod 12), (4 : ZMod 6)), ((2 : ZMod 12), (5 : ZMod 6)), ((4 : ZMod 12),
  (1 : ZMod 6)), ((4 : ZMod 12), (2 : ZMod 6)), ((4 : ZMod 12), (4 : ZMod 6)), ((4 : ZMod 12),
  (5 : ZMod 6)), ((5 : ZMod 12), (1 : ZMod 6)), ((5 : ZMod 12), (2 : ZMod 6)), ((5 : ZMod 12),
  (4 : ZMod 6)), ((5 : ZMod 12), (5 : ZMod 6)), ((7 : ZMod 12), (1 : ZMod 6)), ((7 : ZMod 12),
  (2 : ZMod 6)), ((7 : ZMod 12), (4 : ZMod 6)), ((7 : ZMod 12), (5 : ZMod 6)), ((8 : ZMod 12),
  (1 : ZMod 6)), ((8 : ZMod 12), (2 : ZMod 6)), ((8 : ZMod 12), (4 : ZMod 6)), ((8 : ZMod 12),
  (5 : ZMod 6)), ((10 : ZMod 12), (1 : ZMod 6)), ((10 : ZMod 12), (2 : ZMod 6)), ((10 : ZMod 12),
  (4 : ZMod 6)), ((10 : ZMod 12), (5 : ZMod 6)), ((11 : ZMod 12), (1 : ZMod 6)), ((11 : ZMod 12),
  (2 : ZMod 6)), ((11 : ZMod 12), (4 : ZMod 6)), ((11 : ZMod 12), (5 : ZMod 6))]]

lemma cutMap_singleVtx_apply (v : GrossGroup) (h : GrossGroup) (j : Fin 2) :
    grossComplex.cutMap (grossComplex.singleVtx v) (h, j) = cmTerm v h j := by
  rw [cutMap_apply_eq_sum_cmTerm]
  have hpt : ∀ w : GrossGroup, grossComplex.singleVtx v w = (if w = v then 1 else 0) :=
    fun w => by rw [HomologicalCode.singleVtx]; exact Pi.single_apply v 1 w
  simp [hpt, Finset.sum_ite_eq']

lemma cutMap_listSum_singleVtx_apply (L : List grossComplex.C0) (h : GrossGroup) (j : Fin 2) :
    grossComplex.cutMap ((L.map (fun v => grossComplex.singleVtx v)).sum) (h, j)
      = (L.map (fun v : grossComplex.C0 => cmTerm v h j)).sum := by
  induction L with
  | nil => simp only [List.map_nil, List.sum_nil, map_zero]; rfl
  | cons v L ih =>
    rw [List.map_cons, List.sum_cons, map_add, Pi.add_apply, cutMap_singleVtx_apply, ih,
        List.map_cons, List.sum_cons]

lemma vertexStab_drop_mem_closure {S : Set (NQubitPauliGroupElement grossComplex.numQubits)}
    (dv : GrossGroup) (kp : List grossComplex.C0)
    (hrel : ∀ (h : GrossGroup) (j : Fin 2),
       cmTerm dv h j = (kp.map (fun v : grossComplex.C0 => cmTerm v h j)).sum)
    (hkept : ∀ v ∈ kp, grossComplex.vertexStabOf v ∈ S) :
    grossComplex.vertexStabOf dv ∈ Subgroup.closure S := by
  have hbd : grossComplex.cutMap (grossComplex.singleVtx dv)
      = grossComplex.cutMap ((kp.map (fun v => grossComplex.singleVtx v)).sum) := by
    funext q; obtain ⟨h, j⟩ := q
    rw [cutMap_singleVtx_apply, cutMap_listSum_singleVtx_apply]
    exact hrel h j
  have heq : grossComplex.vertexStabOf dv = (kp.map grossComplex.vertexStabOf).prod := by
    rw [vertexStabOf_listProd, ← HomologicalCode.chainZOperator_cutMap_singleVtx, hbd]
  rw [heq]
  exact Subgroup.list_prod_mem _ (fun g hg => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hg
    exact Subgroup.subset_closure (hkept v hv))

/-! ## §4c  Trimmed generator lists and closure equality -/

noncomputable def genListX : List (NQubitPauliGroupElement grossComplex.numQubits) :=
  keptCoords.map grossComplex.faceStabOf

noncomputable def genListZ : List (NQubitPauliGroupElement grossComplex.numQubits) :=
  keptCoords.map grossComplex.vertexStabOf

noncomputable def genListPackaged : List (NQubitPauliGroupElement grossComplex.numQubits) :=
  genListZ ++ genListX

lemma cover : ∀ f : GrossGroup, f ∈ keptCoords ∨ f ∈ dropSet := by native_decide

lemma faceStab_kept_mem {f : GrossGroup} (hk : f ∈ keptCoords) :
    grossComplex.faceStabOf f ∈ listToSet genListPackaged :=
  List.mem_append_right _ (List.mem_map.mpr ⟨f, hk, rfl⟩)

lemma vtxStab_kept_mem {v : GrossGroup} (hk : v ∈ keptCoords) :
    grossComplex.vertexStabOf v ∈ listToSet genListPackaged :=
  List.mem_append_left _ (List.mem_map.mpr ⟨v, hk, rfl⟩)

lemma faceStabOf_mem_closure (f : GrossGroup) :
    grossComplex.faceStabOf f ∈ Subgroup.closure (listToSet genListPackaged) := by
  rcases cover f with hk | hd
  · exact Subgroup.subset_closure (faceStab_kept_mem hk)
  · simp only [dropSet, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    · exact faceStab_drop_mem_closure _ (keptPartX.getD 0 []) (by native_decide)
        (fun f' hf' => faceStab_kept_mem
          ((by native_decide : ∀ x ∈ keptPartX.getD 0 [], x ∈ keptCoords) f' hf'))
    · exact faceStab_drop_mem_closure _ (keptPartX.getD 1 []) (by native_decide)
        (fun f' hf' => faceStab_kept_mem
          ((by native_decide : ∀ x ∈ keptPartX.getD 1 [], x ∈ keptCoords) f' hf'))
    · exact faceStab_drop_mem_closure _ (keptPartX.getD 2 []) (by native_decide)
        (fun f' hf' => faceStab_kept_mem
          ((by native_decide : ∀ x ∈ keptPartX.getD 2 [], x ∈ keptCoords) f' hf'))
    · exact faceStab_drop_mem_closure _ (keptPartX.getD 3 []) (by native_decide)
        (fun f' hf' => faceStab_kept_mem
          ((by native_decide : ∀ x ∈ keptPartX.getD 3 [], x ∈ keptCoords) f' hf'))
    · exact faceStab_drop_mem_closure _ (keptPartX.getD 4 []) (by native_decide)
        (fun f' hf' => faceStab_kept_mem
          ((by native_decide : ∀ x ∈ keptPartX.getD 4 [], x ∈ keptCoords) f' hf'))
    · exact faceStab_drop_mem_closure _ (keptPartX.getD 5 []) (by native_decide)
        (fun f' hf' => faceStab_kept_mem
          ((by native_decide : ∀ x ∈ keptPartX.getD 5 [], x ∈ keptCoords) f' hf'))

lemma vertexStabOf_mem_closure (v : GrossGroup) :
    grossComplex.vertexStabOf v ∈ Subgroup.closure (listToSet genListPackaged) := by
  rcases cover v with hk | hd
  · exact Subgroup.subset_closure (vtxStab_kept_mem hk)
  · simp only [dropSet, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    · exact vertexStab_drop_mem_closure _ (keptPartZ.getD 0 []) (by native_decide)
        (fun v' hv' => vtxStab_kept_mem
          ((by native_decide : ∀ x ∈ keptPartZ.getD 0 [], x ∈ keptCoords) v' hv'))
    · exact vertexStab_drop_mem_closure _ (keptPartZ.getD 1 []) (by native_decide)
        (fun v' hv' => vtxStab_kept_mem
          ((by native_decide : ∀ x ∈ keptPartZ.getD 1 [], x ∈ keptCoords) v' hv'))
    · exact vertexStab_drop_mem_closure _ (keptPartZ.getD 2 []) (by native_decide)
        (fun v' hv' => vtxStab_kept_mem
          ((by native_decide : ∀ x ∈ keptPartZ.getD 2 [], x ∈ keptCoords) v' hv'))
    · exact vertexStab_drop_mem_closure _ (keptPartZ.getD 3 []) (by native_decide)
        (fun v' hv' => vtxStab_kept_mem
          ((by native_decide : ∀ x ∈ keptPartZ.getD 3 [], x ∈ keptCoords) v' hv'))
    · exact vertexStab_drop_mem_closure _ (keptPartZ.getD 4 []) (by native_decide)
        (fun v' hv' => vtxStab_kept_mem
          ((by native_decide : ∀ x ∈ keptPartZ.getD 4 [], x ∈ keptCoords) v' hv'))
    · exact vertexStab_drop_mem_closure _ (keptPartZ.getD 5 []) (by native_decide)
        (fun v' hv' => vtxStab_kept_mem
          ((by native_decide : ∀ x ∈ keptPartZ.getD 5 [], x ∈ keptCoords) v' hv'))

/-- **Closure equality**: the trimmed 132-generator list generates exactly the
gross homological stabilizer subgroup. -/
lemma closure_packaged_eq :
    Subgroup.closure (listToSet genListPackaged)
      = grossComplex.homologicalStabilizerGroup.toSubgroup := by
  rw [HomologicalCode.homologicalStabilizerGroup_toSubgroup]
  apply le_antisymm
  · refine Subgroup.closure_mono ?_
    intro g hg
    have hgl : g ∈ genListPackaged := hg
    rw [genListPackaged, List.mem_append] at hgl
    rcases hgl with hz | hx
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hz
      exact Or.inl ⟨v, rfl⟩
    · obtain ⟨f, _, rfl⟩ := List.mem_map.mp hx
      exact Or.inr ⟨f, rfl⟩
  · refine (Subgroup.closure_le _).mpr ?_
    rintro g (hz | hx)
    · obtain ⟨v, rfl⟩ := hz; exact vertexStabOf_mem_closure v
    · obtain ⟨f, rfl⟩ := hx; exact faceStabOf_mem_closure f

/-! ## §5a  Symplectic-row bridges (for `rowsLinearIndependent`) -/

private lemma zmod2_dich (a : ZMod 2) : a = 0 ∨ a = 1 := by
  rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- Z-half symplectic entry of a vertex stab = the cutMap chain value at that edge. -/
lemma vertexStabOf_sympl_Z (v : grossComplex.C0) (i : Fin grossComplex.numQubits) :
    NQubitPauliOperator.toSymplectic (grossComplex.vertexStabOf v).operators
        (Fin.natAdd grossComplex.numQubits i)
      = grossComplex.cutMap (grossComplex.singleVtx v) (grossComplex.edgeEquiv.symm i) := by
  rw [NQubitPauliOperator.toSymplectic_Z_part]
  change ((grossComplex.chainZOperator (grossComplex.cutMap (grossComplex.singleVtx v))).operators
    i).toSymplecticSingle.2 = _
  rw [HomologicalCode.chainZOperator_op_at]
  set c := grossComplex.cutMap (grossComplex.singleVtx v) with hc
  by_cases h : ∃ e, grossComplex.edgeEquiv e = i ∧ c e = 1
  · obtain ⟨e, he, hce⟩ := h
    rw [if_pos ⟨e, he, hce⟩]
    have : grossComplex.edgeEquiv.symm i = e := by rw [← he, Equiv.symm_apply_apply]
    rw [this, hce]; rfl
  · rw [if_neg h]
    have hz : c (grossComplex.edgeEquiv.symm i) = 0 := by
      rcases zmod2_dich (c (grossComplex.edgeEquiv.symm i)) with h0 | h1
      · exact h0
      · exact absurd ⟨grossComplex.edgeEquiv.symm i, Equiv.apply_symm_apply _ _, h1⟩ h
    rw [hz]; rfl

/-- X-half symplectic entry of a face stab = the boundary2 chain value at that edge. -/
lemma faceStabOf_sympl_X (f : grossComplex.C2) (i : Fin grossComplex.numQubits) :
    NQubitPauliOperator.toSymplectic (grossComplex.faceStabOf f).operators
        (Fin.castAdd grossComplex.numQubits i)
      = grossComplex.boundary2 (grossComplex.singleFace f) (grossComplex.edgeEquiv.symm i) := by
  rw [NQubitPauliOperator.toSymplectic_X_part]
  change ((grossComplex.chainXOperator (grossComplex.boundary2 (grossComplex.singleFace f))).operators
    i).toSymplecticSingle.1 = _
  rw [HomologicalCode.chainXOperator_op_at]
  set c := grossComplex.boundary2 (grossComplex.singleFace f) with hc
  by_cases h : ∃ e, grossComplex.edgeEquiv e = i ∧ c e = 1
  · obtain ⟨e, he, hce⟩ := h
    rw [if_pos ⟨e, he, hce⟩]
    have : grossComplex.edgeEquiv.symm i = e := by rw [← he, Equiv.symm_apply_apply]
    rw [this, hce]; rfl
  · rw [if_neg h]
    have hz : c (grossComplex.edgeEquiv.symm i) = 0 := by
      rcases zmod2_dich (c (grossComplex.edgeEquiv.symm i)) with h0 | h1
      · exact h0
      · exact absurd ⟨grossComplex.edgeEquiv.symm i, Equiv.apply_symm_apply _ _, h1⟩ h
    rw [hz]; rfl

/-- A vertex stab (Z-type) has zero X-half symplectic entries. -/
lemma vertexStabOf_sympl_X_zero (v : grossComplex.C0) (i : Fin grossComplex.numQubits) :
    NQubitPauliOperator.toSymplectic (grossComplex.vertexStabOf v).operators
        (Fin.castAdd grossComplex.numQubits i) = 0 := by
  rw [NQubitPauliOperator.toSymplectic_X_part]
  rcases (HomologicalCode.vertexStabOf_isZType v).2 i with hI | hZ
  · rw [hI]; rfl
  · rw [hZ]; rfl

/-- A face stab (X-type) has zero Z-half symplectic entries. -/
lemma faceStabOf_sympl_Z_zero (f : grossComplex.C2) (i : Fin grossComplex.numQubits) :
    NQubitPauliOperator.toSymplectic (grossComplex.faceStabOf f).operators
        (Fin.natAdd grossComplex.numQubits i) = 0 := by
  rw [NQubitPauliOperator.toSymplectic_Z_part]
  rcases (HomologicalCode.faceStabOf_isXType f).2 i with hI | hX
  · rw [hI]; rfl
  · rw [hX]; rfl

/-! ## §5b  Coefficient-collapse helpers (consume the kernel-trivial cores) -/

lemma keptCoords_nodup : keptCoords.Nodup := by native_decide

private lemma singleVtx_apply' (a b : GrossGroup) :
    grossComplex.singleVtx a b = if b = a then (1 : ZMod 2) else 0 := by
  rw [HomologicalCode.singleVtx]; exact Pi.single_apply a 1 b

private lemma singleFace_apply' (a b : GrossGroup) :
    grossComplex.singleFace a b = if b = a then (1 : ZMod 2) else 0 := by
  rw [HomologicalCode.singleFace]; exact Pi.single_apply a 1 b

private lemma keptCoords_get_not_dropSet (i : Fin keptCoords.length) :
    (keptCoords.get i : GrossGroup) ∉ dropSet := by
  have hmem : (keptCoords.get i) ∈ keptCoords := List.get_mem _ _
  have hsub : ∀ x ∈ keptCoords, x ∉ dropSet := by native_decide
  exact hsub _ hmem

lemma combo_singleVtx_kernel_zero (c : Fin keptCoords.length → ZMod 2)
    (hker : grossComplex.cutMap
      (∑ i, c i • grossComplex.singleVtx (keptCoords.get i)) = 0) :
    ∀ i, c i = 0 := by
  set s := ∑ i, c i • grossComplex.singleVtx (keptCoords.get i) with hs
  have hd : ∀ d ∈ dropSet, s d = 0 := by
    intro d hdmem
    rw [hs, Finset.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hne : d ≠ keptCoords.get i := fun h => keptCoords_get_not_dropSet i (h ▸ hdmem)
    simp only [Pi.smul_apply, singleVtx_apply', smul_eq_mul, if_neg hne, mul_zero]
  have hs0 : s = 0 := vtx_kernel_trivial hker hd
  intro j
  have hsj := congr_fun hs0 (keptCoords.get j)
  rw [hs, Finset.sum_apply, Finset.sum_eq_single j] at hsj
  · simpa [singleVtx_apply'] using hsj
  · intro i _ hij
    have hne : keptCoords.get j ≠ keptCoords.get i :=
      fun h => hij (List.nodup_iff_injective_get.mp keptCoords_nodup h.symm)
    simp only [Pi.smul_apply, singleVtx_apply', smul_eq_mul, if_neg hne, mul_zero]
  · intro hc; exact absurd (Finset.mem_univ j) hc

lemma combo_singleFace_kernel_zero (c : Fin keptCoords.length → ZMod 2)
    (hker : grossComplex.boundary2
      (∑ i, c i • grossComplex.singleFace (keptCoords.get i)) = 0) :
    ∀ i, c i = 0 := by
  set s := ∑ i, c i • grossComplex.singleFace (keptCoords.get i) with hs
  have hd : ∀ d ∈ dropSet, s d = 0 := by
    intro d hdmem
    rw [hs, Finset.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hne : d ≠ keptCoords.get i := fun h => keptCoords_get_not_dropSet i (h ▸ hdmem)
    simp only [Pi.smul_apply, singleFace_apply', smul_eq_mul, if_neg hne, mul_zero]
  have hs0 : s = 0 := face_kernel_trivial hker hd
  intro j
  have hsj := congr_fun hs0 (keptCoords.get j)
  rw [hs, Finset.sum_apply, Finset.sum_eq_single j] at hsj
  · simpa [singleFace_apply'] using hsj
  · intro i _ hij
    have hne : keptCoords.get j ≠ keptCoords.get i :=
      fun h => hij (List.nodup_iff_injective_get.mp keptCoords_nodup h.symm)
    simp only [Pi.smul_apply, singleFace_apply', smul_eq_mul, if_neg hne, mul_zero]
  · intro hc; exact absurd (Finset.mem_univ j) hc

/-! ## §5c  Packaged-list indexing -/

lemma genListPackaged_length :
    genListPackaged.length = keptCoords.length + keptCoords.length := by
  have h : genListPackaged.length = (keptCoords.map grossComplex.vertexStabOf).length
    + (keptCoords.map grossComplex.faceStabOf).length := rfl
  simpa [List.length_map] using h

lemma get_packaged_Z (i : Fin keptCoords.length)
    (hi : i.val < genListPackaged.length) :
    genListPackaged.get ⟨i.val, hi⟩ = grossComplex.vertexStabOf (keptCoords.get i) := by
  have hlt : i.val < (keptCoords.map grossComplex.vertexStabOf).length := by
    rw [List.length_map]; exact i.isLt
  change (keptCoords.map grossComplex.vertexStabOf
    ++ keptCoords.map grossComplex.faceStabOf).get ⟨i.val, hi⟩ = _
  rw [List.get_eq_getElem, List.getElem_append_left hlt, List.getElem_map]
  rfl

set_option maxRecDepth 4096 in
lemma get_packaged_X (i : Fin keptCoords.length)
    (hi : keptCoords.length + i.val < genListPackaged.length) :
    genListPackaged.get ⟨keptCoords.length + i.val, hi⟩
      = grossComplex.faceStabOf (keptCoords.get i) := by
  have hZlen : (keptCoords.map grossComplex.vertexStabOf).length = keptCoords.length :=
    List.length_map _
  have hge : (keptCoords.map grossComplex.vertexStabOf).length ≤ keptCoords.length + i.val := by
    rw [hZlen]; omega
  have hidx : keptCoords.length + i.val - (keptCoords.map grossComplex.vertexStabOf).length
      = i.val := by rw [hZlen]; omega
  change (keptCoords.map grossComplex.vertexStabOf
    ++ keptCoords.map grossComplex.faceStabOf).get ⟨keptCoords.length + i.val, hi⟩ = _
  rw [List.get_eq_getElem, List.getElem_append_right hge, List.getElem_map]
  simp only [hidx]
  rfl

/-! ## §5d  rowsLinearIndependent (block-split) and generators_independent -/

private lemma zidx_lt (i : Fin keptCoords.length) : i.val < genListPackaged.length := by
  have := genListPackaged_length; have := i.isLt; omega

private lemma xidx_lt (i : Fin keptCoords.length) :
    keptCoords.length + i.val < genListPackaged.length := by
  have := genListPackaged_length; have := i.isLt; omega

set_option maxRecDepth 4096 in
private lemma sum_split_Z {M : Type*} [AddCommMonoid M]
    (F : Fin genListPackaged.length → M)
    (hX : ∀ i : Fin keptCoords.length, F ⟨keptCoords.length + i.val, xidx_lt i⟩ = 0) :
    ∑ k, F k = ∑ i : Fin keptCoords.length, F ⟨i.val, zidx_lt i⟩ := by
  have hlen := genListPackaged_length
  rw [← Equiv.sum_comp (finCongr hlen.symm) F, Fin.sum_univ_add]
  have hXsum : (∑ i : Fin keptCoords.length,
      F (finCongr hlen.symm (Fin.natAdd keptCoords.length i))) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← hX i]; congr 1
  rw [hXsum, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1

set_option maxRecDepth 4096 in
private lemma sum_split_X {M : Type*} [AddCommMonoid M]
    (F : Fin genListPackaged.length → M)
    (hZ : ∀ i : Fin keptCoords.length, F ⟨i.val, zidx_lt i⟩ = 0) :
    ∑ k, F k = ∑ i : Fin keptCoords.length, F ⟨keptCoords.length + i.val, xidx_lt i⟩ := by
  have hlen := genListPackaged_length
  rw [← Equiv.sum_comp (finCongr hlen.symm) F, Fin.sum_univ_add]
  have hZsum : (∑ i : Fin keptCoords.length,
      F (finCongr hlen.symm (Fin.castAdd keptCoords.length i))) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← hZ i]; congr 1
  rw [hZsum, zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The trimmed 132-generator list has linearly independent check-matrix rows. -/
theorem rowsLinearIndependent_packaged :
    NQubitPauliGroupElement.rowsLinearIndependent genListPackaged := by
  rw [NQubitPauliGroupElement.rowsLinearIndependent, Fintype.linearIndependent_iff]
  intro g hsum
  set n := grossComplex.numQubits with hn
  have hZchain : grossComplex.cutMap (∑ i : Fin keptCoords.length,
      g ⟨i.val, zidx_lt i⟩ • grossComplex.singleVtx (keptCoords.get i)) = 0 := by
    funext e
    rw [map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hcol := congr_fun hsum (Fin.natAdd n (grossComplex.edgeEquiv e))
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcol
    rw [← hcol, sum_split_Z (fun k => g k *
      NQubitPauliGroupElement.checkMatrix genListPackaged k
        (Fin.natAdd n (grossComplex.edgeEquiv e)))]
    · refine Finset.sum_congr rfl fun i _ => ?_
      have hterm : NQubitPauliGroupElement.checkMatrix genListPackaged ⟨i.val, zidx_lt i⟩
          (Fin.natAdd n (grossComplex.edgeEquiv e))
          = grossComplex.cutMap (grossComplex.singleVtx (keptCoords.get i)) e := by
        unfold NQubitPauliGroupElement.checkMatrix
        rw [get_packaged_Z i, vertexStabOf_sympl_Z, Equiv.symm_apply_apply]
      rw [hterm]
    · intro i
      have hterm : NQubitPauliGroupElement.checkMatrix genListPackaged
          ⟨keptCoords.length + i.val, xidx_lt i⟩ (Fin.natAdd n (grossComplex.edgeEquiv e)) = 0 := by
        unfold NQubitPauliGroupElement.checkMatrix
        rw [get_packaged_X i, faceStabOf_sympl_Z_zero]
      rw [hterm, mul_zero]
  have hZ0 := combo_singleVtx_kernel_zero _ hZchain
  have hXchain : grossComplex.boundary2 (∑ i : Fin keptCoords.length,
      g ⟨keptCoords.length + i.val, xidx_lt i⟩ • grossComplex.singleFace (keptCoords.get i)) = 0 := by
    funext e
    rw [map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hcol := congr_fun hsum (Fin.castAdd n (grossComplex.edgeEquiv e))
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcol
    rw [← hcol, sum_split_X (fun k => g k *
      NQubitPauliGroupElement.checkMatrix genListPackaged k
        (Fin.castAdd n (grossComplex.edgeEquiv e)))]
    · refine Finset.sum_congr rfl fun i _ => ?_
      have hterm : NQubitPauliGroupElement.checkMatrix genListPackaged
          ⟨keptCoords.length + i.val, xidx_lt i⟩ (Fin.castAdd n (grossComplex.edgeEquiv e))
          = grossComplex.boundary2 (grossComplex.singleFace (keptCoords.get i)) e := by
        unfold NQubitPauliGroupElement.checkMatrix
        rw [get_packaged_X i, faceStabOf_sympl_X, Equiv.symm_apply_apply]
      rw [hterm]
    · intro i
      have hterm : NQubitPauliGroupElement.checkMatrix genListPackaged ⟨i.val, zidx_lt i⟩
          (Fin.castAdd n (grossComplex.edgeEquiv e)) = 0 := by
        unfold NQubitPauliGroupElement.checkMatrix
        rw [get_packaged_Z i, vertexStabOf_sympl_X_zero]
      rw [hterm, mul_zero]
  have hX0 := combo_singleFace_kernel_zero _ hXchain
  intro k
  by_cases hk : k.val < keptCoords.length
  · have hz := hZ0 ⟨k.val, hk⟩
    rwa [Fin.eta] at hz
  · push_neg at hk
    have hlen := genListPackaged_length
    have hkl := k.isLt
    have hsub : k.val - keptCoords.length < keptCoords.length := by omega
    have hx := hX0 ⟨k.val - keptCoords.length, hsub⟩
    have hidx : (⟨keptCoords.length + (k.val - keptCoords.length), by omega⟩ :
        Fin genListPackaged.length) = k := by
      apply Fin.ext; show keptCoords.length + (k.val - keptCoords.length) = k.val; omega
    rwa [hidx] at hx

/-- The trimmed generator list is an independent generating set. -/
theorem generators_independent_packaged :
    Quantum.StabilizerGroup.GeneratorsIndependent grossComplex.numQubits genListPackaged :=
  Quantum.StabilizerGroup.GeneratorsIndependent_of_rowsLinearIndependent
    grossComplex.numQubits genListPackaged rowsLinearIndependent_packaged

end Quantum.Stabilizer.Homological.BB
