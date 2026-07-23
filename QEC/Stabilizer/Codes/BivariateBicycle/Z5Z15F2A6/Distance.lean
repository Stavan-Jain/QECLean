/-
# `d([[300,8,16]]) = 16` at the chain and Pauli levels — the two-tier claim

The assembly of the first `d ≥ 7` doubling instance through the parametric
layer (`BBDoubling.lean`, logical-floor variant).  The three floor inputs
of a `[[150,8,8]]` base are far beyond direct kernel enumeration
(`2⁷⁵`-scale coset sweeps); each was first a solver certificate and each
is **now a kernel-checked theorem**, so
`cover300_chain_distance_eq_16` / `cover300_pauli_distance_eq_16` are
**unconditional** — the program's first solver-free `d > 12` distance
statement.  Floor status:

* `coverData.LogicalFloor 8` — `d(base) ≥ 8`.  **Theorem** `logicalFloor_8`
  (`BaseFloor.lean`, A21 — parity, the y-span lemma, mirror symmetry,
  D2-pigeonholes, and the (3,3) transversality localization, with the
  weight-6 classification closed by translation-reduced coset sweeps).
  Replaces the CaDiCaL `UNSAT@7` certificate; the witness half
  (`d(base) ≤ 8`) is kernel-checked in `Witness.lean`.  `StrongBaseFloor
  8` is *false* here (weight-6 generator columns), hence the logical-floor
  assembly.
* `coverData.DangerousFloorNZ 16` — the (M)-half.  **Theorem**
  `cover300_dangerousFloorNZ`, from `logicalFloor_8` and
  `lightClassification` via `dangerousFloorNZ_of_lightClassification`
  (`Dangerous.lean`).  The light-boundary classification
  (`lightClassification`, `LightAssembly.lean`, A22) replaces the 9.6 h
  SAT enumeration-completeness verdict by a CRT-fibering kernel proof.
* `coverData.SeamCosetFloor 16` — the safe-floor input.  **Theorem**
  `seamCosetFloor_16` (`SeamReduction.lean`, A23): the reduction to the
  single inequality `∀ f, |A⋆f + e₀| + |B⋆f| ≥ 16`, discharged through
  the A22 fibering.  Replaces the CryptoMiniSat XOR-native `UNSAT@14`
  certificate (+ parity + orbit transport; kissat DRAT).

The `_cond` theorems keep the parametric template statement over the
three floor inputs.  The homotopy (R) (`DeckHomotopy.lean`) and the tight
witness (`Witness.lean`) are unconditional kernel facts; the membership
half of both `IsLeast` statements is unconditional
(`cover300_exists_weight16_nontrivial_cycle`).
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.DeckHomotopy
import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.Witness
import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.Dangerous
import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.BaseFloor
import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.LightAssembly
import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.SeamReduction

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z5Z15F2A6

/-- The safe floor at `16`, from the kernel-checked homotopy (R) and the
S4-certified Smith-coset floor. -/
theorem cover300_safeFloor (hMim : coverData.SeamCosetFloor 16) :
    coverData.SafeFloor 16 :=
  coverData.safeFloor_of_seamCosetFloor homotopyR hMim

/-- **Chain-level `d(cover) = 2·d(base) = 16`**, the parametric template
statement over the three floor inputs (see `cover300_chain_distance_eq_16`
for the unconditional form now that all three are theorems). -/
theorem cover300_chain_distance_eq_16_cond
    (hbase : coverData.LogicalFloor 8)
    (hM : coverData.DangerousFloorNZ 16)
    (hMim : coverData.SeamCosetFloor 16) :
    IsLeast {w : ℕ | ∃ v : G300 × Fin 2 → ZMod 2,
      v ∈ coverData.coverComplex.cycles ∧
      v ∉ coverData.coverComplex.boundaries ∧
      coverData.coverComplex.chainWeight v = w} 16 := by
  have h := coverData.chain_distance_eq_double_of_logicalFloor (d := 8)
    hbase hM (cover300_safeFloor hMim)
    uStar150 uStar150_mem_cycles chainWeight_uStar150
    tauUStar150_not_mem_boundaries
  norm_num at h
  exact h

/-- **Pauli-level `d(cover) = 16`**, the parametric template statement
over the three floor inputs (see `cover300_pauli_distance_eq_16` for the
unconditional form now that all three are theorems). -/
theorem cover300_pauli_distance_eq_16_cond
    (hbase : coverData.LogicalFloor 8)
    (hM : coverData.DangerousFloorNZ 16)
    (hMim : coverData.SeamCosetFloor 16) :
    IsLeast {w : ℕ | ∃ g : NQubitPauliGroupElement coverData.coverComplex.numQubits,
      Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
        coverData.coverComplex.homologicalStabilizerGroup ∧
      NQubitPauliGroupElement.weight g = w} 16 := by
  have h := coverData.pauli_distance_eq_double_of_logicalFloor (d := 8)
    hbase hM (cover300_safeFloor hMim)
    uStar150 uStar150_mem_cycles chainWeight_uStar150
    tauUStar150_not_mem_boundaries
  norm_num at h
  exact h

/-- The dangerous floor at `16`, now a theorem: discharged from the
proven base floor (`logicalFloor_8`) and the proven light-boundary
classification (`lightClassification`). -/
theorem cover300_dangerousFloorNZ : coverData.DangerousFloorNZ 16 :=
  dangerousFloorNZ_of_lightClassification logicalFloor_8 lightClassification

/-- **Chain-level `d(cover) = 2·d(base) = 16`, unconditionally.**  All
three floor inputs are now kernel-checked theorems — `logicalFloor_8`
(A21), `lightClassification` (A22, via `cover300_dangerousFloorNZ`), and
`seamCosetFloor_16` (A23) — so the `IsLeast` distance statement carries
no hypotheses. -/
theorem cover300_chain_distance_eq_16 :
    IsLeast {w : ℕ | ∃ v : G300 × Fin 2 → ZMod 2,
      v ∈ coverData.coverComplex.cycles ∧
      v ∉ coverData.coverComplex.boundaries ∧
      coverData.coverComplex.chainWeight v = w} 16 :=
  cover300_chain_distance_eq_16_cond logicalFloor_8
    cover300_dangerousFloorNZ seamCosetFloor_16

/-- **Pauli-level `d(cover) = 16`, unconditionally**: 16 is the least
weight of a nontrivial logical operator of the `[[300,8,16]]`
homological stabilizer group — the program's first solver-free `d > 12`
distance theorem, kernel-checked to the standard axioms plus named
`native_decide` obligations. -/
theorem cover300_pauli_distance_eq_16 :
    IsLeast {w : ℕ | ∃ g : NQubitPauliGroupElement coverData.coverComplex.numQubits,
      Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
        coverData.coverComplex.homologicalStabilizerGroup ∧
      NQubitPauliGroupElement.weight g = w} 16 :=
  cover300_pauli_distance_eq_16_cond logicalFloor_8
    cover300_dangerousFloorNZ seamCosetFloor_16

end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum
