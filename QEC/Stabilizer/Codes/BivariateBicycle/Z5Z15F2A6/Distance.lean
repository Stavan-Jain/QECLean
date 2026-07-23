/-
# `d([[300,8,16]]) = 16` at the chain and Pauli levels — the two-tier claim

The assembly of the first `d ≥ 7` doubling instance through the parametric
layer (`BBDoubling.lean`, logical-floor variant).  Unlike the gross and
pair72 instances, the three floor inputs of a `[[150,8,8]]` base are far
beyond kernel enumeration (`2⁷⁵`-scale coset sweeps), so this instance is
packaged as the **Paper-1 two-tier claim**: the doubling theorem is
kernel-checked; the floors enter as named hypotheses whose provenance is
solver certificates.  Hypothesis status:

* `hbase : coverData.LogicalFloor 8` — `d(base) ≥ 8`.  **Discharged**:
  `logicalFloor_8` (`BaseFloor.lean`, the A21 analytic proof — parity,
  the y-span lemma, mirror symmetry, D2-pigeonholes, and the (3,3)
  transversality localization, with the weight-6 classification closed
  by translation-reduced coset sweeps).  The CaDiCaL `UNSAT@7`
  certificate is fully replaced; the witness half (`d(base) ≤ 8`)
  remains kernel-checked in `Witness.lean`.  Note `StrongBaseFloor 8`
  is *false* here (weight-6 generator columns), which is why the
  logical-floor assembly exists.
* `hM : coverData.DangerousFloorNZ 16` — the (M)-half of the template.
  **Discharged**: `dangerousFloorNZ_of_lightClassification`
  (`Dangerous.lean`) proves it from `hbase` + the light-boundary
  classification, so the `_of_classification` variants below replace
  this input by `hcls : LightClassification` — the exhaustive
  SAT-enumeration completeness statement (9.6 h UNSAT with
  translation-orbit blocking; Φ-closure cross-check; DRAT upgrade
  path = kissat on the blocked n = 75 CNF).  The plain three-hypothesis
  theorems are kept for reference.
* `hMim : coverData.SeamCosetFloor 16` — the S4 certificate of the A17
  docket decision pass (`data/a17/docket_decision.jsonl`): CryptoMiniSat
  XOR-native `UNSAT@14` on the seam-coset G-orbit rep (975.8 s) + the
  weight-parity lemma (odd weights vacuous) + orbit transport; kissat
  re-proof on the Tseitin CNF with a 6.85 GB DRAT certificate
  (`data/a17/kissat_f2a6f17e_y_w14.drat.gz`).

Given those, `cover300_chain_distance_eq_16` / `cover300_pauli_distance_eq_16`
deliver `d(cover) = 16 = 2·d(base)` — the first `d > 12` distance statement
in the program.  The homotopy (R) (`DeckHomotopy.lean`) and the tight
witness (`Witness.lean`) are unconditional kernel facts; in particular the
membership half of both `IsLeast` statements is unconditional
(`cover300_exists_weight16_nontrivial_cycle`).
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.DeckHomotopy
import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.Witness
import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.Dangerous
import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.BaseFloor

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

/-- **Chain-level `d(cover) = 2·d(base) = 16`**, conditional on the three
certificate-checked floors (see the module docstring for provenance). -/
theorem cover300_chain_distance_eq_16
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

/-- **Pauli-level `d(cover) = 16`**, conditional on the three
certificate-checked floors: 16 is the least weight of a nontrivial
logical operator of the `[[300,8,16]]` homological stabilizer group. -/
theorem cover300_pauli_distance_eq_16
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

/-- The dangerous floor, discharged from the light-boundary
classification (`Dangerous.lean`) and the proven base floor
(`BaseFloor.lean`). -/
theorem cover300_dangerousFloorNZ (hcls : LightClassification) :
    coverData.DangerousFloorNZ 16 :=
  dangerousFloorNZ_of_lightClassification logicalFloor_8 hcls

/-- **Chain-level `d(cover) = 16`** with the base floor proven and the
(M)-half discharged: the hypothesis set is the light-boundary
classification and the Smith-coset floor. -/
theorem cover300_chain_distance_eq_16_of_classification
    (hcls : LightClassification) (hMim : coverData.SeamCosetFloor 16) :
    IsLeast {w : ℕ | ∃ v : G300 × Fin 2 → ZMod 2,
      v ∈ coverData.coverComplex.cycles ∧
      v ∉ coverData.coverComplex.boundaries ∧
      coverData.coverComplex.chainWeight v = w} 16 :=
  cover300_chain_distance_eq_16 logicalFloor_8
    (cover300_dangerousFloorNZ hcls) hMim

/-- **Pauli-level `d(cover) = 16`** with the base floor proven and the
(M)-half discharged. -/
theorem cover300_pauli_distance_eq_16_of_classification
    (hcls : LightClassification) (hMim : coverData.SeamCosetFloor 16) :
    IsLeast {w : ℕ | ∃ g : NQubitPauliGroupElement coverData.coverComplex.numQubits,
      Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
        coverData.coverComplex.homologicalStabilizerGroup ∧
      NQubitPauliGroupElement.weight g = w} 16 :=
  cover300_pauli_distance_eq_16 logicalFloor_8
    (cover300_dangerousFloorNZ hcls) hMim

end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum
