/-
# Gross compatibility interface for generic doubling

The three named inputs are specializations of `XDoubleCoverData.LogicalFloor`,
`DangerousFloorNZ`, and `SafeFloor`. The zero-pushforward rung, sector split,
duality, and chain/Pauli assemblies all use the generic logical-floor theorems
from `BBDoubling.lean`. Existing Gross theorem names remain available to the
certificate files and downstream users.

The weight-six base witness and its nontrivial weight-twelve pullback are the
Gross-specific upper bound. `BaseDistance`, `DangerousSector`, and `SafeSector`
supply the lower-bound inputs, using the same generic machinery.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Gross.Witness

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

/-! ## The three residual hypotheses (the Phase 2–4 targets) -/

/-- **(A)** Chain-level `d(base) ≥ 6`: every nontrivial cycle of the bb72
complex has weight ≥ 6. Paper source: the small-cycle theorem, A4 Theorem A /
Corollary A′ (Entry 13). Phase-2 target. -/
def BaseDistanceGe6 : Prop :=
  grossCoverData.LogicalFloor 6

/-- **(M), `b ≠ 0` rungs**: every nontrivial gross cycle in the dangerous sector
(pushforward a base boundary) with *nonzero* pushforward has weight ≥ 12. Paper
source: the light-stabilizer classification + m-rungs, A4 Theorem C (Entries
10–13). Phase-3 target. (The `b = 0` rung is discharged below from
`BaseDistanceGe6` alone.) -/
def DangerousSectorGe12 : Prop :=
  grossCoverData.DangerousFloorNZ 12

/-- **(M-im)**: every gross cycle in the safe sector (pushforward NOT a base
boundary) has weight ≥ 12. Paper source: (R) + the flux characterization + the
(M-im) confined-floor program, A4 Part II / Theorem D (Entries 16–28). Phase-4
target. (Such a `v` is automatically not a boundary, since `p` maps boundaries
to boundaries.) -/
def SafeSectorGe12 : Prop :=
  grossCoverData.SafeFloor 12

/-! ## The `b = 0` dangerous rung (discharged here)

If `p(v) = 0` then by exactness `v = τ(u)`; `u` is a cycle because `τ` is an
injective chain map, `u` is nontrivial because `τ` carries boundaries to
boundaries, and `|v| = 2|u| ≥ 2·6 = 12`. -/

/-- The zero-pushforward bound is the generic logical-floor rung. -/
theorem gross_chainWeight_ge_12_of_coverPush_eq_zero
    (hbase : BaseDistanceGe6)
    {v : GrossGroup × Fin 2 → ZMod 2}
    (hv : v ∈ grossComplex.cycles) (hnb : v ∉ grossComplex.boundaries)
    (h0 : coverPush1 v = 0) :
    12 ≤ grossComplex.chainWeight v :=
  grossCoverData.dangerous_zero_rung_of_logicalFloor hbase hv hnb h0

/-! ## The assembly -/

/-- **Sector-dichotomy assembly**: given the three analytic inputs, every
nontrivial cycle of the gross complex has chain weight ≥ 12. -/
theorem gross_chainWeight_ge_12_of_sectors
    (hbase : BaseDistanceGe6) (hM : DangerousSectorGe12)
    (hMim : SafeSectorGe12) :
    ∀ v : GrossGroup × Fin 2 → ZMod 2,
      v ∈ grossComplex.cycles → v ∉ grossComplex.boundaries →
      12 ≤ grossComplex.chainWeight v :=
  grossCoverData.chainWeight_ge_double_of_logicalFloor hbase hM hMim

/-- Conditional chain-level `d(gross) = 12`: the weight 12 is attained by a
nontrivial cycle (the Phase-0 witness `τ(u*)`, unconditional) and is minimal
(given the three sector inputs). -/
theorem gross_chain_distance_eq_12_of_sectors
    (hbase : BaseDistanceGe6) (hM : DangerousSectorGe12)
    (hMim : SafeSectorGe12) :
    IsLeast {w : ℕ | ∃ v : GrossGroup × Fin 2 → ZMod 2,
      v ∈ grossComplex.cycles ∧ v ∉ grossComplex.boundaries ∧
      grossComplex.chainWeight v = w} 12 :=
  grossCoverData.chain_distance_eq_double_of_logicalFloor hbase hM hMim
    uStar uStar_mem_cycles chainWeight_uStar tauUStar_not_mem_boundaries

/-! ## The dual (Z) side, by the Φ duality -/

/-- Dual-side mirror: the same three inputs bound every nontrivial *dual* cycle
(Z-side chain) at ≥ 12, via the chain-level `d_X = d_Z` duality. -/
theorem gross_dual_chainWeight_ge_12_of_sectors
    (hbase : BaseDistanceGe6) (hM : DangerousSectorGe12)
    (hMim : SafeSectorGe12) :
    ∀ c ∈ grossComplex.dualCycles, c ∉ grossComplex.dualBoundaries →
      12 ≤ grossComplex.chainWeight c :=
  grossCoverData.dual_chainWeight_ge_double_of_logicalFloor hbase hM hMim

/-! ## Pauli-level corollaries (the CSS distance bridge) -/

/-- Unconditional: an explicit weight-12 nontrivial logical Pauli operator of
the gross homological stabilizer group (the X-type encoding of the Phase-0
witness `τ(u*)`). -/
theorem gross_exists_weight12_logical :
    ∃ g : NQubitPauliGroupElement grossComplex.numQubits,
      Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
        grossComplex.homologicalStabilizerGroup ∧
      NQubitPauliGroupElement.weight g = 12 := by
  refine ⟨grossComplex.chainXOperator (coverPull1 uStar), ?_, ?_⟩
  · exact (HomologicalCode.chainXOperator_isNontrivialLogical_iff
      (X := grossComplex) (coverPull1 uStar)).mpr
      ⟨tauUStar_mem_cycles, tauUStar_not_mem_boundaries⟩
  · rw [HomologicalCode.weight_chainXOperator, chainWeight_tauUStar]

/-- Conditional Pauli-level lower bound: given the three sector inputs, every
nontrivial logical operator of the gross homological stabilizer group has weight
≥ 12. -/
theorem gross_logical_weight_ge_12_of_sectors
    (hbase : BaseDistanceGe6) (hM : DangerousSectorGe12)
    (hMim : SafeSectorGe12)
    (g : NQubitPauliGroupElement grossComplex.numQubits)
    (hg : Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
      grossComplex.homologicalStabilizerGroup) :
    12 ≤ NQubitPauliGroupElement.weight g :=
  grossCoverData.logical_weight_ge_double_of_logicalFloor hbase hM hMim g hg

/-- **Conditional Pauli-level `d(gross) = 12`**: given the three sector inputs,
12 is the least weight of a nontrivial logical operator of the gross homological
stabilizer group. -/
theorem gross_pauli_distance_eq_12_of_sectors
    (hbase : BaseDistanceGe6) (hM : DangerousSectorGe12)
    (hMim : SafeSectorGe12) :
    IsLeast {w : ℕ | ∃ g : NQubitPauliGroupElement grossComplex.numQubits,
      Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
        grossComplex.homologicalStabilizerGroup ∧
      NQubitPauliGroupElement.weight g = w} 12 :=
  grossCoverData.pauli_distance_eq_double_of_logicalFloor hbase hM hMim
    uStar uStar_mem_cycles chainWeight_uStar tauUStar_not_mem_boundaries

end BB
end Homological
end Stabilizer
end Quantum
