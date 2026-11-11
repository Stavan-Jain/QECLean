import QEC.Stabilizer.Codes.Toric.LogicalCorrespondenceZ
import QEC.Stabilizer.Codes.Toric.DistanceX

/-!
# The Z-distance of the toric code is `L`

The mirror image of `QEC.Stabilizer.Codes.Toric.DistanceX` for the dual
complex. The chain-level statements are transported from the X side by the
lattice duality `toricDuality L`, which preserves weights:

* `le_edgeWeight_of_not_mem_toricDualBoundaries`: a dual cycle that is not a
  dual boundary has weight at least `L`;
* `dualLoopChain_mem_toricDualBoundaries_iff`,
  `edgeWeight_dualLoopChain_one_zero`, `edgeWeight_dualLoopChain_zero_one`: the
  dual loops `dualLoopChain L 1 0` and `dualLoopChain L 0 1` are not dual
  boundaries and have weight `L`.

On operators:

* `horizontalHRowZOperator L` and `verticalVRowZOperator L` are the Z-chain
  operators of the two dual loops: Z-type nontrivial logical operators of
  weight `L`.
* `HasToricZDistance L d` says that `d` is the least weight of a Z-type
  nontrivial logical operator of the toric code, and `toricCodeN_dZ_eq_L` that
  this distance is `L`.
-/

namespace Quantum
namespace Stabilizer
namespace Lattice

open scoped ToricChain
open Homological

variable (L : ℕ) [Fact (0 < L)]

/-! ## Nontrivial dual cycles have weight at least `L` -/

variable {L} in
/-- A dual cycle that is not a dual boundary has weight at least `L`: it is
the image under duality of a cycle that is not a boundary. -/
theorem le_edgeWeight_of_not_mem_toricDualBoundaries {c : C1 L} (hc : c ∈ Z¹ L)
    (hb : c ∉ B¹ L) : L ≤ edgeWeight c := by
  obtain ⟨c, rfl⟩ := (toricDuality L).surjective c
  rw [edgeWeight_toricDuality]
  exact le_edgeWeight_of_not_mem_toricBoundaries (toricDuality_mem_toricDualCycles_iff.1 hc)
    (mt toricDuality_mem_toricDualBoundaries_iff.2 hb)

/-! ## The dual loops -/

/-- `dualLoopChain L a b` is a dual boundary only for `a = b = 0`. -/
lemma dualLoopChain_mem_toricDualBoundaries_iff (a b : ZMod 2) :
    dualLoopChain L a b ∈ B¹ L ↔ a = 0 ∧ b = 0 := by
  rw [← toricDuality_loopChain, toricDuality_mem_toricDualBoundaries_iff,
    loopChain_mem_toricBoundaries_iff, and_comm]

/-- The dual loop `dualLoopChain L 1 0` consists of the `L` horizontal edges of
one column. -/
lemma edgeWeight_dualLoopChain_one_zero : edgeWeight (dualLoopChain L 1 0) = L := by
  rw [← toricDuality_loopChain, edgeWeight_toricDuality, edgeWeight_loopChain_zero_one]

/-- The dual loop `dualLoopChain L 0 1` consists of the `L` vertical edges of
one row. -/
lemma edgeWeight_dualLoopChain_zero_one : edgeWeight (dualLoopChain L 0 1) = L := by
  rw [← toricDuality_loopChain, edgeWeight_toricDuality, edgeWeight_loopChain_one_zero]

/-- The Z-chain operator of `c` has the weight of `c`. -/
lemma weight_toricZOperatorOfChain (c : C1 L) :
    NQubitPauliGroupElement.weight (toricZOperatorOfChain L c) = edgeWeight c :=
  HomologicalCode.weight_chainZOperator (X := toricHomologicalCode L) c

end Lattice
end Stabilizer

namespace StabilizerGroup
namespace ToricCodeN

open NQubitPauliGroupElement Stabilizer.Lattice
open scoped ToricChain

/-! ## The Z-distance -/

/-- `HasToricZDistance L d`: every Z-type nontrivial logical operator of the
`L × L` toric code has weight at least `d`, and weight `d` is attained. -/
def HasToricZDistance (L d : ℕ) [Fact (2 ≤ L)] : Prop :=
  d ≥ 1 ∧
  (∀ g : NQubitPauliGroupElement (numQubits L),
      NQubitPauliGroupElement.IsZTypeElement g →
      IsNontrivialLogicalOperator g (stabilizerGroup L) →
      0 < weight g →
      weight g ≥ d) ∧
  (∃ g : NQubitPauliGroupElement (numQubits L),
      NQubitPauliGroupElement.IsZTypeElement g ∧
      IsNontrivialLogicalOperator g (stabilizerGroup L) ∧
      weight g = d)

/-- The Z-operator of the dual loop `dualLoopChain L 1 0`: `Z` on the
horizontal edges of the column `zeroCoord L`. -/
def horizontalHRowZOperator (L : ℕ) [Fact (0 < L)] : NQubitPauliGroupElement (numQubits L) :=
  toricZOperatorOfChain L (dualLoopChain L 1 0)

/-- The Z-operator of the dual loop `dualLoopChain L 0 1`: `Z` on the vertical
edges of the row `zeroCoord L`. -/
def verticalVRowZOperator (L : ℕ) [Fact (0 < L)] : NQubitPauliGroupElement (numQubits L) :=
  toricZOperatorOfChain L (dualLoopChain L 0 1)

lemma horizontalHRowZOperator_isZType (L : ℕ) [Fact (0 < L)] :
    IsZTypeElement (horizontalHRowZOperator L) :=
  toricZOperatorOfChain_isZType L _

lemma verticalVRowZOperator_isZType (L : ℕ) [Fact (0 < L)] :
    IsZTypeElement (verticalVRowZOperator L) :=
  toricZOperatorOfChain_isZType L _

variable (L : ℕ) [Fact (2 ≤ L)]

/-- `horizontalHRowZOperator L` is a nontrivial logical operator. -/
theorem horizontalHRowZOperator_isNontrivialLogical :
    IsNontrivialLogicalOperator (horizontalHRowZOperator L) (stabilizerGroup L) :=
  (toricZOperatorOfChain_isNontrivialLogical_iff L _).2 ⟨dualLoopChain_mem_toricDualCycles L 1 0,
    fun h => one_ne_zero ((dualLoopChain_mem_toricDualBoundaries_iff L 1 0).1 h).1⟩

/-- `verticalVRowZOperator L` is a nontrivial logical operator. -/
theorem verticalVRowZOperator_isNontrivialLogical :
    IsNontrivialLogicalOperator (verticalVRowZOperator L) (stabilizerGroup L) :=
  (toricZOperatorOfChain_isNontrivialLogical_iff L _).2 ⟨dualLoopChain_mem_toricDualCycles L 0 1,
    fun h => one_ne_zero ((dualLoopChain_mem_toricDualBoundaries_iff L 0 1).1 h).2⟩

/-- `horizontalHRowZOperator L` has weight `L`. -/
lemma weight_horizontalHRowZOperator : weight (horizontalHRowZOperator L) = L :=
  (weight_toricZOperatorOfChain L _).trans (edgeWeight_dualLoopChain_one_zero L)

/-- `verticalVRowZOperator L` has weight `L`. -/
lemma weight_verticalVRowZOperator : weight (verticalVRowZOperator L) = L :=
  (weight_toricZOperatorOfChain L _).trans (edgeWeight_dualLoopChain_zero_one L)

/-- There is a Z-type nontrivial logical operator of weight `L`:
`verticalVRowZOperator L`. -/
theorem exists_nontrivial_z_logical_weight_eq_L :
    ∃ g : NQubitPauliGroupElement (numQubits L),
      NQubitPauliGroupElement.IsZTypeElement g ∧
      IsNontrivialLogicalOperator g (stabilizerGroup L) ∧
      weight g = L :=
  ⟨verticalVRowZOperator L, verticalVRowZOperator_isZType L,
    verticalVRowZOperator_isNontrivialLogical L, weight_verticalVRowZOperator L⟩

/-- Every Z-type nontrivial logical operator has weight at least `L`: it is
the Z-chain operator of a dual cycle that is not a dual boundary. -/
theorem nontrivial_z_logical_weight_ge_L (g : NQubitPauliGroupElement (numQubits L))
    (hgZ : NQubitPauliGroupElement.IsZTypeElement g)
    (hgLogical : IsNontrivialLogicalOperator g (stabilizerGroup L)) :
    weight g ≥ L := by
  obtain ⟨c, rfl⟩ : ∃ c, toricZOperatorOfChain L c = g := ⟨_, toricZOperatorOfChain_zChainOf L hgZ⟩
  obtain ⟨hc, hb⟩ := (toricZOperatorOfChain_isNontrivialLogical_iff L c).1 hgLogical
  rw [weight_toricZOperatorOfChain]
  exact le_edgeWeight_of_not_mem_toricDualBoundaries hc hb

/-- The Z-distance of the toric code is `L`. -/
theorem toricCodeN_dZ_eq_L : HasToricZDistance L L :=
  ⟨le_trans one_le_two Fact.out, fun g hgZ hgLogical _ =>
    nontrivial_z_logical_weight_ge_L L g hgZ hgLogical, exists_nontrivial_z_logical_weight_eq_L L⟩

end ToricCodeN
end StabilizerGroup
end Quantum
