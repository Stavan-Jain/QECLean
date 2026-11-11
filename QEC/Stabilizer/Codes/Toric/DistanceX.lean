import QEC.Stabilizer.Codes.Toric.LogicalCorrespondenceX
import QEC.Stabilizer.Codes.Toric.WrappingInvariants

/-!
# The X-distance of the toric code is `L`

* `horizontalLoopXOperator L` and `verticalLoopXOperator L` are the X-chain
  operators of the horizontal loop `loopChain L 1 0` and the vertical loop
  `loopChain L 0 1`: X-type nontrivial logical operators of weight `L`.
* `HasToricXDistance L d` says that `d` is the least weight of an X-type
  nontrivial logical operator of the toric code, and `toricCodeN_dX_eq_L` that
  this distance is `L`. The lower bound is the statement on chains
  `le_edgeWeight_of_not_mem_toricBoundaries`: a cycle that is not a boundary
  has weight at least `L`.
-/

namespace Quantum
namespace StabilizerGroup
namespace ToricCodeN

open NQubitPauliGroupElement Stabilizer.Lattice
open scoped ToricChain

/-! ## The X-distance -/

/-- `HasToricXDistance L d`: every X-type nontrivial logical operator of the
`L × L` toric code has weight at least `d`, and weight `d` is attained. -/
def HasToricXDistance (L d : ℕ) [Fact (2 ≤ L)] : Prop :=
  d ≥ 1 ∧
  (∀ g : NQubitPauliGroupElement (numQubits L),
      NQubitPauliGroupElement.IsXTypeElement g →
      IsNontrivialLogicalOperator g (stabilizerGroup L) →
      0 < weight g →
      weight g ≥ d) ∧
  (∃ g : NQubitPauliGroupElement (numQubits L),
      NQubitPauliGroupElement.IsXTypeElement g ∧
      IsNontrivialLogicalOperator g (stabilizerGroup L) ∧
      weight g = d)

/-- The horizontal X-loop: `X` on the horizontal edges of the row
`zeroCoord L`. -/
def horizontalLoopXOperator (L : ℕ) [Fact (0 < L)] : NQubitPauliGroupElement (numQubits L) :=
  toricXOperatorOfChain L (loopChain L 1 0)

/-- The vertical X-loop: `X` on the vertical edges of the column
`zeroCoord L`. -/
def verticalLoopXOperator (L : ℕ) [Fact (0 < L)] : NQubitPauliGroupElement (numQubits L) :=
  toricXOperatorOfChain L (loopChain L 0 1)

lemma horizontalLoopXOperator_isXType (L : ℕ) [Fact (0 < L)] :
    IsXTypeElement (horizontalLoopXOperator L) :=
  toricXOperatorOfChain_isXType L _

lemma verticalLoopXOperator_isXType (L : ℕ) [Fact (0 < L)] :
    IsXTypeElement (verticalLoopXOperator L) :=
  toricXOperatorOfChain_isXType L _

variable (L : ℕ) [Fact (2 ≤ L)]

/-- The horizontal X-loop is a nontrivial logical operator. -/
theorem horizontalLoopXOperator_isNontrivialLogical :
    IsNontrivialLogicalOperator (horizontalLoopXOperator L) (stabilizerGroup L) :=
  (toricXOperatorOfChain_isNontrivialLogical_iff L _).2 ⟨loopChain_mem_toricCycles L 1 0,
    fun h => one_ne_zero ((loopChain_mem_toricBoundaries_iff L 1 0).1 h).1⟩

/-- The vertical X-loop is a nontrivial logical operator. -/
theorem verticalLoopXOperator_isNontrivialLogical :
    IsNontrivialLogicalOperator (verticalLoopXOperator L) (stabilizerGroup L) :=
  (toricXOperatorOfChain_isNontrivialLogical_iff L _).2 ⟨loopChain_mem_toricCycles L 0 1,
    fun h => one_ne_zero ((loopChain_mem_toricBoundaries_iff L 0 1).1 h).2⟩

/-- The horizontal X-loop has weight `L`. -/
lemma weight_horizontalLoopXOperator : weight (horizontalLoopXOperator L) = L :=
  (weight_toricXOperatorOfChain L _).trans (edgeWeight_loopChain_one_zero L)

/-- The vertical X-loop has weight `L`. -/
lemma weight_verticalLoopXOperator : weight (verticalLoopXOperator L) = L :=
  (weight_toricXOperatorOfChain L _).trans (edgeWeight_loopChain_zero_one L)

/-- There is an X-type nontrivial logical operator of weight `L`: the
horizontal X-loop. -/
theorem exists_nontrivial_x_logical_weight_eq_L :
    ∃ g : NQubitPauliGroupElement (numQubits L),
      NQubitPauliGroupElement.IsXTypeElement g ∧
      IsNontrivialLogicalOperator g (stabilizerGroup L) ∧
      weight g = L :=
  ⟨horizontalLoopXOperator L, horizontalLoopXOperator_isXType L,
    horizontalLoopXOperator_isNontrivialLogical L, weight_horizontalLoopXOperator L⟩

/-- Every X-type nontrivial logical operator has weight at least `L`: it is
the X-chain operator of a cycle that is not a boundary. -/
theorem nontrivial_x_logical_weight_ge_L (g : NQubitPauliGroupElement (numQubits L))
    (hgX : NQubitPauliGroupElement.IsXTypeElement g)
    (hgLogical : IsNontrivialLogicalOperator g (stabilizerGroup L)) :
    weight g ≥ L := by
  obtain ⟨c, rfl⟩ : ∃ c, toricXOperatorOfChain L c = g := ⟨_, toricXOperatorOfChain_xChainOf L hgX⟩
  obtain ⟨hc, hb⟩ := (toricXOperatorOfChain_isNontrivialLogical_iff L c).1 hgLogical
  rw [weight_toricXOperatorOfChain]
  exact le_edgeWeight_of_not_mem_toricBoundaries hc hb

/-- The X-distance of the toric code is `L`. -/
theorem toricCodeN_dX_eq_L : HasToricXDistance L L :=
  ⟨le_trans one_le_two Fact.out, fun g hgX hgLogical _ =>
    nontrivial_x_logical_weight_ge_L L g hgX hgLogical, exists_nontrivial_x_logical_weight_eq_L L⟩

end ToricCodeN
end StabilizerGroup
end Quantum
