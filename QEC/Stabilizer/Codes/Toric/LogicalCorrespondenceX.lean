import QEC.Stabilizer.Framework.Homological.LogicalCorrespondence
import QEC.Stabilizer.Codes.Toric.CodeN

/-!
# X-type logical operators of the toric code and homology

The X-chain operator `toricXOperatorOfChain L c` of a 1-chain `c` is logical
exactly when `c` is a cycle, and it is a stabilizer exactly when `c` is a
boundary:

* `toricXOperatorOfChain_commutes_vertexStab_iff`: it commutes with the vertex
  check at `(x, y)` iff `∂₁ L c (x, y) = 0`;
* `toricXOperatorOfChain_commutes_ZGenerators_iff_mem_toricCycles` and
  `toricXOperatorOfChain_mem_centralizer_iff_mem_toricCycles`: it commutes with
  all vertex checks, equivalently with the whole stabilizer group, iff
  `c ∈ Z₁ L`;
* `toricXOperatorOfChain_mem_XClosure_iff_mem_toricBoundaries`: it is a product
  of face checks iff `c ∈ B₁ L`;
* `toricXOperatorOfChain_isNontrivialLogical_iff`: it is a nontrivial logical
  operator iff `c` is a cycle that is not a boundary.

Every X-type Pauli group element is the X-chain operator of its X-support
chain (`toricXOperatorOfChain_xChainOf`), so these statements describe all
X-type logical operators.

All of them are the corresponding statements about the chain operators of
`toricHomologicalCode L`, whose checks and stabilizer group are those of the
toric code.
-/

namespace Quantum
namespace Stabilizer
namespace Lattice

open scoped ToricChain
open Homological
open StabilizerGroup.ToricCodeN
open NQubitPauliGroupElement (IsXTypeElement)

/-- Every X-type Pauli group element is the X-chain operator of its X-support
chain. -/
lemma toricXOperatorOfChain_xChainOf (L : ℕ) [Fact (0 < L)]
    {g : NQubitPauliGroupElement (toricNumQubits L)} (hg : IsXTypeElement g) :
    toricXOperatorOfChain L ((toricHomologicalCode L).xChainOf g) = g :=
  NQubitPauliGroupElement.ext _ _ hg.1.symm <| funext fun i => by
    rw [← toricHomologicalCode_chainXOperator_eq, HomologicalCode.chainXOperator_xChainOf_op_at]
    rcases hg.2 i with h | h <;> simp [h]

variable (L : ℕ) [Fact (2 ≤ L)] (c : C1 L)

/-- The X-chain operator of `c` commutes with the vertex check at `(x, y)` iff
the boundary of `c` vanishes at that vertex. -/
theorem toricXOperatorOfChain_commutes_vertexStab_iff (x y : Fin L) :
    vertexStab L x y * toricXOperatorOfChain L c =
        toricXOperatorOfChain L c * vertexStab L x y ↔
      ∂₁ L c (x, y) = 0 := by
  rw [vertexStab_eq_vertexStabOf, eq_comm]
  exact HomologicalCode.chainXOperator_commutes_vertexStabOf_iff (X := toricHomologicalCode L) c _

/-- The X-chain operator of `c` commutes with every vertex check iff `c` is a
cycle. -/
theorem toricXOperatorOfChain_commutes_ZGenerators_iff_mem_toricCycles :
    (∀ z ∈ ZGenerators L, z * toricXOperatorOfChain L c = toricXOperatorOfChain L c * z) ↔
      c ∈ Z₁ L := by
  rw [ZGenerators_eq_homologicalZGenerators]
  exact HomologicalCode.chainXOperator_commutes_ZGenerators_iff_mem_cycles
    (X := toricHomologicalCode L) c

/-- The X-chain operator of `c` is a product of face checks iff `c` is a
boundary. -/
theorem toricXOperatorOfChain_mem_XClosure_iff_mem_toricBoundaries :
    toricXOperatorOfChain L c ∈ Subgroup.closure (XGenerators L) ↔ c ∈ B₁ L := by
  rw [XGenerators_eq_homologicalXGenerators]
  exact HomologicalCode.chainXOperator_mem_XClosure_iff_mem_boundaries
    (X := toricHomologicalCode L) c

/-- The X-chain operator of `c` commutes with the stabilizer group iff `c` is a
cycle. -/
theorem toricXOperatorOfChain_mem_centralizer_iff_mem_toricCycles :
    toricXOperatorOfChain L c ∈ StabilizerGroup.centralizer (stabilizerGroup L) ↔
      c ∈ Z₁ L := by
  rw [StabilizerGroup.centralizer_eq_of_toSubgroup_eq _ _
    (stabilizerGroup_toSubgroup_eq_homologicalStabilizerGroup L)]
  exact HomologicalCode.chainXOperator_mem_centralizer_iff_mem_cycles
    (X := toricHomologicalCode L) c

/-- The X-chain operator of `c` is a nontrivial logical operator iff `c` is a
cycle that is not a boundary. -/
theorem toricXOperatorOfChain_isNontrivialLogical_iff :
    StabilizerGroup.IsNontrivialLogicalOperator (toricXOperatorOfChain L c)
        (stabilizerGroup L) ↔
      c ∈ Z₁ L ∧ c ∉ B₁ L := by
  rw [StabilizerGroup.IsNontrivialLogicalOperator_of_toSubgroup_eq _
    (stabilizerGroup_toSubgroup_eq_homologicalStabilizerGroup L)]
  exact HomologicalCode.chainXOperator_isNontrivialLogical_iff (X := toricHomologicalCode L) c

end Lattice
end Stabilizer
end Quantum
