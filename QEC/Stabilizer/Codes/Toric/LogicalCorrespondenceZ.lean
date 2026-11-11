import QEC.Stabilizer.Framework.Homological.LogicalCorrespondence
import QEC.Stabilizer.Codes.Toric.CodeN
import QEC.Stabilizer.Codes.Toric.DualWrappingInvariants

/-!
# Z-type logical operators of the toric code and dual homology

The Z-chain operator `toricZOperatorOfChain L c` of a 1-chain `c` is logical
exactly when `c` is a dual cycle, and it is a stabilizer exactly when `c` is a
dual boundary:

* `toricZOperatorOfChain_commutes_faceStab_iff`: it commutes with the face
  check at `(x, y)` iff `toricDualBoundary L c (x, y) = 0`;
* `toricZOperatorOfChain_commutes_XGenerators_iff_mem_toricDualCycles` and
  `toricZOperatorOfChain_mem_centralizer_iff_mem_toricDualCycles`: it commutes
  with all face checks, equivalently with the whole stabilizer group, iff
  `c ∈ Z¹ L`;
* `toricZOperatorOfChain_mem_ZClosure_iff_mem_toricDualBoundaries`: it is a
  product of vertex checks iff `c ∈ B¹ L`;
* `toricZOperatorOfChain_isNontrivialLogical_iff`: it is a nontrivial logical
  operator iff `c` is a dual cycle that is not a dual boundary.

Every Z-type Pauli group element is the Z-chain operator of its Z-support
chain (`toricZOperatorOfChain_zChainOf`), so these statements describe all
Z-type logical operators.

All of them are the corresponding statements about the chain operators of
`toricHomologicalCode L`, whose checks and stabilizer group are those of the
toric code and whose dual complex is the dual toric complex.
-/

namespace Quantum
namespace Stabilizer
namespace Lattice

open scoped ToricChain
open Homological
open StabilizerGroup.ToricCodeN

variable (L : ℕ) [Fact (2 ≤ L)] (c : C1 L)

/-- The Z-chain operator of `c` commutes with the face check at `(x, y)` iff
the dual boundary of `c` vanishes at that face. -/
theorem toricZOperatorOfChain_commutes_faceStab_iff (x y : Fin L) :
    faceStab L x y * toricZOperatorOfChain L c =
        toricZOperatorOfChain L c * faceStab L x y ↔
      toricDualBoundary L c (x, y) = 0 := by
  rw [faceStab_eq_faceStabOf, eq_comm, ← toricHomologicalCode_dualBoundary_eq]
  exact HomologicalCode.chainZOperator_commutes_faceStabOf_iff (X := toricHomologicalCode L) c _

/-- The Z-chain operator of `c` commutes with every face check iff `c` is a
dual cycle. -/
theorem toricZOperatorOfChain_commutes_XGenerators_iff_mem_toricDualCycles :
    (∀ x ∈ XGenerators L, x * toricZOperatorOfChain L c = toricZOperatorOfChain L c * x) ↔
      c ∈ Z¹ L := by
  rw [XGenerators_eq_homologicalXGenerators, ← toricHomologicalCode_dualCycles_eq]
  exact HomologicalCode.chainZOperator_commutes_XGenerators_iff_mem_dualCycles
    (X := toricHomologicalCode L) c

/-- The Z-chain operator of `c` is a product of vertex checks iff `c` is a dual
boundary. -/
theorem toricZOperatorOfChain_mem_ZClosure_iff_mem_toricDualBoundaries :
    toricZOperatorOfChain L c ∈ Subgroup.closure (ZGenerators L) ↔ c ∈ B¹ L := by
  rw [ZGenerators_eq_homologicalZGenerators, ← toricHomologicalCode_dualBoundaries_eq]
  exact HomologicalCode.chainZOperator_mem_ZClosure_iff_mem_dualBoundaries
    (X := toricHomologicalCode L) c

/-- The Z-chain operator of `c` commutes with the stabilizer group iff `c` is a
dual cycle. -/
theorem toricZOperatorOfChain_mem_centralizer_iff_mem_toricDualCycles :
    toricZOperatorOfChain L c ∈ StabilizerGroup.centralizer (stabilizerGroup L) ↔
      c ∈ Z¹ L := by
  rw [← toricHomologicalCode_dualCycles_eq]
  exact HomologicalCode.chainZOperator_mem_centralizer_iff_of_toSubgroup_eq
    (X := toricHomologicalCode L) (stabilizerGroup_toSubgroup_eq_homologicalStabilizerGroup L) c

/-- The Z-chain operator of `c` is a nontrivial logical operator iff `c` is a
dual cycle that is not a dual boundary. -/
theorem toricZOperatorOfChain_isNontrivialLogical_iff :
    StabilizerGroup.IsNontrivialLogicalOperator (toricZOperatorOfChain L c)
        (stabilizerGroup L) ↔
      c ∈ Z¹ L ∧ c ∉ B¹ L := by
  rw [StabilizerGroup.IsNontrivialLogicalOperator_of_toSubgroup_eq _
    (stabilizerGroup_toSubgroup_eq_homologicalStabilizerGroup L),
    ← toricHomologicalCode_dualCycles_eq, ← toricHomologicalCode_dualBoundaries_eq]
  exact HomologicalCode.chainZOperator_isNontrivialLogical_iff (X := toricHomologicalCode L) c

end Lattice
end Stabilizer
end Quantum
