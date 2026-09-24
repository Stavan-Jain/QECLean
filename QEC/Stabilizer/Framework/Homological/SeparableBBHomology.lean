import QEC.Stabilizer.Framework.Homological.AutoPresentation
import QEC.Stabilizer.Framework.Homological.BBDuality

/-!
# Homological dimension of bivariate bicycle codes

The BB reflection and block swap identify boundaries with coboundaries.
Rank-nullity then expresses first homology as twice the common-check kernel.
-/

namespace Quantum.Stabilizer.Homological.BB

open HomologicalCode

variable {G : Type} [Fintype G] [AddCommGroup G] [DecidableEq G]
variable (A B : G → ZMod 2)

/-- BB duality identifies the boundary and coboundary spaces linearly. -/
noncomputable def boundaryDuality :
    (bbChainComplex A B).boundaries ≃ₗ[ZMod 2] (bbChainComplex A B).dualBoundaries where
  toFun c := ⟨bbDualFn c.val, (bbDual_mem_dualBoundaries_iff A B c.val).mpr c.property⟩
  invFun c := ⟨bbDualFn c.val, (bbDual_mem_dualBoundaries_iff A B (bbDualFn c.val)).mp
    (by rw [bbDualFn_bbDualFn]; exact c.property)⟩
  left_inv c := Subtype.ext (bbDualFn_bbDualFn c.val)
  right_inv c := Subtype.ext (bbDualFn_bbDualFn c.val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A BB complex has equal boundary and coboundary ranks. -/
theorem finrank_boundaries_eq_dualBoundaries :
    Module.finrank (ZMod 2) (bbChainComplex A B).boundaries =
      Module.finrank (ZMod 2) (bbChainComplex A B).dualBoundaries :=
  (boundaryDuality A B).finrank_eq

/-- The number of BB logical qubits is twice the common-check nullity. -/
theorem finrank_H1_eq_two_mul_boundary2_nullity :
    Module.finrank (ZMod 2) (bbChainComplex A B).H1 =
      2 * Module.finrank (ZMod 2) (LinearMap.ker (bbChainComplex A B).boundary2) := by
  have hr := (bbChainComplex A B).rank_nullity_boundary2
  have hh := (bbChainComplex A B).finrank_H1_add_stabilizer_ranks
  rw [(bbChainComplex A B).finrank_C2] at hr
  rw [← finrank_boundaries_eq_dualBoundaries A B] at hh
  change Fintype.card G = _ at hr
  change _ = 2 * Fintype.card G at hh
  omega

end Quantum.Stabilizer.Homological.BB
