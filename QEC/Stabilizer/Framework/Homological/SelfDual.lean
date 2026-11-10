import QEC.Stabilizer.Framework.Homological.LogicalCorrespondence

/-!
# Self-dual CSS chain complexes

A binary check matrix `H : F → Q → ZMod 2` whose rows are mutually orthogonal
defines a CSS code with the same checks in the X and Z sectors: the chain
complex `SelfDual.homologicalCode H` has `∂₂ = checkCombination H` (the
combinations of the rows) and `∂₁ = syndrome H` (the pairings with the rows),
and `∂₁ ∘ ∂₂ = 0` is the orthogonality of the rows (`syndrome_checkCombination`).

For this complex the two transposes are the boundary maps themselves
(`cutMap_eq_boundary2`, `dualBoundary_eq_boundary1`), so the dual cycles and
dual boundaries are the cycles and boundaries (`dualCycles_eq_cycles`,
`dualBoundaries_eq_boundaries`).
-/

namespace Quantum.Stabilizer.Homological

open scoped BigOperators

namespace SelfDual

variable {Q F : Type} [Fintype Q] [Fintype F]

/-- The syndrome map of a binary check matrix: `c ↦ (f ↦ ∑ q, H f q * c q)`. -/
def syndrome (H : F → Q → ZMod 2) : (Q → ZMod 2) →ₗ[ZMod 2] (F → ZMod 2) where
  toFun c f := ∑ q, H f q * c q
  map_add' c c' := by
    ext f
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' a c := by
    ext f
    simp [Finset.mul_sum, mul_left_comm]

/-- The linear combinations of the rows of a binary check matrix:
`c ↦ (q ↦ ∑ f, c f * H f q)`. -/
def checkCombination (H : F → Q → ZMod 2) :
    (F → ZMod 2) →ₗ[ZMod 2] (Q → ZMod 2) where
  toFun c q := ∑ f, c f * H f q
  map_add' c c' := by
    ext q
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    ext q
    simp [Finset.mul_sum, mul_assoc]

omit [Fintype F] in
/-- Pointwise evaluation of the syndrome map. -/
@[simp] theorem syndrome_apply (H : F → Q → ZMod 2) (c : Q → ZMod 2) (f : F) :
    syndrome H c f = ∑ q, H f q * c q := rfl

omit [Fintype Q] in
/-- Pointwise evaluation of the check-combination map. -/
@[simp] theorem checkCombination_apply (H : F → Q → ZMod 2)
    (c : F → ZMod 2) (q : Q) : checkCombination H c q = ∑ f, c f * H f q := rfl

/-- Orthogonal check rows give a chain complex: the syndrome of a combination
of rows is the same combination of the pairings of the rows. -/
theorem syndrome_checkCombination (H : F → Q → ZMod 2)
    (horth : ∀ f g, ∑ q, H f q * H g q = 0) :
    (syndrome H).comp (checkCombination H) = 0 := by
  ext c f
  change (∑ q, H f q * ∑ g, c g * H g q) = 0
  simp_rw [Finset.mul_sum, mul_left_comm (H f _)]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, horth, mul_zero, Finset.sum_const_zero]

variable [DecidableEq Q] [DecidableEq F]

/-- The CSS chain complex of a self-orthogonal binary matrix `H`: the 0-cells
and the 2-cells are the rows, the 1-cells the columns, numbered by `e`. -/
def homologicalCode (H : F → Q → ZMod 2)
    (horth : ∀ f g, ∑ q, H f q * H g q = 0)
    (n : ℕ) (hcard : Fintype.card Q = n) (e : Q ≃ Fin n) : HomologicalCode where
  C0 := F
  C1 := Q
  C2 := F
  decEq0 := inferInstance
  decEq1 := inferInstance
  decEq2 := inferInstance
  fin0 := inferInstance
  fin1 := inferInstance
  fin2 := inferInstance
  boundary1 := syndrome H
  boundary2 := checkCombination H
  boundary_comp := syndrome_checkCombination H horth
  numQubits := n
  numQubits_eq := hcard
  edgeEquiv := e

variable (H : F → Q → ZMod 2) (horth : ∀ f g, ∑ q, H f q * H g q = 0)
  (n : ℕ) (hcard : Fintype.card Q = n) (e : Q ≃ Fin n)

/-- The transpose of `∂₁` of a self-dual CSS complex is its `∂₂`, the
check-combination map. -/
theorem cutMap_eq_boundary2 :
    (homologicalCode H horth n hcard e).cutMap =
      (homologicalCode H horth n hcard e).boundary2 :=
  LinearMap.ext fun c => funext fun q => by
    change (∑ f : F, c f * syndrome H (Pi.single q 1 : Q → ZMod 2) f) =
      checkCombination H c q
    simp [Pi.single_apply]

/-- The transpose of `∂₂` of a self-dual CSS complex is its `∂₁`, the syndrome
map. -/
theorem dualBoundary_eq_boundary1 :
    (homologicalCode H horth n hcard e).dualBoundary =
      (homologicalCode H horth n hcard e).boundary1 :=
  LinearMap.ext fun c => funext fun f => by
    change (∑ q : Q, c q * checkCombination H (Pi.single f 1 : F → ZMod 2) q) =
      syndrome H c f
    simp [Pi.single_apply, mul_comm]

/-- Primal and dual cycle spaces agree for self-dual CSS codes. -/
theorem dualCycles_eq_cycles :
    (homologicalCode H horth n hcard e).dualCycles =
      (homologicalCode H horth n hcard e).cycles :=
  congrArg LinearMap.ker (dualBoundary_eq_boundary1 H horth n hcard e)

/-- Primal and dual boundary spaces agree for self-dual CSS codes. -/
theorem dualBoundaries_eq_boundaries :
    (homologicalCode H horth n hcard e).dualBoundaries =
      (homologicalCode H horth n hcard e).boundaries :=
  congrArg LinearMap.range (cutMap_eq_boundary2 H horth n hcard e)

end SelfDual

end Quantum.Stabilizer.Homological
