import QEC.Stabilizer.Framework.Homological.LogicalCorrespondence

/-!
# Self-dual CSS chain complexes

A binary check matrix whose rows are mutually orthogonal defines a CSS code
with the same checks in the X and Z sectors. This construction supplies the
chain complex and identifies its primal and dual cycles and boundaries.
-/

namespace Quantum.Stabilizer.Homological

open scoped BigOperators

namespace SelfDual

variable {Q F : Type} [Fintype Q] [Fintype F]

/-- The syndrome map of a binary check matrix. -/
def syndrome (H : F → Q → ZMod 2) : (Q → ZMod 2) →ₗ[ZMod 2] (F → ZMod 2) where
  toFun c f := ∑ q, H f q * c q
  map_add' c c' := by
    ext f
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' a c := by
    ext f
    simp [Finset.mul_sum, mul_left_comm]

/-- A linear combination of the rows of a binary check matrix. -/
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

/-- Orthogonal check rows give a chain complex. -/
theorem syndrome_checkCombination (H : F → Q → ZMod 2)
    (horth : ∀ f g, ∑ q, H f q * H g q = 0) :
    (syndrome H).comp (checkCombination H) = 0 := by
  ext c f
  change (∑ q, H f q * ∑ g, c g * H g q) = 0
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ g, ∑ q, H f q * (c g * H g q)) =
        ∑ g, c g * ∑ q, H f q * H g q := by
      apply Finset.sum_congr rfl
      intro g _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = 0 := by simp [horth]

variable [DecidableEq Q] [DecidableEq F]

/-- The CSS chain complex associated with a self-orthogonal binary matrix,
using an explicitly chosen numbering of its physical qubits. -/
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

/-- The transpose map of a self-dual CSS complex is its check-combination
map. -/
theorem cutMap_eq_boundary2 :
    (homologicalCode H horth n hcard e).cutMap =
      (homologicalCode H horth n hcard e).boundary2 := by
  apply LinearMap.ext
  intro c
  funext q
  change (∑ f : F, c f * syndrome H (Pi.single q 1 : Q → ZMod 2) f) =
    checkCombination H c q
  simp [Pi.single_apply]

/-- The dual syndrome map equals the primal syndrome map. -/
theorem dualBoundary_eq_boundary1 :
    (homologicalCode H horth n hcard e).dualBoundary =
      (homologicalCode H horth n hcard e).boundary1 := by
  apply LinearMap.ext
  intro c
  funext f
  change (∑ q : Q, c q * checkCombination H (Pi.single f 1 : F → ZMod 2) q) =
    syndrome H c f
  simp [Pi.single_apply, mul_comm]

/-- Primal and dual cycle spaces agree for self-dual CSS codes. -/
theorem dualCycles_eq_cycles :
    (homologicalCode H horth n hcard e).dualCycles =
      (homologicalCode H horth n hcard e).cycles := by
  unfold HomologicalCode.dualCycles HomologicalCode.cycles
  rw [dualBoundary_eq_boundary1]
  rfl

/-- Primal and dual boundary spaces agree for self-dual CSS codes. -/
theorem dualBoundaries_eq_boundaries :
    (homologicalCode H horth n hcard e).dualBoundaries =
      (homologicalCode H horth n hcard e).boundaries := by
  unfold HomologicalCode.dualBoundaries HomologicalCode.boundaries
  rw [cutMap_eq_boundary2]
  rfl

end SelfDual

end Quantum.Stabilizer.Homological
