import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic
import QEC.Stabilizer.Foundations.BinarySymplectic.Core
import QEC.Stabilizer.Foundations.BinarySymplectic.SymplecticInner
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrix
import QEC.Stabilizer.Framework.Symplectic.SymplecticSpan
import QEC.Stabilizer.Framework.Symplectic.SymplecticImage
import QEC.Stabilizer.Framework.Symplectic.SymplecticOrthogonal
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerGroup
import QEC.Stabilizer.Framework.Core.Stabilizer.Centralizer
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode
import QEC.Stabilizer.Framework.Core.Logical.LogicalOperators
import QEC.Stabilizer.Foundations.PauliGroup.NQubitElement

/-!
# Classifying the centralizer of a stabilizer group

The centralizer of a stabilizer group `S` is the symplectic orthogonal of its
symplectic image (`toSymplectic_mem_sympOrthogonal_sympImage_iff`), and the
symplectic image is isotropic (`sympImage_le_sympOrthogonal`). This file
classifies the elements of the centralizer in two ways.

- `centralizer_classify`: an element of the centralizer either has the
  operator part of a stabilizer element or is a nontrivial logical operator.
  The first alternative is about operator parts, not membership in `S`: an
  element of the centralizer may differ from a stabilizer element by a phase
  `i`, `−1` or `−i`, and is then neither in `S` nor a nontrivial logical
  operator.
- `operators_eq_stab_of_commutes_both_logicals`: in a code with one logical
  qubit, an element of the centralizer that commutes with both logical
  operators `X̄` and `Z̄` has the operator part of a stabilizer element. In
  symplectic terms, with `V` the symplectic image of the stabilizer group, the
  orthogonal of `V ⊔ span {X̄, Z̄}` is `V` itself
  (`NQubitPauliOperator.mem_of_mem_sympOrthogonal_of_pair`).
-/

namespace Quantum

variable {n : ℕ}

namespace StabilizerGroup

open NQubitPauliGroupElement NQubitPauliOperator

/-- An element of the centralizer of a stabilizer group either has the operator
part of a stabilizer element or is a nontrivial logical operator. -/
theorem centralizer_classify (S : StabilizerGroup n) (g : NQubitPauliGroupElement n)
    (hg : g ∈ centralizer S) :
    (∃ s ∈ S.toSubgroup, s.operators = g.operators) ∨ IsNontrivialLogicalOperator g S :=
  or_iff_not_imp_left.mpr fun h =>
    (IsNontrivialLogicalOperator_iff g S).mpr ⟨hg, fun s hs heq => h ⟨s, hs, heq⟩⟩

/-- A Pauli group element lies in the centralizer of `S` iff its symplectic
vector is orthogonal to the symplectic image of `S`. -/
lemma toSymplectic_mem_sympOrthogonal_sympImage_iff (S : StabilizerGroup n)
    (g : NQubitPauliGroupElement n) :
    toSymplectic g.operators ∈ sympOrthogonal S.sympImage ↔ g ∈ centralizer S := by
  rw [sympImage, mem_sympOrthogonal_span_iff, Set.forall_mem_image, mem_centralizer_iff]
  exact forall₂_congr fun s _ => symplecticBilinear_toSymplectic_eq_zero_iff s g

/-- The symplectic image of a stabilizer group is isotropic: it lies in its own
symplectic orthogonal. -/
lemma sympImage_le_sympOrthogonal (S : StabilizerGroup n) :
    S.sympImage ≤ sympOrthogonal S.sympImage := fun v hv => by
  obtain ⟨s, hs, rfl⟩ := (mem_sympImage_iff S v).mp hv
  exact (toSymplectic_mem_sympOrthogonal_sympImage_iff S s).mpr (stabilizer_le_centralizer S hs)

/-- In a code with one logical qubit, an element of the centralizer that
commutes with both logical operators has the operator part of a stabilizer
element.

The symplectic image `V` of the stabilizer group is isotropic of dimension
`n - 1`, and the symplectic vectors of the logical operators are orthogonal to
`V` and pair to `1`, so `mem_of_mem_sympOrthogonal_of_pair` puts the symplectic
vector of `g` in `V`. -/
theorem operators_eq_stab_of_commutes_both_logicals (C : StabilizerCodeWithLogicals n 1)
    (g : NQubitPauliGroupElement n) (hg : g ∈ centralizer C.toStabilizerGroup)
    (hX : g * C.logicalX 0 = C.logicalX 0 * g)
    (hZ : g * C.logicalZ 0 = C.logicalZ 0 * g) :
    ∃ s ∈ C.toStabilizerGroup.toSubgroup, s.operators = g.operators := by
  have hmem := toSymplectic_mem_sympOrthogonal_sympImage_iff C.toStabilizerGroup
  have h : toSymplectic g.operators ∈ C.toStabilizerGroup.sympImage :=
    mem_of_mem_sympOrthogonal_of_pair (sympImage_le_sympOrthogonal _)
      (by rw [C.toStabilizerCode.finrank_sympImage]; have := C.hk; omega)
      ((hmem _).mpr (C.logicalOps 0).x_mem_centralizer)
      ((hmem _).mpr (C.logicalOps 0).z_mem_centralizer)
      ((symplecticBilinear_toSymplectic _ _).trans <|
        (anticommutes_iff_symplectic_inner_one _ _).mp (C.logicalOps 0).anticommute)
      ((hmem g).mpr hg)
      ((symplecticBilinear_toSymplectic_eq_zero_iff _ g).mpr hX.symm)
      ((symplecticBilinear_toSymplectic_eq_zero_iff _ g).mpr hZ.symm)
  obtain ⟨s, hs, hsg⟩ := (mem_sympImage_iff _ _).mp h
  exact ⟨s, hs, toSymplectic_injective hsg⟩

end StabilizerGroup

end Quantum
