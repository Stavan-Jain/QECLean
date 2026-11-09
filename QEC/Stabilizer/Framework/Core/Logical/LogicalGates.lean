import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import QEC.Foundations.Foundations
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerGroup
import QEC.Stabilizer.Framework.Core.Stabilizer.Centralizer
import QEC.Stabilizer.Framework.Core.Logical.LogicalGateGroup
import QEC.Stabilizer.Foundations.PauliGroup

/-!
# Logical gates

A logical gate of a stabilizer group `S` is a unitary that maps the codespace
of `S` to itself: `IsLogicalGate U S` is membership of `U` in
`logicalGateGroup S`.

Main results:

- `isLogicalGate_iff`, `isLogicalGate_iff_conjugation`,
  `isLogicalGate_iff_conjugation_matrix`: `U` is a logical gate iff it maps
  codespace states to codespace states, iff for every `g ∈ S` the conjugate
  `U g U†` fixes every codespace state (stated for gates and for matrices);
- `isLogicalGate_of_conjugates_toSubgroup`,
  `isLogicalGate_of_generator_set_conjugation`: a unitary whose conjugation
  action maps `S`, or just a generating set of `S`, into `S` is a logical gate.
-/

namespace Quantum
namespace StabilizerGroup

variable {n : ℕ}

open Matrix

/-- A unitary gate is a logical gate for `S` if it lies in the logical gate
group of `S`, i.e. maps the codespace to itself. -/
def IsLogicalGate (U : NQubitGate n) (S : StabilizerGroup n) : Prop :=
  U ∈ logicalGateGroup S

/-- `U` is a logical gate iff it maps every codespace state to a codespace
state. -/
theorem isLogicalGate_iff (U : NQubitGate n) (S : StabilizerGroup n) :
    IsLogicalGate U S ↔ ∀ ψ, IsInCodespace ψ S → IsInCodespace (U • ψ) S :=
  mem_logicalGateGroup_iff U S

/-- `U` is a logical gate iff for every `g ∈ S` the matrix `U g U†` fixes every
codespace state. -/
theorem isLogicalGate_iff_conjugation_matrix (U : NQubitGate n) (S : StabilizerGroup n) :
    IsLogicalGate U S ↔ ∀ g ∈ S.toSubgroup, ∀ ψ : NQubitState n,
      IsInCodespace ψ S → (U.val * g.toMatrix * star U.val).mulVec ψ.val = ψ.val :=
  mem_logicalGateGroup_iff_conjugation U S

/-- `U` is a logical gate iff for every `g ∈ S` the conjugated gate
`conjByGate U g.gate` fixes every codespace state. -/
theorem isLogicalGate_iff_conjugation (U : NQubitGate n) (S : StabilizerGroup n) :
    IsLogicalGate U S ↔ ∀ g ∈ S.toSubgroup, ∀ ψ : NQubitState n,
      IsInCodespace ψ S → (conjByGate U g.gate) • ψ = ψ := by
  simp only [isLogicalGate_iff_conjugation_matrix, Subtype.ext_iff, smul_QState_val,
    conjByGate_val, NQubitPauliGroupElement.gate_val]

/-- Being a logical gate depends only on the underlying stabilizer subgroup. -/
theorem isLogicalGate_iff_toSubgroup_eq (U : NQubitGate n) (S T : StabilizerGroup n)
    (h : S.toSubgroup = T.toSubgroup) : IsLogicalGate U S ↔ IsLogicalGate U T := by
  rw [IsLogicalGate, IsLogicalGate, mem_logicalGateGroup_iff_forall_mem,
    mem_logicalGateGroup_iff_forall_mem, codespaceSubmodule_eq_of_toSubgroup_eq S T h]

/-!
## Logical gates from the conjugation action on generators
-/

/-- If conjugation by `U` maps every element of `T` into `closure T`, then it
maps every element of `closure T` into `closure T`. -/
lemma conjugates_mem_closure_of_set_conjugates
    (U : NQubitGate n) (T : Set (NQubitPauliGroupElement n))
    (hgen : ∀ g ∈ T, ∃ g' ∈ Subgroup.closure T, conjByGate U g.toGate = g'.toGate) :
    ∀ g ∈ Subgroup.closure T, ∃ g' ∈ Subgroup.closure T, conjByGate U g.toGate = g'.toGate := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hgen x hx
  | one => exact ⟨1, Subgroup.one_mem _, by rw [NQubitPauliGroupElement.toGate_one, conjByGate_one]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', hx', hcx⟩ := hx
    obtain ⟨y', hy', hcy⟩ := hy
    exact ⟨x' * y', Subgroup.mul_mem _ hx' hy', by
      rw [NQubitPauliGroupElement.toGate_mul, conjByGate_mul, hcx, hcy,
        ← NQubitPauliGroupElement.toGate_mul]⟩
  | inv x _ hx =>
    obtain ⟨x', hx', hcx⟩ := hx
    exact ⟨x'⁻¹, Subgroup.inv_mem _ hx', by
      rw [NQubitPauliGroupElement.toGate_inv, conjByGate_inv, hcx,
        ← NQubitPauliGroupElement.toGate_inv]⟩

/-- If conjugation by `U` maps every element of `S` to an element of `S`, then
`U` is a logical gate for `S`. -/
lemma isLogicalGate_of_conjugates_toSubgroup
    (U : NQubitGate n) (S : StabilizerGroup n)
    (hconj : ∀ g ∈ S.toSubgroup, ∃ g' ∈ S.toSubgroup, conjByGate U g.toGate = g'.toGate) :
    IsLogicalGate U S := by
  rw [isLogicalGate_iff_conjugation]
  intro g hg ψ hψ
  obtain ⟨g', hg', hgg'⟩ := hconj g hg
  rw [NQubitPauliGroupElement.gate_eq_toGate, hgg']
  exact Subtype.ext (by
    rw [smul_QState_val, NQubitPauliGroupElement.toGate_val]
    exact hψ g' hg')

/-- If `S.toSubgroup = closure T` and conjugation by `U` maps every element of
`T` to an element of `S`, then `U` is a logical gate for `S`. -/
lemma isLogicalGate_of_generator_set_conjugation
    (U : NQubitGate n) (S : StabilizerGroup n) (T : Set (NQubitPauliGroupElement n))
    (hS : S.toSubgroup = Subgroup.closure T)
    (hgen : ∀ g ∈ T, ∃ g' ∈ S.toSubgroup, conjByGate U g.toGate = g'.toGate) :
    IsLogicalGate U S := by
  refine isLogicalGate_of_conjugates_toSubgroup U S ?_
  rw [hS] at hgen ⊢
  exact conjugates_mem_closure_of_set_conjugates U T hgen

end StabilizerGroup
end Quantum
