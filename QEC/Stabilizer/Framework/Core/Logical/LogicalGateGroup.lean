import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Group.Subgroup.Basic
import QEC.Foundations.Foundations
import QEC.Stabilizer.Framework.Core.Stabilizer.Codespace
import QEC.Stabilizer.Foundations.PauliGroup

/-!
# Logical gate group

The logical gate group `logicalGateGroup S` of a stabilizer group `S` is the
subgroup of n-qubit unitaries that map the codespace of `S` into itself. A
unitary maps a finite-dimensional subspace into itself only if it maps it onto
itself, which is why the set is closed under inverses.

Membership has two equivalent formulations:

- `mem_logicalGateGroup_iff`: `U` maps every codespace state to a codespace
  state;
- `mem_logicalGateGroup_iff_conjugation`: for every `g ∈ S`, the conjugate
  `U g U†` fixes every codespace state.
-/

namespace Quantum
namespace StabilizerGroup

variable {n : ℕ}

open Matrix

/-- A unitary that maps the codespace into itself maps it onto itself: its
restriction to the codespace is injective, so its range has the dimension of
the codespace. -/
private lemma exists_mulVec_eq_of_maps_codespace (U : NQubitGate n) (S : StabilizerGroup n)
    (hU : ∀ v ∈ codespaceSubmodule S, U.val.mulVec v ∈ codespaceSubmodule S) :
    ∀ v ∈ codespaceSubmodule S, ∃ w ∈ codespaceSubmodule S, U.val.mulVec w = v := by
  intro v hv
  have h_range : LinearMap.range (Matrix.mulVecLin U.val ∘ₗ (codespaceSubmodule S).subtype) =
      codespaceSubmodule S := by
    refine Submodule.eq_of_le_of_finrank_eq (Set.range_subset_iff.mpr fun x => hU x.val x.2) ?_
    rw [LinearMap.finrank_range_of_inj]
    intro x y hxy
    have h := congrArg (star U.val).mulVec hxy
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, mem_unitaryGroup_iff'.1 U.2,
      Matrix.one_mulVec] at h
    exact Subtype.ext h
  obtain ⟨⟨w, hw⟩, hwv⟩ := (SetLike.ext_iff.mp h_range v).mpr hv
  exact ⟨w, hw, hwv⟩

/-- The logical gate group of `S`: the unitaries that map the codespace of `S`
into itself. -/
def logicalGateGroup (S : StabilizerGroup n) : Subgroup (NQubitGate n) where
  carrier := { U | ∀ v ∈ codespaceSubmodule S, U.val.mulVec v ∈ codespaceSubmodule S }
  one_mem' := fun v hv => by rwa [gate_one_val, one_mulVec]
  mul_mem' := fun ha hb v hv => by
    rw [gate_mul_val, ← mulVec_mulVec]
    exact ha _ (hb v hv)
  inv_mem' := fun {U} hU v hv => by
    obtain ⟨w, hw, rfl⟩ := exists_mulVec_eq_of_maps_codespace U S hU v hv
    rwa [mulVec_mulVec, gate_val_inv_mul, one_mulVec]

/-- `U` is in the logical gate group iff it maps every vector of the codespace
into the codespace. -/
lemma mem_logicalGateGroup_iff_forall_mem (U : NQubitGate n) (S : StabilizerGroup n) :
    U ∈ logicalGateGroup S ↔
      ∀ v ∈ codespaceSubmodule S, U.val.mulVec v ∈ codespaceSubmodule S :=
  Iff.rfl

/-- `U` is in the logical gate group iff it maps every codespace state to a
codespace state. -/
lemma mem_logicalGateGroup_iff (U : NQubitGate n) (S : StabilizerGroup n) :
    U ∈ logicalGateGroup S ↔ ∀ ψ, IsInCodespace ψ S → IsInCodespace (U • ψ) S := by
  refine ⟨fun h ψ hψ => h ψ.val hψ, fun h v hv => ?_⟩
  obtain ⟨c, ψ, hψ, rfl⟩ := exists_smul_state_of_mem_codespaceSubmodule S hv
  rw [mulVec_smul]
  exact (codespaceSubmodule S).smul_mem c (h ψ hψ)

/-- `U` is in the logical gate group iff for every `g ∈ S` the conjugate
`U g U†` fixes every codespace state. Both sides say that `U†` maps the
codespace into itself. -/
lemma mem_logicalGateGroup_iff_conjugation (U : NQubitGate n) (S : StabilizerGroup n) :
    U ∈ logicalGateGroup S ↔ ∀ g ∈ S.toSubgroup, ∀ ψ : NQubitState n,
      IsInCodespace ψ S → (U.val * g.toMatrix * star U.val).mulVec ψ.val = ψ.val := by
  rw [← inv_mem_iff]
  constructor
  · intro h g hg ψ hψ
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← gate_inv_val, h ψ.val hψ g hg, mulVec_mulVec,
      gate_val_mul_inv, one_mulVec]
  · intro h v hv g hg
    obtain ⟨c, ψ, hψ, rfl⟩ := exists_smul_state_of_mem_codespaceSubmodule S hv
    have h_fix := congrArg (U⁻¹).val.mulVec (h g hg ψ hψ)
    rw [Matrix.mul_assoc, ← mulVec_mulVec, mulVec_mulVec, gate_val_inv_mul,
      one_mulVec, ← mulVec_mulVec, ← gate_inv_val] at h_fix
    rw [mulVec_smul, mulVec_smul, h_fix]

end StabilizerGroup

end Quantum
