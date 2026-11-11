import QEC.Foundations.Basic
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerGroup
import QEC.Stabilizer.Foundations.PauliGroup
import QEC.Stabilizer.Foundations.PauliGroup.Representation

/-!
# Codespace and stabilizer sum

The codespace of a stabilizer group `S` is the subspace of vectors fixed by
every element of `S`. This file provides:

- `StabilizerGroup.codespaceSubmodule S`: the codespace as a submodule of the
  n-qubit vector space;
- `StabilizerGroup.stabilizerSum S`: the sum of the matrices of all elements of
  `S`. Its trace is `2 ^ n` (`trace_stabilizerSum`), because the identity is the
  only element of `S` with nonzero trace, and it maps every vector into the
  codespace (`stabilizerSum_mulVec_mem`);
- `StabilizerGroup.exists_codespace_state`: the codespace contains a state;
- `StabilizerGroup.exists_smul_state_of_mem_codespaceSubmodule`: every vector of
  the codespace is a scalar multiple of a codespace state.
-/

namespace Quantum
namespace StabilizerGroup

variable {n : ℕ}
open Matrix
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.decEq
attribute [local instance] Classical.decPred

/-- The four single-qubit Pauli operators form a finite type. -/
instance : Fintype PauliOperator where
  elems := {PauliOperator.I, PauliOperator.X, PauliOperator.Y, PauliOperator.Z}
  complete := by
    intro x
    cases x <;> simp +decide

/-- The n-qubit Pauli group is finite: an element is a phase power in `Fin 4`
together with one Pauli operator per qubit. -/
noncomputable instance : Fintype (NQubitPauliGroupElement n) :=
  Fintype.ofEquiv (Fin 4 × (Fin n → PauliOperator))
  { toFun := fun p => ⟨p.1, p.2⟩
    invFun := fun p => (p.phasePower, p.operators)
    left_inv := by intro p; simp
    right_inv := by intro p; cases p; simp }

/-!
## The codespace
-/

/-- The codespace of `S` as a submodule of the n-qubit vector space: the vectors
fixed by the matrix of every element of `S`. -/
def codespaceSubmodule (S : StabilizerGroup n) : Submodule ℂ (NQubitVec n) where
  carrier := { v | ∀ g ∈ S.toSubgroup, Matrix.mulVec g.toMatrix v = v }
  add_mem' := by intro a b ha hb g hg; rw [Matrix.mulVec_add, ha g hg, hb g hg]
  zero_mem' := by intro g hg; rw [Matrix.mulVec_zero]
  smul_mem' := by intro c x hx g hg; rw [Matrix.mulVec_smul, hx g hg]

/-- A state is in the codespace iff its vector lies in
`codespaceSubmodule S`. -/
lemma mem_codespace_iff_mem_submodule (ψ : NQubitState n) (S : StabilizerGroup n) :
    IsInCodespace ψ S ↔ ψ.val ∈ codespaceSubmodule S :=
  Iff.rfl

/-- The codespace depends only on the underlying subgroup. -/
lemma codespaceSubmodule_eq_of_toSubgroup_eq (S T : StabilizerGroup n)
    (h : S.toSubgroup = T.toSubgroup) : codespaceSubmodule S = codespaceSubmodule T :=
  SetLike.ext fun v => by
    change (∀ g ∈ S.toSubgroup, _) ↔ (∀ g ∈ T.toSubgroup, _)
    rw [h]

/-!
## The stabilizer sum
-/

/-- The sum of the matrices of all elements of the stabilizer group. -/
noncomputable def stabilizerSum (S : StabilizerGroup n) :
    Matrix (NQubitBasis n) (NQubitBasis n) ℂ :=
  ∑ g ∈ (Finset.univ.filter (fun g => g ∈ S.toSubgroup)), g.toMatrix

/-- The only element of a stabilizer group whose operator part is the identity
is the identity: any other phase would put `-I`, or a square root of it, in the
group. -/
lemma eq_one_of_mem_stabilizer_and_is_scalar (S : StabilizerGroup n) (g : NQubitPauliGroupElement n)
    (hg : g ∈ S.toSubgroup) (h_scalar : g.operators = NQubitPauliOperator.identity n) :
    g = 1 := by
  obtain ⟨k, ops⟩ := g
  subst h_scalar
  have h_sq := S.toSubgroup.mul_mem hg hg
  rw [show (⟨k, NQubitPauliOperator.identity n⟩ : NQubitPauliGroupElement n) *
      ⟨k, NQubitPauliOperator.identity n⟩ = ⟨k + k, NQubitPauliOperator.identity n⟩ by
    ext : 1 <;> simp [NQubitPauliGroupElement.mul,
      NQubitPauliGroupElement.mulOp_identity_left_phase,
      NQubitPauliGroupElement.mulOp_identity_left_op]] at h_sq
  fin_cases k
  · rfl
  · exact absurd h_sq S.no_neg_identity
  · exact absurd hg S.no_neg_identity
  · exact absurd h_sq S.no_neg_identity

/-- A Pauli group element whose operator part is not the identity has trace
zero. -/
lemma trace_eq_zero_of_ne_identity (g : NQubitPauliGroupElement n)
    (h_ne_I : g.operators ≠ NQubitPauliOperator.identity n) :
    (g.toMatrix).trace = 0 := by
  have h := NQubitPauliOperator.trace_mul g.operators (NQubitPauliOperator.identity n)
  rw [NQubitPauliOperator.identity_toMatrix, mul_one, if_neg h_ne_I] at h
  rw [NQubitPauliGroupElement.toMatrix, Matrix.trace_smul, h, smul_zero]

/-- The trace of the stabilizer sum is `2 ^ n`: only the identity
contributes. -/
lemma trace_stabilizerSum (S : StabilizerGroup n) : (stabilizerSum S).trace = (2 : ℂ)^n := by
  rw [stabilizerSum, Matrix.trace_sum,
    Finset.sum_eq_single_of_mem 1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, S.one_mem⟩)
      fun g hg hne => trace_eq_zero_of_ne_identity g fun h =>
        hne (eq_one_of_mem_stabilizer_and_is_scalar S g (Finset.mem_filter.mp hg).2 h),
    NQubitPauliGroupElement.toMatrix_one, Matrix.trace_one]
  simp

/-- The stabilizer sum is not the zero matrix. -/
lemma stabilizerSum_ne_zero (S : StabilizerGroup n) : stabilizerSum S ≠ 0 := by
  intro h
  have h_trace := trace_stabilizerSum S
  rw [h, Matrix.trace_zero] at h_trace
  exact pow_ne_zero n two_ne_zero h_trace.symm

/-- Multiplying the stabilizer sum by an element of `S` permutes its summands,
so leaves it unchanged. -/
lemma mul_stabilizerSum_eq (S : StabilizerGroup n) (g : NQubitPauliGroupElement n)
    (hg : g ∈ S.toSubgroup) : g.toMatrix * stabilizerSum S = stabilizerSum S := by
  rw [stabilizerSum, Finset.mul_sum]
  refine Finset.sum_equiv (Equiv.mulLeft g) (fun h => ?_)
    (fun h _ => (NQubitPauliGroupElement.toMatrix_mul g h).symm)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_mulLeft,
    S.toSubgroup.mul_mem_cancel_left hg]

/-- The stabilizer sum maps every vector into the codespace. -/
lemma stabilizerSum_mulVec_mem (S : StabilizerGroup n) (v : NQubitVec n) :
    (stabilizerSum S).mulVec v ∈ codespaceSubmodule S := fun g hg => by
  rw [Matrix.mulVec_mulVec, mul_stabilizerSum_eq S g hg]

/-!
## States in the codespace
-/

/-- A nonzero vector can be rescaled to a unit vector. -/
private lemma exists_smul_norm_eq_one {v : NQubitVec n} (hv : v ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ Quantum.norm (c • v) = 1 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have h : 0 < Quantum.norm v := Real.sqrt_pos.mpr (Finset.sum_pos' (fun _ _ => sq_nonneg _)
    ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩)
  refine ⟨((Quantum.norm v)⁻¹ : ℝ), Complex.ofReal_ne_zero.mpr (inv_ne_zero h.ne'), ?_⟩
  rw [Quantum.norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr h.le),
    inv_mul_cancel₀ h.ne']

/-- The codespace of a stabilizer group contains a state: the stabilizer sum is
nonzero, so it maps some vector to a nonzero vector of the codespace, which can
be normalized. -/
lemma exists_codespace_state (S : StabilizerGroup n) : ∃ ψ : NQubitState n, IsInCodespace ψ S := by
  obtain ⟨v, hv⟩ : ∃ v : NQubitVec n, (stabilizerSum S).mulVec v ≠ 0 := by
    by_contra! h
    exact stabilizerSum_ne_zero S (Matrix.mulVec_injective (funext fun v => by simp [h v]))
  obtain ⟨c, -, hc⟩ := exists_smul_norm_eq_one hv
  exact ⟨⟨_, hc⟩, (codespaceSubmodule S).smul_mem c (stabilizerSum_mulVec_mem S v)⟩

/-- Every vector of the codespace is a scalar multiple of a codespace state. A
statement that is linear in the vector therefore holds on the whole codespace
as soon as it holds for codespace states. -/
lemma exists_smul_state_of_mem_codespaceSubmodule (S : StabilizerGroup n) {v : NQubitVec n}
    (hv : v ∈ codespaceSubmodule S) :
    ∃ (c : ℂ) (ψ : NQubitState n), IsInCodespace ψ S ∧ v = c • ψ.val := by
  by_cases hv0 : v = 0
  · obtain ⟨ψ, hψ⟩ := exists_codespace_state S
    exact ⟨0, ψ, hψ, by rw [hv0, zero_smul]⟩
  · obtain ⟨c, hc0, hc⟩ := exists_smul_norm_eq_one hv0
    exact ⟨c⁻¹, ⟨_, hc⟩, (codespaceSubmodule S).smul_mem c hv,
      by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩

end

end StabilizerGroup
end Quantum
