import Mathlib.LinearAlgebra.Trace
import QEC.Stabilizer.Framework.Core.Stabilizer.Codespace
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode

/-!
# Dimension of a stabilizer codespace

Averaging the matrices of a stabilizer group `S` gives a projection onto its
codespace (`codespaceProjector_isProj`). Its trace is `2 ^ n / |S|`
(`trace_codespaceProjector`), and the trace of a projection is the dimension of
its range, so `dim (codespace) * |S| = 2 ^ n` (`finrank_codespace_mul_card`).
In particular a `StabilizerCode n k` has codespace dimension exactly `2 ^ k`
(`StabilizerCode.finrank_codespace`).
-/

namespace Quantum
namespace StabilizerGroup

open Matrix
open scoped BigOperators

variable {n : ℕ}

noncomputable section

/-- The order of a stabilizer group is nonzero as a complex number. -/
private lemma card_toSubgroup_ne_zero (S : StabilizerGroup n) :
    (Nat.card S.toSubgroup : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr Nat.card_pos.ne'

/-- The stabilizer sum acts on a codespace vector as multiplication by the
group order. -/
lemma stabilizerSum_mulVec_of_mem (S : StabilizerGroup n) (v : NQubitVec n)
    (hv : v ∈ codespaceSubmodule S) :
    (stabilizerSum S).mulVec v = (Nat.card S.toSubgroup : ℂ) • v := by
  classical
  rw [stabilizerSum, Matrix.sum_mulVec,
    Finset.sum_congr rfl fun g hg => hv g (Finset.mem_filter.mp hg).2, Finset.sum_const,
    ← Nat.cast_smul_eq_nsmul ℂ, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The average of the matrices of the stabilizer group, as a linear
endomorphism of the n-qubit vector space. -/
def codespaceProjector (S : StabilizerGroup n) : NQubitVec n →ₗ[ℂ] NQubitVec n :=
  (Nat.card S.toSubgroup : ℂ)⁻¹ • (stabilizerSum S).mulVecLin

/-- Averaging over the stabilizer group is a projection onto the codespace. -/
theorem codespaceProjector_isProj (S : StabilizerGroup n) :
    LinearMap.IsProj (codespaceSubmodule S) (codespaceProjector S) := by
  refine ⟨fun v => (codespaceSubmodule S).smul_mem _ (stabilizerSum_mulVec_mem S v),
    fun v hv => ?_⟩
  change (Nat.card S.toSubgroup : ℂ)⁻¹ • (stabilizerSum S).mulVec v = v
  rw [stabilizerSum_mulVec_of_mem S v hv, smul_smul, inv_mul_cancel₀ (card_toSubgroup_ne_zero S),
    one_smul]

/-- The trace of the codespace projector is the ambient dimension divided by
the order of the stabilizer group. -/
lemma trace_codespaceProjector (S : StabilizerGroup n) :
    LinearMap.trace ℂ (NQubitVec n) (codespaceProjector S) =
      (2 : ℂ) ^ n / Nat.card S.toSubgroup := by
  rw [codespaceProjector, map_smul]
  change (Nat.card S.toSubgroup : ℂ)⁻¹ *
    LinearMap.trace ℂ (NQubitVec n) (stabilizerSum S).toLin' = _
  rw [Matrix.trace_toLin'_eq, trace_stabilizerSum, div_eq_mul_inv, mul_comm]

/-- The dimension of the codespace times the order of the stabilizer group is
the ambient dimension `2 ^ n`. -/
theorem finrank_codespace_mul_card (S : StabilizerGroup n) :
    Module.finrank ℂ (codespaceSubmodule S) * Nat.card S.toSubgroup = 2 ^ n := by
  have h := (codespaceProjector_isProj S).trace
  rw [trace_codespaceProjector] at h
  exact_mod_cast ((div_eq_iff (card_toSubgroup_ne_zero S)).mp h).symm

end

/-- A stabilizer code encoding `k` logical qubits has codespace dimension
exactly `2 ^ k`. -/
theorem StabilizerCode.finrank_codespace {n k : ℕ} (C : StabilizerCode n k) :
    Module.finrank ℂ (StabilizerGroup.codespaceSubmodule C.toStabilizerGroup) = 2 ^ k := by
  refine Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos (n - k)) ?_
  rw [← C.card_eq, finrank_codespace_mul_card, C.card_eq, ← pow_add, Nat.add_sub_of_le C.hk]

end StabilizerGroup
end Quantum
