import Mathlib.LinearAlgebra.Trace
import QEC.Stabilizer.Framework.Core.Stabilizer.Codespace
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode

/-!
# Dimension of a stabilizer codespace

Averaging the Pauli representation over a stabilizer group gives a projection
onto its complex codespace. Its trace is `2^n / |S|`, so a `StabilizerCode n k`
has codespace dimension exactly `2^k`.
-/

namespace Quantum
namespace StabilizerGroup

open Matrix
open scoped BigOperators

variable {n : ℕ}

noncomputable section

/-- The stabilizer sum acts on a codespace vector by the group order. -/
lemma stabilizerSum_mulVec_of_mem (S : StabilizerGroup n) (v : NQubitVec n)
    (hv : v ∈ codespaceSubmodule S) :
    (stabilizerSum S).mulVec v = (Nat.card S.toSubgroup : ℂ) • v := by
  classical
  rw [stabilizerSum, Matrix.sum_mulVec]
  have hcard : (Finset.univ.filter (fun g => g ∈ S.toSubgroup)).card =
      Nat.card S.toSubgroup := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc
    _ = ∑ _g ∈ Finset.univ.filter (fun g => g ∈ S.toSubgroup), v := by
      apply Finset.sum_congr rfl
      intro g hg
      exact hv g (Finset.mem_filter.mp hg).2
    _ = (Nat.card S.toSubgroup : ℂ) • v := by
      simp only [Finset.sum_const, hcard, Nat.cast_smul_eq_nsmul]

/-- The group average, regarded as a linear endomorphism of state vectors. -/
def codespaceProjector (S : StabilizerGroup n) : NQubitVec n →ₗ[ℂ] NQubitVec n :=
  (Nat.card S.toSubgroup : ℂ)⁻¹ • (stabilizerSum S).mulVecLin

/-- Averaging over the stabilizer group projects onto its complex codespace. -/
theorem codespaceProjector_isProj (S : StabilizerGroup n) :
    LinearMap.IsProj (codespaceSubmodule S) (codespaceProjector S) := by
  classical
  have hcard : (Nat.card S.toSubgroup : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  constructor
  · intro v g hg
    change g.toMatrix.mulVec ((Nat.card S.toSubgroup : ℂ)⁻¹ •
      (stabilizerSum S).mulVec v) = _
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, mul_stabilizerSum_eq S g hg]
    rfl
  · intro v hv
    change (Nat.card S.toSubgroup : ℂ)⁻¹ • (stabilizerSum S).mulVec v = v
    rw [stabilizerSum_mulVec_of_mem S v hv, smul_smul, inv_mul_cancel₀ hcard, one_smul]

/-- The trace of the codespace projector is the ambient dimension divided by
the order of the stabilizer group. -/
lemma trace_codespaceProjector (S : StabilizerGroup n) :
    LinearMap.trace ℂ (NQubitVec n) (codespaceProjector S) =
      (2 : ℂ) ^ n / Nat.card S.toSubgroup := by
  rw [codespaceProjector, map_smul]
  change (Nat.card S.toSubgroup : ℂ)⁻¹ *
    LinearMap.trace ℂ (NQubitVec n) (stabilizerSum S).toLin' = _
  rw [Matrix.trace_toLin'_eq, trace_stabilizerSum, div_eq_mul_inv, mul_comm]

/-- The complex codespace dimension times the stabilizer group order is the
ambient dimension `2^n`. -/
theorem finrank_codespace_mul_card (S : StabilizerGroup n) :
    Module.finrank ℂ (codespaceSubmodule S) * Nat.card S.toSubgroup = 2 ^ n := by
  have hcard : (Nat.card S.toSubgroup : ℂ) ≠ 0 := by
    classical
    exact_mod_cast Nat.card_pos.ne'
  have h := (codespaceProjector_isProj S).trace
  rw [trace_codespaceProjector] at h
  have hdim := (div_eq_iff hcard).mp h
  exact_mod_cast hdim.symm

end

/-- A stabilizer code encoding `k` logical qubits has complex codespace
dimension exactly `2^k`. -/
theorem StabilizerCode.finrank_codespace {n k : ℕ} (C : StabilizerCode n k) :
    Module.finrank ℂ (StabilizerGroup.codespaceSubmodule C.toStabilizerGroup) = 2 ^ k := by
  have h := StabilizerGroup.finrank_codespace_mul_card C.toStabilizerGroup
  rw [C.card_eq] at h
  apply Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos (n - k))
  calc
    _ = 2 ^ n := h
    _ = 2 ^ k * 2 ^ (n - k) := by rw [← pow_add, Nat.add_sub_of_le C.hk]

end StabilizerGroup
end Quantum
