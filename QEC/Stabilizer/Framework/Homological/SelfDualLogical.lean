import QEC.Stabilizer.Framework.Homological.SelfDual
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The binary logical class of a self-dual CSS code

For independent, mutually orthogonal binary checks `H : F → Q → ZMod 2` with
`|Q| = 2 |F| + 1`, the zero-syndrome space is the row span together with the
all-ones chain (`ker_syndrome_eq_range_sup_span`). Hence every zero-syndrome
chain is a combination of rows plus its parity times the all-ones chain
(`exists_checkCombination_add_parity`), and the row span is exactly the
even-parity part of the zero-syndrome space
(`mem_range_checkCombination_iff`): the all-ones chain represents the one
nontrivial logical class.
-/

open scoped BigOperators

namespace Quantum.Stabilizer.Homological.SelfDual

variable {Q F : Type} [Fintype Q] [Fintype F]

/-- The syndrome and check-combination maps have the same rank, because
their matrices are transposes. -/
theorem finrank_syndrome_eq_finrank_checkCombination (H : F → Q → ZMod 2) :
    Module.finrank (ZMod 2) (LinearMap.range (syndrome H)) =
      Module.finrank (ZMod 2) (LinearMap.range (checkCombination H)) := by
  have htranspose : checkCombination H = Matrix.mulVecLin (Matrix.transpose H) := by
    ext c q
    change (∑ f, c f * H f q) = ∑ f, H f q * c f
    exact Finset.sum_congr rfl fun f _ => mul_comm _ _
  rw [htranspose]
  exact (Matrix.rank_transpose H).symm

omit [Fintype F] in
/-- Every self-orthogonal binary check row has even parity. -/
theorem sum_row_eq_zero (H : F → Q → ZMod 2)
    (horth : ∀ f g, ∑ q, H f q * H g q = 0) (f : F) :
    ∑ q, H f q = 0 := by
  have hsquare : ∀ a : ZMod 2, a * a = a := by decide
  simpa only [hsquare] using horth f f

/-- Every combination of self-orthogonal binary check rows has even
parity. -/
theorem sum_checkCombination_eq_zero (H : F → Q → ZMod 2)
    (horth : ∀ f g, ∑ q, H f q * H g q = 0) (a : F → ZMod 2) :
    ∑ q, checkCombination H a q = 0 := by
  simp only [checkCombination_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_row_eq_zero H horth]
  simp

omit [Fintype F] in
/-- An odd number of qubits is `1` in `ZMod 2`. -/
private lemma card_cast_eq_one {m : ℕ} (hcard : Fintype.card Q = 2 * m + 1) :
    (Fintype.card Q : ZMod 2) = 1 := by
  rw [hcard]
  simp [show (2 : ZMod 2) = 0 from rfl]

/-- For independent self-orthogonal checks with `n = 2m + 1`, the cycle
space is the check span together with the all-ones chain: the all-ones chain
has zero syndrome and odd parity, so it is not in the check span, and the two
sides have the same dimension `m + 1`. -/
theorem ker_syndrome_eq_range_sup_span (H : F → Q → ZMod 2)
    (horth : ∀ f g, ∑ q, H f q * H g q = 0)
    (hinj : Function.Injective (checkCombination H))
    (hcard : Fintype.card Q = 2 * Fintype.card F + 1) :
    LinearMap.ker (syndrome H) =
      LinearMap.range (checkCombination H) ⊔
        Submodule.span (ZMod 2) {fun _ : Q => (1 : ZMod 2)} := by
  classical
  let w : Q → ZMod 2 := fun _ => 1
  have hwpar : ∑ q, w q = 1 := by
    simpa only [w, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      using card_cast_eq_one hcard
  have hwker : w ∈ LinearMap.ker (syndrome H) :=
    LinearMap.mem_ker.mpr <| funext fun f => by
      simpa only [syndrome_apply, w, mul_one, Pi.zero_apply] using sum_row_eq_zero H horth f
  have hrange : LinearMap.range (checkCombination H) ≤ LinearMap.ker (syndrome H) :=
    LinearMap.range_le_ker_iff.2 (syndrome_checkCombination H horth)
  have hwnot : w ∉ LinearMap.range (checkCombination H) := by
    rintro ⟨a, ha⟩
    have hp := sum_checkCombination_eq_zero H horth a
    rw [ha, hwpar] at hp
    exact one_ne_zero hp
  have hwne : w ≠ 0 := fun hw => hwnot (hw ▸ Submodule.zero_mem _)
  have hrank : Module.finrank (ZMod 2) (LinearMap.range (checkCombination H)) =
      Fintype.card F := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]
  have hker : Module.finrank (ZMod 2) (LinearMap.ker (syndrome H)) =
      Fintype.card F + 1 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (syndrome H)
    rw [finrank_syndrome_eq_finrank_checkCombination, hrank,
      Module.finrank_fintype_fun_eq_card, hcard] at hrn
    omega
  have hsup : Module.finrank (ZMod 2)
      (LinearMap.range (checkCombination H) ⊔ Submodule.span (ZMod 2) {w} :
        Submodule (ZMod 2) (Q → ZMod 2)) =
        Fintype.card F + 1 := by
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.range (checkCombination H)) (Submodule.span (ZMod 2) {w})
    rwa [(Submodule.disjoint_span_singleton_of_notMem hwnot).eq_bot, finrank_bot, add_zero,
      hrank, finrank_span_singleton hwne] at hdim
  exact (Submodule.eq_of_le_of_finrank_eq
    (sup_le hrange ((Submodule.span_singleton_le_iff_mem _ _).mpr hwker))
    (hsup.trans hker.symm)).symm

/-- Every zero-syndrome chain is a check combination plus its parity
times the all-ones chain. -/
theorem exists_checkCombination_add_parity (H : F → Q → ZMod 2)
    (horth : ∀ f g, ∑ q, H f q * H g q = 0)
    (hinj : Function.Injective (checkCombination H))
    (hcard : Fintype.card Q = 2 * Fintype.card F + 1)
    (c : Q → ZMod 2) (hc : syndrome H c = 0) :
    ∃ a : F → ZMod 2,
      c = checkCombination H a + (∑ q, c q) • (fun _ : Q => (1 : ZMod 2)) := by
  have hmem : c ∈ LinearMap.ker (syndrome H) := hc
  rw [ker_syndrome_eq_range_sup_span H horth hinj hcard] at hmem
  obtain ⟨b, ⟨a, rfl⟩, z, hz, hsum⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have hpar := congrArg (fun v : Q → ZMod 2 => ∑ q, v q) hsum
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one,
    Finset.sum_add_distrib, sum_checkCombination_eq_zero H horth a,
    zero_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hpar
  rw [card_cast_eq_one hcard, one_mul] at hpar
  exact ⟨a, by rw [← hpar]; exact hsum.symm⟩

/-- The row span is precisely the even part of the zero-syndrome space
when independent self-orthogonal checks satisfy `n = 2m + 1`. -/
theorem mem_range_checkCombination_iff (H : F → Q → ZMod 2)
    (horth : ∀ f g, ∑ q, H f q * H g q = 0)
    (hinj : Function.Injective (checkCombination H))
    (hcard : Fintype.card Q = 2 * Fintype.card F + 1) (c : Q → ZMod 2) :
    c ∈ LinearMap.range (checkCombination H) ↔
      syndrome H c = 0 ∧ ∑ q, c q = 0 := by
  refine ⟨?_, fun ⟨hc, hpar⟩ => ?_⟩
  · rintro ⟨a, rfl⟩
    exact ⟨LinearMap.congr_fun (syndrome_checkCombination H horth) a,
      sum_checkCombination_eq_zero H horth a⟩
  · obtain ⟨a, ha⟩ := exists_checkCombination_add_parity H horth hinj hcard c hc
    rw [hpar, zero_smul, add_zero] at ha
    exact ⟨a, ha.symm⟩

end Quantum.Stabilizer.Homological.SelfDual
