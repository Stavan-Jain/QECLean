import QEC.Stabilizer.Framework.Homological.Certificate.MaskFiber
import QEC.Stabilizer.Framework.Homological.Certificate.DualCover
import QEC.Stabilizer.Framework.Homological.Certificate.ParityFold
import Mathlib.Algebra.BigOperators.Pi

namespace Quantum.Stabilizer.Homological.F2Mask
open scoped BigOperators

/-- The support of a packed mask in its finite coordinate space. -/
def maskSupport (n m : Nat) : Finset (Fin n) :=
  Finset.univ.filter fun q => chainOfMask (Equiv.refl (Fin n)) m q ≠ 0

/-- A binary chain is the sum of unit point masses on its support. -/
theorem binary_eq_sum_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ZMod 2) :
    c = ∑ i ∈ Finset.univ.filter (fun i => c i ≠ 0), Pi.single i (1 : ZMod 2) := by
  conv_lhs => rw [pi_eq_sum_univ' c]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (c i) with h | h
  · simp only [h, zero_smul, ne_eq, not_true_eq_false, if_false]
  · simp only [h, one_smul]
    split
    · rfl
    · contradiction

/-- Reconstruction of a point mass is its indexed packed column. -/
theorem reconLinear_single {n m : Nat} (cols : List (Nat × Nat)) (q : Fin n) :
    reconLinear (Equiv.refl (Fin n)) (Equiv.refl (Fin m)) cols (Pi.single q 1) =
      chainOfMask (Equiv.refl (Fin m)) (reconX cols (2 ^ q.val)) := by
  change chainOfMask _ (reconX cols (maskOf _ (Pi.single q 1))) = _
  rw [maskOf_single]
  rfl

/-- The reconstructed packed mask is the sum of the columns on its support. -/
theorem reconX_eq_sum_maskSupport {n m : Nat} (cols : List (Nat × Nat))
    (s : Nat) (hs : s < 2 ^ n) :
    chainOfMask (Equiv.refl (Fin m)) (reconX cols s) =
      ∑ q ∈ maskSupport n s,
        chainOfMask (Equiv.refl (Fin m)) (reconX cols (2 ^ q.val)) := by
  have h := congrArg (reconLinear (Equiv.refl (Fin n)) (Equiv.refl (Fin m)) cols)
    (binary_eq_sum_support (chainOfMask (Equiv.refl (Fin n)) s))
  rw [map_sum] at h
  simp only [reconLinear_single] at h
  change chainOfMask _ (reconX cols (maskOf _ (chainOfMask _ s))) = _ at h
  rw [maskOf_chainOfMask _ hs] at h
  exact h

/-- Packed overflow counts the support outside a given shadow. -/
theorem maskSupport_sdiff_card {n : Nat} (s beta : Nat)
    (hs : s < 2 ^ n) (hb : beta < 2 ^ n) :
    ((maskSupport n s) \ maskSupport n beta).card =
      bitCount n (s &&& ((2 ^ n - 1) ^^^ beta)) := by
  have hset : maskSupport n s \ maskSupport n beta =
      Finset.univ.filter fun i : Fin n =>
        chainOfMask (Equiv.refl (Fin n)) s i ≠ 0 ∧
        chainOfMask (Equiv.refl (Fin n)) beta i = 0 := by
    ext i
    simp [maskSupport]
  rw [hset, off_support_card, maskOf_chainOfMask _ hs, maskOf_chainOfMask _ hb]

/-- Dual covers exclude a packed solution with bounded off-shadow support. -/
theorem no_recon_solution_of_dual_cover {n m : Nat} {J : Type*}
    (cols : List (Nat × Nat)) (rhs beta : Nat) (cap : Nat)
    (dual : J → (Fin m → ZMod 2) →+ ZMod 2)
    (hon : ∀ j q, q ∈ maskSupport n beta →
      dual j (chainOfMask (Equiv.refl (Fin m)) (reconX cols (2 ^ q.val))) = 0)
    (hcover : ∀ t : Finset (Fin n), Disjoint t (maskSupport n beta) → t.card ≤ cap →
      ∃ j, dual j (chainOfMask (Equiv.refl (Fin m)) rhs) = 1 ∧
        ∑ q ∈ t, dual j (chainOfMask (Equiv.refl (Fin m))
          (reconX cols (2 ^ q.val))) = 0)
    (s : Nat) (hs : s < 2 ^ n) (hb : beta < 2 ^ n)
    (hw : bitCount n (s &&& ((2 ^ n - 1) ^^^ beta)) ≤ cap) :
    reconX cols s ≠ rhs := by
  intro heq
  have h := no_solution_of_dual_cover
    (fun q : Fin n => chainOfMask (Equiv.refl (Fin m)) (reconX cols (2 ^ q.val)))
    (chainOfMask (Equiv.refl (Fin m)) rhs) (maskSupport n beta) cap dual hon hcover
    (maskSupport n s) (by rwa [maskSupport_sdiff_card s beta hs hb])
  apply h
  rw [← reconX_eq_sum_maskSupport cols s hs, heq]

/-- Empty and singleton dual tests cover every off-support subset of size at most one. -/
theorem dual_cover_cap_one {Q J M : Type*} [DecidableEq Q] [AddCommMonoid M]
    (cols : Q → M) (rhs : M) (support : Finset Q)
    (dual : J → M →+ ZMod 2)
    (hzero : ∃ j, dual j rhs = 1)
    (hsingle : ∀ q, q ∉ support → ∃ j, dual j rhs = 1 ∧ dual j (cols q) = 0) :
    ∀ t : Finset Q, Disjoint t support → t.card ≤ 1 →
      ∃ j, dual j rhs = 1 ∧ ∑ q ∈ t, dual j (cols q) = 0 := by
  intro t hd ht
  by_cases he : t = ∅
  · subst t
    obtain ⟨j, hj⟩ := hzero
    exact ⟨j, hj, by simp⟩
  · have hc : t.card = 1 := by
      have hn := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
      omega
    obtain ⟨q, rfl⟩ := Finset.card_eq_one.mp hc
    have hq : q ∉ support := by simpa using hd
    obtain ⟨j, hj, hc⟩ := hsingle q hq
    exact ⟨j, hj, by simpa using hc⟩


/-- Fast parity checks give a dual cover for overflow budgets zero and one. -/
theorem no_recon_solution_small_cap {n k l : Nat}
    (cols : List (Nat × Nat)) (rhs beta cap : Nat) (lambdas : Fin l → Nat)
    (hcap : cap ≤ 1)
    (hon : ∀ (j : Fin l) (q : Fin n), beta.testBit q.val = true →
      parityFold k (lambdas j &&& reconX cols (2 ^ q.val)) = 0)
    (hzero : ∃ j : Fin l, parityFold k (lambdas j &&& rhs) = 1)
    (hsingle : cap = 1 → ∀ q : Fin n, beta.testBit q.val = false →
      ∃ j : Fin l, parityFold k (lambdas j &&& rhs) = 1 ∧
        parityFold k (lambdas j &&& reconX cols (2 ^ q.val)) = 0)
    (s : Nat) (hs : s < 2 ^ n) (hb : beta < 2 ^ n)
    (hw : bitCount n (s &&& ((2 ^ n - 1) ^^^ beta)) ≤ cap) :
    reconX cols s ≠ rhs := by
  let dual : Fin l → (Fin (2 ^ k) → ZMod 2) →+ ZMod 2 :=
    fun j => dualOfMask (2 ^ k) (lambdas j)
  have hzero' : ∃ j : Fin l,
      dual j (chainOfMask (Equiv.refl (Fin (2 ^ k))) rhs) = 1 := by
    obtain ⟨j, hj⟩ := hzero
    refine ⟨j, ?_⟩
    change dualOfMask (2 ^ k) _ _ = _
    rw [dualOfMask_eq_parityFold, hj]
    rfl
  apply no_recon_solution_of_dual_cover cols rhs beta cap dual ?_ ?_ s hs hb hw
  · intro j q hq
    have hbit : beta.testBit q.val = true := by
      cases h : beta.testBit q.val
      · simp [maskSupport, chainOfMask, h] at hq
      · rfl
    change dualOfMask (2 ^ k) _ _ = _
    rw [dualOfMask_eq_parityFold, hon j q hbit]
    rfl
  · intro t hd ht
    by_cases hc : cap = 0
    · have hcard : t.card = 0 := by omega
      have he : t = ∅ := Finset.card_eq_zero.mp hcard
      obtain ⟨j, hj⟩ := hzero'
      exact ⟨j, hj, by simp only [he, Finset.sum_empty]⟩
    · have hc : cap = 1 := by omega
      apply dual_cover_cap_one _ _ _ dual hzero' ?_ t hd (by omega)
      intro q hq
      have hbit : beta.testBit q.val = false := by
        cases h : beta.testBit q.val
        · rfl
        · exact False.elim (hq (by simp [maskSupport, chainOfMask, h]))
      obtain ⟨j, hj, he⟩ := hsingle hc q hbit
      refine ⟨j, ?_, ?_⟩
      · change dualOfMask (2 ^ k) _ _ = _
        rw [dualOfMask_eq_parityFold, hj]
        rfl
      · change dualOfMask (2 ^ k) _ _ = _
        rw [dualOfMask_eq_parityFold, he]
        rfl

end Quantum.Stabilizer.Homological.F2Mask
