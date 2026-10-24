import QEC.Stabilizer.Framework.Homological.BBSmallCycle
import QEC.Stabilizer.Framework.Homological.BBDoubling
import QEC.Stabilizer.Framework.Homological.Certificate.MaskLinear

open scoped BigOperators

namespace Quantum.Stabilizer.Homological.BB.XDoubleCoverData

variable {G H : Type}
  [Fintype G] [AddCommGroup G] [DecidableEq G]
  [Fintype H] [AddCommGroup H] [DecidableEq H]
  (D : XDoubleCoverData G H)

/-- The two sheet restrictions sum to the whole pushforward as a chain. -/
theorem sheets_add_eq_push (v : G × Fin 2 → ZMod 2) :
    D.sheet0 v + D.sheet1 v = D.push1 v := by
  funext i
  exact D.sheet0_add_sheet1 v i

/-- Pushforward sends a point mass to the point mass of its projected qubit. -/
theorem push1_single (q : G × Fin 2) :
    D.push1 (Pi.single q 1) = Pi.single (D.proj q.1, q.2) 1 := by
  funext j
  change (∑ i : G × Fin 2, if (D.proj i.1, i.2) = j then (Pi.single q 1) i else 0) = _
  rw [Finset.sum_eq_single q]
  · simp only [Pi.single_eq_same, Pi.single_apply]
    by_cases h : (D.proj q.1, q.2) = j
    · simp [h]
    · simp [h, Ne.symm h]
  · intro i hi hne
    simp [Pi.single_eq_of_ne hne]
  · intro h
    exact False.elim (h (Finset.mem_univ q))

/-- Restricting a point mass to sheet zero either keeps its projection or gives zero. -/
theorem sheet0_single (q : G × Fin 2) :
    D.sheet0 (Pi.single q 1) =
      if D.sec (D.proj q.1) = q.1 then Pi.single (D.proj q.1, q.2) 1 else 0 := by
  by_cases hq : D.sec (D.proj q.1) = q.1
  · rw [if_pos hq]
    funext j
    have heq : D.sec1 j = q ↔ j = (D.proj q.1, q.2) := by
      constructor
      · intro h
        have hp := congrArg (Prod.map D.proj id) h
        simpa only [D.proj_prodMap_sec1] using hp
      · intro h
        subst j
        exact Prod.ext hq rfl
    simp only [sheet0, Pi.single_apply]
    simp only [heq]
  · rw [if_neg hq]
    funext j
    have hne : D.sec1 j ≠ q := by
      intro h
      have hp := congrArg (Prod.map D.proj id) h
      rw [D.proj_prodMap_sec1] at hp
      have hj : j = (D.proj q.1, q.2) := hp
      apply hq
      rw [hj] at h
      exact congrArg Prod.fst h
    simp [sheet0, Pi.single_apply, hne]

/-- In certificate coordinates a restricted point mass is either one bit or zero. -/
theorem maskOf_sheet0_single {n : Nat} (e : (H × Fin 2) ≃ Fin n)
    (q : G × Fin 2) :
    F2Mask.maskOf e (D.sheet0 (Pi.single q 1)) =
      if D.sec (D.proj q.1) = q.1 then 2 ^ (e (D.proj q.1, q.2)).val else 0 := by
  rw [D.sheet0_single]
  split_ifs <;> simp only [F2Mask.maskOf_single, F2Mask.maskOf_zero]

/-- A sparse identity checked on point masses gives the carry equation of every cycle. -/
theorem sheet_equation_of_basis
    (E R : (H × Fin 2 → ZMod 2) →ₗ[ZMod 2] (G → ZMod 2))
    (hbasis : ∀ q : G × Fin 2,
      E (D.sheet0 (Pi.single q 1)) +
          R (D.sheet0 (Pi.single q 1) + D.sheet1 (Pi.single q 1)) =
        fun h => SmallCycle.termAt D.Ac D.Bc q h)
    {v : G × Fin 2 → ZMod 2} (hv : v ∈ D.coverComplex.cycles) :
    E (D.sheet0 v) = R (D.push1 v) := by
  have hfull : ∀ w : G × Fin 2 → ZMod 2,
      E (D.sheet0 w) + R (D.sheet0 w + D.sheet1 w) = D.coverComplex.boundary1 w := by
    apply funLiftF2
    · change E 0 + R (0 + 0) = 0
      simp
    · exact map_zero _
    · intro a b
      simp only [sheet0_add, sheet1_add, map_add]
      abel
    · intro a b
      exact map_add _ a b
    · intro q
      rw [hbasis]
      funext h
      exact (SmallCycle.bbBoundary1Fn_single_point D.Ac D.Bc q h).symm
  have h := hfull v
  rw [D.sheets_add_eq_push, show D.coverComplex.boundary1 v = 0 from hv] at h
  funext i
  have key : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  exact key _ _ (congrFun h i)

end Quantum.Stabilizer.Homological.BB.XDoubleCoverData

namespace Quantum.Stabilizer.Homological.F2Mask

/-- Restricting one chain to the zero coordinates of another is a bounded mask difference. -/
theorem maskOf_restrict_zero {ι : Type} {n : Nat} (e : ι ≃ Fin n)
    (a b : ι → ZMod 2) :
    maskOf e (fun i => if b i = 0 then a i else 0) =
      maskOf e a &&& ((2 ^ n - 1) ^^^ maskOf e b) := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
    testBit_maskOf]
  by_cases hk : k < n
  · simp only [dif_pos hk]
    by_cases hb : b (e.symm ⟨k, hk⟩) = 0 <;> simp [hb, hk]
  · simp [hk]

/-- A zero off-shadow mask proves containment of the corresponding supports. -/
theorem support_subset_of_mask_restrict_zero {ι : Type} {n : Nat} (e : ι ≃ Fin n)
    (a b : ι → ZMod 2)
    (h : maskOf e a &&& ((2 ^ n - 1) ^^^ maskOf e b) = 0) :
    ∀ i, a i ≠ 0 → b i ≠ 0 := by
  rw [← maskOf_restrict_zero] at h
  have hz : (fun i => if b i = 0 then a i else 0) = 0 :=
    maskOf_injective e (h.trans (maskOf_zero e).symm)
  intro i ha hb
  have hi := congrFun hz i
  simp only [hb, if_true, Pi.zero_apply] at hi
  exact ha hi

/-- The off-shadow bit count is the cardinality of the off-shadow chain support. -/
theorem off_support_card {ι : Type} [Fintype ι] {n : Nat} (e : ι ≃ Fin n)
    (a b : ι → ZMod 2) :
    (Finset.univ.filter fun i => a i ≠ 0 ∧ b i = 0).card =
      bitCount n (maskOf e a &&& ((2 ^ n - 1) ^^^ maskOf e b)) := by
  rw [← maskOf_restrict_zero, ← card_support_eq_bitCount]
  congr 1
  ext i
  by_cases hb : b i = 0 <;> simp [hb]

end Quantum.Stabilizer.Homological.F2Mask

namespace Quantum.Stabilizer.Homological.BB.XDoubleCoverData

variable {G H : Type}
  [Fintype G] [AddCommGroup G] [DecidableEq G]
  [Fintype H] [AddCommGroup H] [DecidableEq H]
  (D : XDoubleCoverData G H)

/-- The sheet weight identity expressed entirely in packed certificate coordinates. -/
theorem weight_eq_mask_shadow_overflow {n : Nat} (e : (H × Fin 2) ≃ Fin n)
    (v : G × Fin 2 → ZMod 2) :
    D.coverComplex.chainWeight v =
      F2Mask.bitCount n (F2Mask.maskOf e (D.push1 v)) +
        2 * F2Mask.bitCount n (F2Mask.maskOf e (D.sheet0 v) &&&
          ((2 ^ n - 1) ^^^ F2Mask.maskOf e (D.push1 v))) := by
  rw [D.chainWeight_sheet_eq, D.baseComplex_chainWeight_eq,
    F2Mask.card_support_eq_bitCount e, F2Mask.off_support_card e]

/-- A total weight bound gives the precise off-shadow budget used by lift certificates. -/
theorem mask_overflow_le {n limit : Nat} (e : (H × Fin 2) ≃ Fin n)
    (v : G × Fin 2 → ZMod 2) (hv : D.coverComplex.chainWeight v ≤ limit) :
    F2Mask.bitCount n (F2Mask.maskOf e (D.sheet0 v) &&&
      ((2 ^ n - 1) ^^^ F2Mask.maskOf e (D.push1 v))) ≤
        (limit - F2Mask.bitCount n (F2Mask.maskOf e (D.push1 v))) / 2 := by
  rw [D.weight_eq_mask_shadow_overflow e] at hv
  omega

end Quantum.Stabilizer.Homological.BB.XDoubleCoverData
