import QEC.Stabilizer.Framework.Homological.Certificate.MaskFiber

namespace Quantum.Stabilizer.Homological.BB.XDoubleCoverData
open F2Mask

variable {G H : Type}
  [Fintype G] [AddCommGroup G] [DecidableEq G]
  [Fintype H] [AddCommGroup H] [DecidableEq H]
  (D : XDoubleCoverData G H)

/-- The second sheet is the first sheet plus the shadow. -/
theorem sheet1_eq_sheet0_add_push (v : G × Fin 2 → ZMod 2) :
    D.sheet1 v = D.sheet0 v + D.push1 v := by
  rw [← D.sheets_add_eq_push]
  funext q
  simp only [Pi.add_apply, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-- A cover chain is determined by its first sheet and its shadow. -/
theorem eq_of_sheet0_push_eq {u v : G × Fin 2 → ZMod 2}
    (h0 : D.sheet0 u = D.sheet0 v) (hp : D.push1 u = D.push1 v) : u = v := by
  have hz : D.push1 (u + v) = 0 := by
    rw [map_add, hp]
    funext q
    exact CharTwo.add_self_eq_zero _
  obtain ⟨w, hw⟩ := (D.push1_eq_zero_iff (u + v)).mp hz
  have hw0 : w = 0 := by
    have hh := congrArg D.sheet0 hw
    rw [D.sheet0_add, D.sheet0_pull1, h0] at hh
    funext q
    have h := congrFun hh q
    simpa only [Pi.add_apply, CharTwo.add_self_eq_zero] using h.symm
  rw [hw0, map_zero] at hw
  funext q
  have key : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  exact key _ _ (congrFun hw q)

/-- Sparse sheet-embedding columns reconstruct every cover mask from its two sheets. -/
theorem maskOf_eq_join_of_basis {n m : Nat}
    (e : (H × Fin 2) ≃ Fin n) (f : (G × Fin 2) ≃ Fin m)
    (left right : List (Nat × Nat))
    (hl : ∀ p ∈ left, p.2 < 2 ^ m) (hr : ∀ p ∈ right, p.2 < 2 ^ m)
    (hbasis : ∀ q : G × Fin 2,
      (reconX left (maskOf e (D.sheet0 (Pi.single q 1)))) ^^^
        reconX right (maskOf e (D.sheet1 (Pi.single q 1))) = 2 ^ (f q).val)
    (v : G × Fin 2 → ZMod 2) :
    maskOf f v =
      (reconX left (maskOf e (D.sheet0 v))) ^^^
        reconX right ((maskOf e (D.sheet0 v)) ^^^ maskOf e (D.push1 v)) := by
  have hfull : ∀ w : G × Fin 2 → ZMod 2,
      reconLinear e f left (D.sheet0 w) + reconLinear e f right (D.sheet1 w) = w := by
    apply funLiftF2
    · change reconLinear e f left 0 + reconLinear e f right 0 = 0
      simp
    · rfl
    · intro a b
      rw [D.sheet0_add, D.sheet1_add, map_add, map_add]
      abel
    · intro a b
      rfl
    · intro q
      apply maskOf_injective f
      rw [maskOf_add, maskOf_reconLinear _ _ _ _ hl,
        maskOf_reconLinear _ _ _ _ hr, maskOf_single]
      exact hbasis q
  have h := congrArg (maskOf f) (hfull v)
  rw [maskOf_add, maskOf_reconLinear _ _ _ _ hl,
    maskOf_reconLinear _ _ _ _ hr, D.sheet1_eq_sheet0_add_push, maskOf_add] at h
  exact h.symm

end Quantum.Stabilizer.Homological.BB.XDoubleCoverData
