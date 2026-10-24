import QEC.Stabilizer.Framework.Homological.Certificate.MaskFiber

namespace Quantum.Stabilizer.Homological.BB.XDoubleCoverData
open F2Mask
variable {G H : Type} [Fintype G] [AddCommGroup G] [DecidableEq G]
  [Fintype H] [AddCommGroup H] [DecidableEq H]
  (D : XDoubleCoverData G H)

/-- The first sheet of a sparse chain is computed from its surviving point masses. -/
theorem maskOf_sheet0_sum_points {n : Nat} (e : (H × Fin 2) ≃ Fin n)
    (qs : List (G × Fin 2)) :
    maskOf e (D.sheet0 ((qs.map (fun q => Pi.single q (1 : ZMod 2))).sum)) =
      xorList (qs.map fun q => if D.sec (D.proj q.1) = q.1 then
        2 ^ (e (D.proj q.1, q.2)).val else 0) := by
  induction qs with
  | nil =>
      simp only [List.map_nil, List.sum_nil, xorList_nil]
      exact maskOf_zero e
  | cons q qs ih =>
      rw [List.map_cons, List.sum_cons, D.sheet0_add, maskOf_add,
        D.maskOf_sheet0_single, ih, List.map_cons, xorList_cons]

/-- The projection of a sparse chain is computed from its projected point masses. -/
theorem maskOf_push1_sum_points {n : Nat} (e : (H × Fin 2) ≃ Fin n)
    (qs : List (G × Fin 2)) :
    maskOf e (D.push1 ((qs.map (fun q => Pi.single q (1 : ZMod 2))).sum)) =
      xorList (qs.map fun q => 2 ^ (e (D.proj q.1, q.2)).val) := by
  induction qs with
  | nil => simp only [List.map_nil, List.sum_nil, map_zero, maskOf_zero, xorList_nil]
  | cons q qs ih =>
      rw [List.map_cons, List.sum_cons, map_add, maskOf_add,
        D.push1_single, maskOf_single, ih, List.map_cons, xorList_cons]

end Quantum.Stabilizer.Homological.BB.XDoubleCoverData
