import QEC.Stabilizer.Framework.Homological.Certificate.ForestReconstruct
import QEC.Stabilizer.Framework.Homological.Certificate.SmallMaskPair
import QEC.Stabilizer.Framework.Homological.Certificate.MaskAdjoint
import QEC.Stabilizer.Framework.Homological.Certificate.ReconWindow

namespace Quantum.Stabilizer.Homological.F2Mask

/-- Explicit finite coordinates of a bounded binary row. -/
def rowCells (n row : Nat) : List Nat := (List.range n).filter fun q => row.testBit q

/-- Row coordinate lists have no duplicate entries. -/
theorem rowCells_nodup (n row : Nat) : (rowCells n row).Nodup :=
  List.nodup_range.filter _

/-- A bounded row's finite coordinate list contains exactly its set bits. -/
theorem mem_rowCells {n row : Nat} (hr : row < 2^n) (q : Nat) :
    q ∈ rowCells n row ↔ row.testBit q = true := by
  simp only [rowCells,List.mem_filter,List.mem_range]
  constructor
  · exact And.right
  · intro hq
    refine ⟨?_,hq⟩
    by_contra h
    have hf := Nat.testBit_lt_two_pow (hr.trans_le
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : n ≤ q)))
    simp [hq] at hf

/-- Explicit row evaluation is the binary parity of the packed intersection. -/
theorem cellEval_rowCells (n row value : Nat) :
    cellEval (rowCells n row) value = (bitCount n (row &&& value) : ZMod 2) := by
  induction n with
  | zero => simp [rowCells,cellEval,bitCount]
  | succ n ih =>
    rw [bitCount_succ,Nat.cast_add]
    simp only [rowCells,List.range_succ,List.filter_append,List.filter_cons,List.filter_nil,
      cellEval,List.map_append,List.sum_append] at *
    rw [ih]
    congr 1
    simp only [Nat.testBit_and]
    cases hr : row.testBit n <;> cases hv : value.testBit n <;> simp [hr,hv]

/-- Restricting a row to a mask preserves its evaluation on supported words. -/
theorem cellEval_restrict_support (n row beta value : Nat) (hs : value &&& beta = value) :
    cellEval (rowCells n (row &&& beta)) value = cellEval (rowCells n row) value := by
  rw [cellEval_rowCells,cellEval_rowCells]
  congr 2
  calc (row &&& beta) &&& value = row &&& (value &&& beta) := by ac_rfl
       _ = row &&& value := by rw [hs]

/-- A vanishing checked syndrome coordinate gives the corresponding row equation. -/
theorem cellEval_zero_of_adjoint (n : Nat) (E TE : List (Nat × Nat))
    (htranspose : ∀ (i j : Fin n),
      reconLinear (Equiv.refl (Fin n)) (Equiv.refl (Fin n)) TE (Pi.single j 1) i =
      reconLinear (Equiv.refl (Fin n)) (Equiv.refl (Fin n)) E (Pi.single i 1) j)
    (hEp : ∀ p ∈ E, p.1 < n) (hTEp : ∀ p ∈ TE, p.1 < n)
    (value row : Nat) (q : Fin n) (hrow : reconX TE (2^q.val) = row)
    (hz : (reconX E value).testBit q = false) :
    cellEval (rowCells n row) value = 0 := by
  have h := dualOfMask_apply_of_adjoint
    (reconLinear (Equiv.refl (Fin n)) (Equiv.refl (Fin n)) E)
    (reconLinear (Equiv.refl (Fin n)) (Equiv.refl (Fin n)) TE)
    htranspose (2^q.val) value row
    (by rw [reconLinear_chainOfMask _ _ _ hTEp,hrow])
  rw [reconLinear_chainOfMask _ _ _ hEp,dualOfMask_chainOfMask] at h
  rw [cellEval_rowCells,← h,Nat.and_comm,Nat.and_two_pow,hz]
  simp [bitCount_eq_card]

#print axioms cellEval_zero_of_adjoint
end Quantum.Stabilizer.Homological.F2Mask
