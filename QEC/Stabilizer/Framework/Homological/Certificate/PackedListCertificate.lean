import QEC.Stabilizer.Framework.Homological.Certificate.BatchLinear

/-!
# Packed certificates given as explicit lists

`packList width values` packs an explicit list into lanes of `width` bits by
shifts alone, which the kernel evaluates without indexed lookups or
multiplications by a large base. It agrees with the digit expansion
(`packList_eq_ofDigits`) and with the table packing `packF`
(`packList_eq_packF`).

`reconstruction_list_sound` turns one batch reconstruction check on packed
lists of inputs and expected outputs into the statement that the window
reconstruction `F2Mask.reconX` maps every listed input to its listed output.
-/

namespace PackedDigits
open Quantum.Stabilizer.Homological.F2Mask

/-- Pack an explicit list by shifts, without indexed lookups or multiplication
by a large base. -/
def packList (width : Nat) : List Nat → Nat
  | [] => 0
  | value :: rest => value + (packList width rest <<< width)

/-- Shift-based packing agrees with the base-power digit representation. -/
lemma packList_eq_ofDigits (width : Nat) (values : List Nat) :
    packList width values = Nat.ofDigits (2 ^ width) values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    change value + (packList width rest <<< width) =
      value + 2 ^ width * Nat.ofDigits (2 ^ width) rest
    rw [ih, Nat.shiftLeft_eq, Nat.mul_comm]

/-- Packing list entries agrees with the functional packed-table
specification. -/
theorem packList_eq_packF (width : Nat) (values : List Nat) :
    packList width values = packF width values.length (fun i => values.getD i 0) := by
  rw [packList_eq_ofDigits, packF]
  congr 1
  refine List.ext_getElem (by simp) fun i hi _ => ?_
  simp only [List.getElem_map, List.getElem_range]
  exact (List.getD_eq_getElem _ _ hi).symm

/-- A checked parallel map of an explicit list proves each listed
reconstruction: if the batch reconstruction of the packed first components is
the packed list of second components, then `reconX rows p.1 = p.2` for every
listed pair `p`. -/
theorem reconstruction_list_sound (width : Nat) (pairs : List (Nat × Nat))
    (hw : 0 < width) (hpair : ∀ p ∈ pairs, p.1 < 2 ^ width ∧ p.2 < 2 ^ width)
    (rows : List (Nat × Nat)) (hr : ∀ p ∈ rows, p.1 < width ∧ p.2 < 2 ^ width)
    (hcheck : batchRecon (packList width (pairs.map fun _ => 1))
      (packList width (pairs.map Prod.fst)) rows = packList width (pairs.map Prod.snd)) :
    ∀ p ∈ pairs, reconX rows p.1 = p.2 := by
  have hone : packList width (pairs.map fun _ => 1) = packF width pairs.length (fun _ => 1) := by
    rw [packList_eq_ofDigits, packF]
    congr 1
    simp
  have hfst : ∀ i < pairs.length, (pairs.map Prod.fst).getD i 0 < 2 ^ width := fun i hi => by
    simpa [hi] using (hpair _ (List.getElem_mem hi)).1
  have hsnd : ∀ i < pairs.length, (pairs.map Prod.snd).getD i 0 < 2 ^ width := fun i hi => by
    simpa [hi] using (hpair _ (List.getElem_mem hi)).2
  rw [hone, packList_eq_packF, packList_eq_packF] at hcheck
  simp only [List.length_map] at hcheck
  rw [batchRecon_packF _ _ _ hw hfst rows hr] at hcheck
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  have he := congrArg (lane width i) hcheck
  rw [lane_packF _ _ _ _ (fun j _ => reconX_lt rows _ width fun q hq => (hr q hq).2),
    lane_packF _ _ _ _ hsnd, if_pos hi, if_pos hi] at he
  simpa [hi] using he

end PackedDigits
