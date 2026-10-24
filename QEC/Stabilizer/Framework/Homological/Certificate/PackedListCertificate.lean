import QEC.Stabilizer.Framework.Homological.Certificate.BatchLinear

namespace PackedDigits
open Quantum.Stabilizer.Homological.F2Mask

/-- Pack an explicit short list without any indexed lookups during evaluation. -/
def packList (width : Nat) (values : List Nat) : Nat := Nat.ofDigits (2^width) values

/-- Packing list entries agrees with the functional packed-table specification. -/
theorem packList_eq_packF (width : Nat) (values : List Nat) :
    packList width values = packF width values.length (fun i => values.getD i 0) := by
  unfold packList packF
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range]
    exact (List.getD_eq_getElem _ _ hi).symm

/-- A checked parallel map of an explicit list proves each listed reconstruction. -/
theorem reconstruction_list_sound (width : Nat) (pairs : List (Nat × Nat))
    (hw : 0 < width) (hpair : ∀ p ∈ pairs, p.1 < 2^width ∧ p.2 < 2^width)
    (rows : List (Nat × Nat)) (hr : ∀ p ∈ rows,p.1 < width ∧ p.2 < 2^width)
    (hcheck : batchRecon (packList width (pairs.map fun _ => 1))
      (packList width (pairs.map Prod.fst)) rows = packList width (pairs.map Prod.snd)) :
    ∀ p ∈ pairs, reconX rows p.1 = p.2 := by
  have hone : packList width (pairs.map fun _ => 1) = packF width pairs.length (fun _ => 1) := by
    unfold packList packF
    congr 1
    simp
  rw [hone,packList_eq_packF,packList_eq_packF] at hcheck
  simp only [List.length_map] at hcheck
  have hc : ∀ i < pairs.length, (pairs.map Prod.fst).getD i 0 < 2^width := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by simpa)]
    simp only [List.getElem_map]
    exact (hpair _ (List.getElem_mem hi)).1
  rw [batchRecon_packF _ _ _ hw hc rows hr] at hcheck
  intro p hp
  obtain ⟨i,hi,hp⟩ := List.getElem_of_mem hp
  have he := congrArg (lane width i) hcheck
  rw [lane_packF _ _ _ _ (fun j hj => reconX_lt rows _ width (fun q hq => (hr q hq).2)),
    lane_packF _ _ _ _ (by
      intro j hj
      rw [List.getD_eq_getElem _ _ (by simpa)]
      simp only [List.getElem_map]
      exact (hpair _ (List.getElem_mem hj)).2),if_pos hi,if_pos hi] at he
  rw [List.getD_eq_getElem _ _ (show i < (pairs.map Prod.fst).length by simpa),
    List.getD_eq_getElem _ _ (show i < (pairs.map Prod.snd).length by simpa)] at he
  simpa only [List.getElem_map,hp] using he


#print axioms reconstruction_list_sound
end PackedDigits
