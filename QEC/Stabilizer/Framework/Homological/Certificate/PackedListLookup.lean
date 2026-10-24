import QEC.Stabilizer.Framework.Homological.Certificate.BatchListBinary

namespace PackedDigits

/-- A checked packed field cache returns the field of each existing list record. -/
theorem getD_field_eq_lane {α : Type*} (width : Nat) (xs : List α)
    (field : α → Nat) (fallback : α) (packed : Nat)
    (hbound : ∀ x ∈ xs, field x < 2^width)
    (hpacked : packList width (xs.map field) = packed)
    (i : Nat) (hi : i < xs.length) :
    field (xs.getD i fallback) = lane width i packed := by
  have hm : ∀ x ∈ xs.map field, x < 2^width := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    exact hbound a ha
  rw [List.getD_eq_getElem _ _ hi, ← hpacked,
    lane_packList width (xs.map field) hm i (by simpa only [List.length_map] using hi)]
  simp only [List.getElem_map]

#print axioms getD_field_eq_lane
end PackedDigits
