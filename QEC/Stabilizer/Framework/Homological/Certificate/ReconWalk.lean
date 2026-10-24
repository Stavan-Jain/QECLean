import QEC.Stabilizer.Framework.Homological.BZCertificate

namespace Quantum.Stabilizer.Homological.F2Mask

/-- A complete subset walk verifies every reconstruction from its row family. -/
theorem reconX_ok_of_full_walk (ok : Nat → Bool) (rows : List (Nat × Nat))
    (hz : ok 0 = true)
    (hw : xorWalk ok (rows.map Prod.snd) rows.length 0 = true)
    (coeff : Nat) : ok (reconX rows coeff) = true := by
  let selected := (rows.filter fun p => coeff.testBit p.1).map Prod.snd
  have hs : selected.Sublist (rows.map Prod.snd) :=
    (List.filter_sublist).map Prod.snd
  change ok (xorList selected) = true
  by_cases he : selected = []
  · simpa [he] using hz
  · have hlen : selected.length ≤ rows.length := by
      simpa only [List.length_map] using hs.length_le
    have h := xorWalk_sound hw hs he hlen
    simpa only [Nat.zero_xor] using h

/-- Taking a fixed bit mask commutes with XOR reconstruction. -/
theorem reconX_and (rows : List (Nat × Nat)) (coeff mask : Nat) :
    reconX rows coeff &&& mask =
      reconX (rows.map fun p => (p.1, p.2 &&& mask)) coeff := by
  induction rows with
  | nil => simp [reconX]
  | cons p ps ih =>
    simp only [reconX] at ih
    simp only [reconX, List.filter_cons, List.map_cons]
    cases h : coeff.testBit p.1 <;> simp [h, xorList_cons, ih, Nat.and_xor_distrib_right]

/-- Right shifts commute with XOR reconstruction. -/
theorem reconX_shiftRight (rows : List (Nat × Nat)) (coeff shift : Nat) :
    reconX rows coeff >>> shift =
      reconX (rows.map fun p => (p.1, p.2 >>> shift)) coeff := by
  induction rows with
  | nil => simp [reconX]
  | cons p ps ih =>
    simp only [reconX] at ih
    simp only [reconX, List.filter_cons, List.map_cons]
    cases h : coeff.testBit p.1 <;> simp [h, xorList_cons, ih, Nat.shiftRight_xor_distrib]

#print axioms reconX_ok_of_full_walk
end Quantum.Stabilizer.Homological.F2Mask
