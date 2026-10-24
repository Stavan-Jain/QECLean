import QEC.Stabilizer.Framework.Homological.Certificate.PackedListCertificate
import QEC.Stabilizer.Framework.Homological.Certificate.BatchReconLane
namespace PackedDigits
open Quantum.Stabilizer.Homological.F2Mask

/-- A short list of bounded digits forms a bounded packed integer. -/
theorem packList_lt (width : Nat) (xs : List Nat) (hw : 0 < width)
    (hx : ∀ x ∈ xs, x < 2^width) : packList width xs < 2^(width*xs.length) := by
  rw [packList_eq_packF]
  apply packF_lt _ _ _ hw
  intro i hi
  rw [List.getD_eq_getElem _ _ hi]
  exact hx _ (List.getElem_mem hi)

/-- Reading an existing lane of a packed list returns its corresponding entry. -/
theorem lane_packList (width : Nat) (xs : List Nat) (hx : ∀ x ∈ xs, x < 2^width)
    (i : Nat) (hi : i < xs.length) : lane width i (packList width xs) = xs[i] := by
  rw [packList_eq_packF,lane_packF _ _ _ _ (by
    intro j hj
    rw [List.getD_eq_getElem _ _ hj]
    exact hx _ (List.getElem_mem hj)),if_pos hi,List.getD_eq_getElem _ _ hi]

/-- Two parallel maps on the same list certify the XOR of their images pointwise. -/
theorem binary_reconstruction_list_sound {α : Type*} (width : Nat) (xs : List α)
    (f g output : α → Nat) (hw : 0 < width)
    (hf : ∀ x ∈ xs, f x < 2^width) (hg : ∀ x ∈ xs, g x < 2^width)
    (ho : ∀ x ∈ xs, output x < 2^width)
    (left right : List (Nat × Nat))
    (hl : ∀ p ∈ left, p.1 < width ∧ p.2 < 2^width)
    (hr : ∀ p ∈ right, p.1 < width ∧ p.2 < 2^width)
    (hcheck : batchRecon (packList width (xs.map fun _ => 1)) (packList width (xs.map f)) left ^^^
      batchRecon (packList width (xs.map fun _ => 1)) (packList width (xs.map g)) right =
      packList width (xs.map output)) :
    ∀ x ∈ xs, reconX left (f x) ^^^ reconX right (g x) = output x := by
  have hone : packList width (xs.map fun _ => 1) = packF width xs.length (fun _ => 1) := by
    unfold packList packF
    congr 1
    simp
  have hfm : ∀ y ∈ xs.map f, y < 2^width := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
    exact hf x hx
  have hgm : ∀ y ∈ xs.map g, y < 2^width := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
    exact hg x hx
  have hom : ∀ y ∈ xs.map output, y < 2^width := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
    exact ho x hx
  have hfb : packList width (xs.map f) < 2^(width*xs.length) := by
    simpa only [List.length_map] using packList_lt width _ hw hfm
  have hgb : packList width (xs.map g) < 2^(width*xs.length) := by
    simpa only [List.length_map] using packList_lt width _ hw hgm
  rw [hone] at hcheck
  intro x hx
  obtain ⟨i,hi,hxi⟩ := List.getElem_of_mem hx
  have he := congrArg (lane width i) hcheck
  rw [lane_xor,batchRecon_lane _ _ _ hw hfb left hl i hi,
    batchRecon_lane _ _ _ hw hgb right hr i hi,
    lane_packList _ _ hfm i (by simpa),lane_packList _ _ hgm i (by simpa),
    lane_packList _ _ hom i (by simpa)] at he
  simpa only [List.getElem_map,hxi] using he

#print axioms binary_reconstruction_list_sound
end PackedDigits
