import QEC.Stabilizer.Codes.Color.Code
import QEC.Stabilizer.Framework.Homological.Distance

/-!
# Face-spin coordinates for triangular color-code logical chains

A face-check combination is evaluated by adding the incident face labels.
The formulas below express these local values in the three-row layer
enumeration, with missing boundary labels set to zero.
-/

namespace Quantum.StabilizerGroup.ColorCode

open scoped BigOperators
open Stabilizer.Homological

/-- A face label, extended by zero beyond the finite triangular patch. -/
def faceBit {r : ℕ} (a : Face r → ZMod 2) (k : Fin 3) (l j : ℕ) : ZMod 2 :=
  if hl : l < r then
    if hj : j < l + 1 then a (k, ⟨⟨l, hl⟩, ⟨j, hj⟩⟩) else 0
  else 0

/-- Face labels vanish beyond the last layer. -/
@[simp] theorem faceBit_of_layer_ge {r : ℕ} (a : Face r → ZMod 2)
    (k : Fin 3) (l j : ℕ) (h : r ≤ l) : faceBit a k l j = 0 := by
  simp [faceBit, show ¬l < r from by omega]

/-- Face labels vanish beyond the last position of their triangular row. -/
@[simp] theorem faceBit_of_column_ge {r : ℕ} (a : Face r → ZMod 2)
    (k : Fin 3) (l j : ℕ) (h : l + 1 ≤ j) : faceBit a k l j = 0 := by
  simp [faceBit, show ¬j < l + 1 from by omega]

/-- A zero-extended face label is a sum selecting its unique finite index. -/
private theorem faceBit_eq_sum {r : ℕ} (a : Face r → ZMod 2)
    (k : Fin 3) (l j : ℕ) :
    faceBit a k l j =
      ∑ f : FaceRow r, if f.1.val = l ∧ f.2.val = j then a (k, f) else 0 := by
  classical
  by_cases hl : l < r
  · by_cases hj : j < l + 1
    · let f : FaceRow r := ⟨⟨l, hl⟩, ⟨j, hj⟩⟩
      have hsingle : (∑ g : FaceRow r,
          if g.1.val = l ∧ g.2.val = j then a (k, g) else 0) = a (k, f) := by
        rw [Finset.sum_eq_single f]
        · simp [f]
        · intro g _ hgf
          have hnot : ¬(g.1.val = l ∧ g.2.val = j) := by
            intro h
            apply hgf
            rcases g with ⟨s, t⟩
            have hs : s = ⟨l, hl⟩ := Fin.ext h.1
            subst s
            have ht : t = ⟨j, hj⟩ := Fin.ext h.2
            subst t
            rfl
          simp [hnot]
        · intro h
          exact (h (Finset.mem_univ f)).elim
      rw [hsingle]
      simp [faceBit, hl, hj, f]
    · rw [faceBit, dif_pos hl, dif_neg hj]
      symm
      apply Finset.sum_eq_zero
      intro f _
      have hnot : ¬(f.1.val = l ∧ f.2.val = j) := by
        have hcol := f.2.isLt
        omega
      simp [hnot]
  · rw [faceBit, dif_neg hl]
    symm
    apply Finset.sum_eq_zero
    intro f _
    have hnot : ¬(f.1.val = l ∧ f.2.val = j) := by
      have hrow := f.1.isLt
      omega
    simp [hnot]

/-- The contribution from one of the three colors of faces at a site. -/
def faceClassSum {r : ℕ} (a : Face r → ZMod 2) (k : Fin 3) (p : Coord) : ZMod 2 :=
  ∑ f : FaceRow r, if Adjacent (faceCoord (k, f)) p then a (k, f) else 0

/-- Classifying the unique neighboring face evaluates a single-color sum. -/
private theorem faceClassSum_eq_faceBit {r : ℕ} (a : Face r → ZMod 2)
    (k : Fin 3) (p : Coord) (l j : ℕ)
    (h : ∀ f : FaceRow r, Adjacent (faceCoord (k, f)) p ↔
      f.1.val = l ∧ f.2.val = j) :
    faceClassSum a k p = faceBit a k l j := by
  rw [faceBit_eq_sum]
  apply Finset.sum_congr rfl
  intro f _
  simp only [h f]

/-- A boundary guard omits a neighboring face outside the lattice. -/
private theorem faceClassSum_eq_guard {r : ℕ} (a : Face r → ZMod 2)
    (k : Fin 3) (p : Coord) (l j : ℕ) (P : Prop) [Decidable P]
    (h : ∀ f : FaceRow r, Adjacent (faceCoord (k, f)) p ↔
      P ∧ f.1.val = l ∧ f.2.val = j) :
    faceClassSum a k p = if P then faceBit a k l j else 0 := by
  by_cases hP : P
  · rw [if_pos hP]
    apply faceClassSum_eq_faceBit
    intro f
    simpa only [hP, true_and] using h f
  · rw [if_neg hP]
    apply Finset.sum_eq_zero
    intro f _
    simp only [h f, hP, false_and, if_false]

/-- A color absent from a site's neighborhood contributes no face labels. -/
private theorem faceClassSum_zero {r : ℕ} (a : Face r → ZMod 2)
    (k : Fin 3) (p : Coord)
    (h : ∀ f : FaceRow r, ¬Adjacent (faceCoord (k, f)) p) :
    faceClassSum a k p = 0 := by
  apply Finset.sum_eq_zero
  intro f _
  simp only [h f, if_false]

/-- The odd logical coset evaluated at a lattice coordinate. -/
def spinAt {r : ℕ} (a : Face r → ZMod 2) (p : Coord) : ZMod 2 :=
  1 + ∑ k : Fin 3, faceClassSum a k p

/-- Local face-spin evaluation agrees with the binary check combination. -/
theorem spinAt_qubitCoord {r : ℕ} (a : Face r → ZMod 2) (q : Qubit r) :
    spinAt a (qubitCoord q) = 1 + SelfDual.checkCombination (@incidence r) a q := by
  unfold spinAt
  congr 1
  change (∑ k : Fin 3, ∑ f : FaceRow r,
    if Adjacent (faceCoord (k, f)) (qubitCoord q) then a (k, f) else 0) =
      ∑ f : Face r, a f * incidence f q
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro f _
  simp only [incidence, mem_faceSupport]
  split_ifs <;> simp

/-- The apex meets only the first face in the first row. -/
theorem spinAt_apex {r : ℕ} (a : Face r → ZMod 2) :
    spinAt a (0, 0) =
      1 + faceBit a 0 0 0 := by
  have h0 : faceClassSum a 0 (0, 0) = faceBit a 0 0 0 := by
    apply faceClassSum_eq_faceBit
    rintro ⟨s, t⟩
    norm_num [faceCoord, Adjacent]
  have h1 : faceClassSum a 1 (0, 0) = 0 := by
    apply faceClassSum_zero
    rintro ⟨s, t⟩
    norm_num [faceCoord, Adjacent]
  have h2 : faceClassSum a 2 (0, 0) = 0 := by
    apply faceClassSum_zero
    rintro ⟨s, t⟩
    norm_num [faceCoord, Adjacent]
  simp only [spinAt, Fin.sum_univ_three, h0, h1, h2]
  ring

/-- The leftmost site of the first row meets its first two face colors. -/
theorem spinAt_a0 {r : ℕ} (a : Face r → ZMod 2) (l : ℕ) :
    spinAt a (3 * l + 1, 0) =
      1 + faceBit a 0 l 0 + faceBit a 1 l 0 := by
  have h0 : faceClassSum a 0 (3 * l + 1, 0) = faceBit a 0 l 0 := by
    apply faceClassSum_eq_faceBit
    rintro ⟨s, t⟩
    norm_num [faceCoord, Adjacent]
    omega
  have h1 : faceClassSum a 1 (3 * l + 1, 0) = faceBit a 1 l 0 := by
    apply faceClassSum_eq_faceBit
    rintro ⟨s, t⟩
    norm_num [faceCoord, Adjacent]
    omega
  have h2 : faceClassSum a 2 (3 * l + 1, 0) = 0 := by
    apply faceClassSum_zero
    rintro ⟨s, t⟩
    norm_num [faceCoord, Adjacent]
  simp only [spinAt, Fin.sum_univ_three, h0, h1, h2]
  ring

/-- An odd site in the first row also meets a face in the previous layer. -/
theorem spinAt_a_odd {r : ℕ} (a : Face r → ZMod 2) (l j : ℕ) :
    spinAt a (3 * l + 1, 3 * j + 2) =
      1 + (if l = 0 then 0 else faceBit a 2 (l - 1) j) +
        faceBit a 0 l j + faceBit a 1 l (j + 1) := by
  have h0 : faceClassSum a 0 (3 * l + 1, 3 * j + 2) = faceBit a 0 l j := by
    apply faceClassSum_eq_faceBit
    rintro ⟨s, t⟩
    norm_num [faceCoord, Adjacent]
    omega
  have h1 : faceClassSum a 1 (3 * l + 1, 3 * j + 2) = faceBit a 1 l (j + 1) := by
    apply faceClassSum_eq_faceBit
    rintro ⟨s, t⟩
    norm_num [faceCoord, Adjacent]
    omega
  have h2 : faceClassSum a 2 (3 * l + 1, 3 * j + 2) =
      if l = 0 then 0 else faceBit a 2 (l - 1) j := by
    have h := faceClassSum_eq_guard a 2 (3 * l + 1, 3 * j + 2) (l - 1) j (l ≠ 0) (by
      rintro ⟨s, t⟩
      norm_num [faceCoord, Adjacent]
      omega)
    simpa only [ne_eq, ite_not] using h
  simp only [spinAt, Fin.sum_univ_three, h0, h1, h2]
  ring

/-- The next even site shares the previous-layer face with its odd neighbor. -/
theorem spinAt_a_even_succ {r : ℕ} (a : Face r → ZMod 2) (l j : ℕ) :
    spinAt a (3 * l + 1, 3 * j + 3) =
      1 + (if l = 0 then 0 else faceBit a 2 (l - 1) j) +
        faceBit a 0 l (j + 1) + faceBit a 1 l (j + 1) := by
  have h0 : faceClassSum a 0 (3 * l + 1, 3 * j + 3) = faceBit a 0 l (j + 1) := by
    apply faceClassSum_eq_faceBit
    rintro ⟨s, t⟩
    norm_num [faceCoord, Adjacent]
    omega
  have h1 : faceClassSum a 1 (3 * l + 1, 3 * j + 3) = faceBit a 1 l (j + 1) := by
    apply faceClassSum_eq_faceBit
    rintro ⟨s, t⟩
    norm_num [faceCoord, Adjacent]
    omega
  have h2 : faceClassSum a 2 (3 * l + 1, 3 * j + 3) =
      if l = 0 then 0 else faceBit a 2 (l - 1) j := by
    have h := faceClassSum_eq_guard a 2 (3 * l + 1, 3 * j + 3) (l - 1) j (l ≠ 0) (by
      rintro ⟨s, t⟩
      norm_num [faceCoord, Adjacent]
      omega)
    simpa only [ne_eq, ite_not] using h
  simp only [spinAt, Fin.sum_univ_three, h0, h1, h2]
  ring

/-- An even site in the middle row meets all three faces in one column. -/
theorem spinAt_b_even {r : ℕ} (a : Face r → ZMod 2) (l j : ℕ) :
    spinAt a (3 * l + 2, 3 * j + 1) =
      1 + faceBit a 2 l j + faceBit a 0 l j + faceBit a 1 l j := by
  have h0 : faceClassSum a 0 (3 * l + 2, 3 * j + 1) = faceBit a 0 l j := by
    apply faceClassSum_eq_faceBit
    rintro ⟨s, t⟩
    norm_num [faceCoord, Adjacent]
    omega
  have h1 : faceClassSum a 1 (3 * l + 2, 3 * j + 1) = faceBit a 1 l j := by
    apply faceClassSum_eq_faceBit
    rintro ⟨s, t⟩
    norm_num [faceCoord, Adjacent]
    omega
  have h2 : faceClassSum a 2 (3 * l + 2, 3 * j + 1) = faceBit a 2 l j := by
    apply faceClassSum_eq_faceBit
    rintro ⟨s, t⟩
    norm_num [faceCoord, Adjacent]
    omega
  simp only [spinAt, Fin.sum_univ_three, h0, h1, h2]
  ring

/-- An odd middle-row site meets the next face of the second color. -/
theorem spinAt_b_odd {r : ℕ} (a : Face r → ZMod 2) (l j : ℕ) :
    spinAt a (3 * l + 2, 3 * j + 2) =
      1 + faceBit a 2 l j + faceBit a 0 l j + faceBit a 1 l (j + 1) := by
  have h0 : faceClassSum a 0 (3 * l + 2, 3 * j + 2) = faceBit a 0 l j := by
    apply faceClassSum_eq_faceBit
    rintro ⟨s, t⟩
    norm_num [faceCoord, Adjacent]
    omega
  have h1 : faceClassSum a 1 (3 * l + 2, 3 * j + 2) = faceBit a 1 l (j + 1) := by
    apply faceClassSum_eq_faceBit
    rintro ⟨s, t⟩
    norm_num [faceCoord, Adjacent]
    omega
  have h2 : faceClassSum a 2 (3 * l + 2, 3 * j + 2) = faceBit a 2 l j := by
    apply faceClassSum_eq_faceBit
    rintro ⟨s, t⟩
    norm_num [faceCoord, Adjacent]
    omega
  simp only [spinAt, Fin.sum_univ_three, h0, h1, h2]
  ring

/-- The leftmost site of the bottom row meets the next layer. -/
theorem spinAt_c0 {r : ℕ} (a : Face r → ZMod 2) (l : ℕ) :
    spinAt a (3 * l + 3, 0) =
      1 + faceBit a 1 l 0 + faceBit a 0 (l + 1) 0 := by
  have h0 : faceClassSum a 0 (3 * l + 3, 0) = faceBit a 0 (l + 1) 0 := by
    apply faceClassSum_eq_faceBit
    rintro ⟨s, t⟩
    norm_num [faceCoord, Adjacent]
    omega
  have h1 : faceClassSum a 1 (3 * l + 3, 0) = faceBit a 1 l 0 := by
    apply faceClassSum_eq_faceBit
    rintro ⟨s, t⟩
    norm_num [faceCoord, Adjacent]
    omega
  have h2 : faceClassSum a 2 (3 * l + 3, 0) = 0 := by
    apply faceClassSum_zero
    rintro ⟨s, t⟩
    norm_num [faceCoord, Adjacent]
  simp only [spinAt, Fin.sum_univ_three, h0, h1, h2]
  ring

/-- An odd bottom-row site meets the current and next layers. -/
theorem spinAt_c_odd {r : ℕ} (a : Face r → ZMod 2) (l j : ℕ) :
    spinAt a (3 * l + 3, 3 * j + 1) =
      1 + faceBit a 2 l j + faceBit a 1 l j + faceBit a 0 (l + 1) j := by
  have h0 : faceClassSum a 0 (3 * l + 3, 3 * j + 1) = faceBit a 0 (l + 1) j := by
    apply faceClassSum_eq_faceBit
    rintro ⟨s, t⟩
    norm_num [faceCoord, Adjacent]
    omega
  have h1 : faceClassSum a 1 (3 * l + 3, 3 * j + 1) = faceBit a 1 l j := by
    apply faceClassSum_eq_faceBit
    rintro ⟨s, t⟩
    norm_num [faceCoord, Adjacent]
    omega
  have h2 : faceClassSum a 2 (3 * l + 3, 3 * j + 1) = faceBit a 2 l j := by
    apply faceClassSum_eq_faceBit
    rintro ⟨s, t⟩
    norm_num [faceCoord, Adjacent]
    omega
  simp only [spinAt, Fin.sum_univ_three, h0, h1, h2]
  ring

/-- The next even bottom site joins adjacent face columns. -/
theorem spinAt_c_even_succ {r : ℕ} (a : Face r → ZMod 2) (l j : ℕ) :
    spinAt a (3 * l + 3, 3 * j + 3) =
      1 + faceBit a 2 l j + faceBit a 1 l (j + 1) +
        faceBit a 0 (l + 1) (j + 1) := by
  have h0 : faceClassSum a 0 (3 * l + 3, 3 * j + 3) = faceBit a 0 (l + 1) (j + 1) := by
    apply faceClassSum_eq_faceBit
    rintro ⟨s, t⟩
    norm_num [faceCoord, Adjacent]
    omega
  have h1 : faceClassSum a 1 (3 * l + 3, 3 * j + 3) = faceBit a 1 l (j + 1) := by
    apply faceClassSum_eq_faceBit
    rintro ⟨s, t⟩
    norm_num [faceCoord, Adjacent]
    omega
  have h2 : faceClassSum a 2 (3 * l + 3, 3 * j + 3) = faceBit a 2 l j := by
    apply faceClassSum_eq_faceBit
    rintro ⟨s, t⟩
    norm_num [faceCoord, Adjacent]
    omega
  simp only [spinAt, Fin.sum_univ_three, h0, h1, h2]
  ring

end Quantum.StabilizerGroup.ColorCode
