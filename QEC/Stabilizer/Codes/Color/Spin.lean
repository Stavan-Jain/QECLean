import QEC.Stabilizer.Codes.Color.Code

/-!
# Spins of the color code in terms of face labels

Given a label `a f : ZMod 2` on every face, the *spin* `spinAt a p` at a
lattice point `p` is `1` plus the sum of the labels of the faces adjacent to
`p`. At the position of a qubit it is the value of the all-ones chain plus the
combination of face checks with coefficients `a` (`spinAt_qubitCoord`).

`faceBit a k l j` is the label of the face at position `j` of row `k` of layer
`l`, and `0` if there is no such face. The lemmas `spinAt_apex`, `spinAt_a0`,
`spinAt_a_odd`, `spinAt_a_even_succ`, `spinAt_b_even`, `spinAt_b_odd`,
`spinAt_c0`, `spinAt_c_odd` and `spinAt_c_even_succ` express the spin at every
qubit position through the labels `faceBit` of the at most three faces that
contain it. Here `a`, `b`, `c` name the three rows of qubits of a layer, the
lattice rows `3 * l + 1`, `3 * l + 2` and `3 * l + 3`.
-/

namespace Quantum.StabilizerGroup.ColorCode

open scoped BigOperators
open Stabilizer.Homological

/-- The label of the face at position `j` of row `k` of layer `l`, and `0` if
the patch has no such face. -/
def faceBit {r : ℕ} (a : Face r → ZMod 2) (k : Fin 3) (l j : ℕ) : ZMod 2 :=
  if hl : l < r then
    if hj : j < l + 1 then a (k, ⟨⟨l, hl⟩, ⟨j, hj⟩⟩) else 0
  else 0

/-- Face labels vanish beyond the last layer. -/
@[simp] lemma faceBit_of_layer_ge {r : ℕ} (a : Face r → ZMod 2)
    (k : Fin 3) (l j : ℕ) (h : r ≤ l) : faceBit a k l j = 0 := by
  simp [faceBit, show ¬l < r from by omega]

/-- Face labels vanish beyond the last position of a row of faces. -/
@[simp] lemma faceBit_of_column_ge {r : ℕ} (a : Face r → ZMod 2)
    (k : Fin 3) (l j : ℕ) (h : l + 1 ≤ j) : faceBit a k l j = 0 := by
  simp [faceBit, show ¬j < l + 1 from by omega]

/-- `faceBit a k l j` is the sum of the labels of the faces of row `k` at
layer `l` and position `j`, of which there is at most one. -/
private lemma faceBit_eq_sum {r : ℕ} (a : Face r → ZMod 2)
    (k : Fin 3) (l j : ℕ) :
    faceBit a k l j =
      ∑ f : FaceRow r, if f.1.val = l ∧ f.2.val = j then a (k, f) else 0 := by
  unfold faceBit
  split_ifs with hl hj
  · rw [Finset.sum_eq_single ⟨⟨l, hl⟩, ⟨j, hj⟩⟩]
    · simp
    · rintro ⟨s, t⟩ - hne
      refine if_neg fun h => hne ?_
      obtain rfl : s = ⟨l, hl⟩ := Fin.ext h.1
      obtain rfl : t = ⟨j, hj⟩ := Fin.ext h.2
      rfl
    · exact fun h => (h (Finset.mem_univ _)).elim
  · refine (Finset.sum_eq_zero fun f _ => if_neg fun h => hj ?_).symm
    have := f.2.isLt
    omega
  · refine (Finset.sum_eq_zero fun f _ => if_neg fun h => hl ?_).symm
    have := f.1.isLt
    omega

/-- The sum of the labels of the faces of row `k` adjacent to the lattice
point `p`. -/
def faceClassSum {r : ℕ} (a : Face r → ZMod 2) (k : Fin 3) (p : Coord) : ZMod 2 :=
  ∑ f : FaceRow r, if Adjacent (faceCoord (k, f)) p then a (k, f) else 0

/-- If the faces of row `k` adjacent to `p` are those at layer `l` and
position `j`, their labels sum to `faceBit a k l j`. -/
private lemma faceClassSum_eq_faceBit {r : ℕ} (a : Face r → ZMod 2)
    (k : Fin 3) (p : Coord) (l j : ℕ)
    (h : ∀ f : FaceRow r, Adjacent (faceCoord (k, f)) p ↔
      f.1.val = l ∧ f.2.val = j) :
    faceClassSum a k p = faceBit a k l j := by
  rw [faceBit_eq_sum]
  exact Finset.sum_congr rfl fun f _ => by simp only [h f]

/-- The form of `faceClassSum_eq_faceBit` for a point that has an adjacent
face of row `k` only if `P` does not hold. -/
private lemma faceClassSum_eq_guard {r : ℕ} (a : Face r → ZMod 2)
    (k : Fin 3) (p : Coord) (l j : ℕ) (P : Prop) [Decidable P]
    (h : ∀ f : FaceRow r, Adjacent (faceCoord (k, f)) p ↔
      ¬P ∧ f.1.val = l ∧ f.2.val = j) :
    faceClassSum a k p = if P then 0 else faceBit a k l j := by
  split_ifs with hP
  · exact Finset.sum_eq_zero fun f _ => if_neg fun hf => ((h f).mp hf).1 hP
  · exact faceClassSum_eq_faceBit a k p l j fun f => (h f).trans (and_iff_right hP)

/-- A point with no adjacent face of row `k` has no labels to sum. -/
private lemma faceClassSum_zero {r : ℕ} (a : Face r → ZMod 2)
    (k : Fin 3) (p : Coord)
    (h : ∀ f : FaceRow r, ¬Adjacent (faceCoord (k, f)) p) :
    faceClassSum a k p = 0 :=
  Finset.sum_eq_zero fun f _ => if_neg (h f)

/-- The spin at a lattice point: `1` plus the sum of the labels of the
adjacent faces. -/
def spinAt {r : ℕ} (a : Face r → ZMod 2) (p : Coord) : ZMod 2 :=
  1 + ∑ k : Fin 3, faceClassSum a k p

/-- The spin at a qubit is the value there of the all-ones chain plus the
combination of face checks with coefficients `a`. -/
theorem spinAt_qubitCoord {r : ℕ} (a : Face r → ZMod 2) (q : Qubit r) :
    spinAt a (qubitCoord q) = 1 + SelfDual.checkCombination (@incidence r) a q := by
  rw [spinAt, SelfDual.checkCombination_apply, Fintype.sum_prod_type]
  refine congrArg (1 + ·) (Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun f _ => ?_)
  simp [incidence]

/-! ## The spin at each kind of qubit position -/

/-- Decides which faces of a row are adjacent to a given lattice point: the
hypotheses of `faceClassSum_eq_faceBit`, `faceClassSum_eq_guard` and
`faceClassSum_zero` for explicit coordinates. -/
local macro "adjacent_faces" : tactic =>
  `(tactic| (rintro ⟨s, t⟩; norm_num [faceCoord, Adjacent] <;> omega))

/-- The spin at the apex `(0, 0)`. -/
lemma spinAt_apex {r : ℕ} (a : Face r → ZMod 2) :
    spinAt a (0, 0) = 1 + faceBit a 0 0 0 := by
  rw [spinAt, Fin.sum_univ_three,
    faceClassSum_eq_faceBit a 0 (0, 0) 0 0 (by adjacent_faces),
    faceClassSum_zero a 1 (0, 0) (by adjacent_faces),
    faceClassSum_zero a 2 (0, 0) (by adjacent_faces)]
  ring

/-- The spin at the leftmost qubit of row `a` of layer `l`. -/
lemma spinAt_a0 {r : ℕ} (a : Face r → ZMod 2) (l : ℕ) :
    spinAt a (3 * l + 1, 0) = 1 + faceBit a 0 l 0 + faceBit a 1 l 0 := by
  rw [spinAt, Fin.sum_univ_three,
    faceClassSum_eq_faceBit a 0 (3 * l + 1, 0) l 0 (by adjacent_faces),
    faceClassSum_eq_faceBit a 1 (3 * l + 1, 0) l 0 (by adjacent_faces),
    faceClassSum_zero a 2 (3 * l + 1, 0) (by adjacent_faces)]
  ring

/-- The spin at the qubit `(3 * l + 1, 3 * j + 2)` of row `a` of layer `l`,
which also lies on a face of the previous layer if `l ≠ 0`. -/
lemma spinAt_a_odd {r : ℕ} (a : Face r → ZMod 2) (l j : ℕ) :
    spinAt a (3 * l + 1, 3 * j + 2) =
      1 + (if l = 0 then 0 else faceBit a 2 (l - 1) j) +
        faceBit a 0 l j + faceBit a 1 l (j + 1) := by
  rw [spinAt, Fin.sum_univ_three,
    faceClassSum_eq_faceBit a 0 (3 * l + 1, 3 * j + 2) l j (by adjacent_faces),
    faceClassSum_eq_faceBit a 1 (3 * l + 1, 3 * j + 2) l (j + 1) (by adjacent_faces),
    faceClassSum_eq_guard a 2 (3 * l + 1, 3 * j + 2) (l - 1) j (l = 0) (by adjacent_faces)]
  ring

/-- The spin at the qubit `(3 * l + 1, 3 * j + 3)` of row `a` of layer `l`,
which also lies on a face of the previous layer if `l ≠ 0`. -/
lemma spinAt_a_even_succ {r : ℕ} (a : Face r → ZMod 2) (l j : ℕ) :
    spinAt a (3 * l + 1, 3 * j + 3) =
      1 + (if l = 0 then 0 else faceBit a 2 (l - 1) j) +
        faceBit a 0 l (j + 1) + faceBit a 1 l (j + 1) := by
  rw [spinAt, Fin.sum_univ_three,
    faceClassSum_eq_faceBit a 0 (3 * l + 1, 3 * j + 3) l (j + 1) (by adjacent_faces),
    faceClassSum_eq_faceBit a 1 (3 * l + 1, 3 * j + 3) l (j + 1) (by adjacent_faces),
    faceClassSum_eq_guard a 2 (3 * l + 1, 3 * j + 3) (l - 1) j (l = 0) (by adjacent_faces)]
  ring

/-- The spin at the qubit `(3 * l + 2, 3 * j + 1)` of row `b` of layer `l`. -/
lemma spinAt_b_even {r : ℕ} (a : Face r → ZMod 2) (l j : ℕ) :
    spinAt a (3 * l + 2, 3 * j + 1) =
      1 + faceBit a 2 l j + faceBit a 0 l j + faceBit a 1 l j := by
  rw [spinAt, Fin.sum_univ_three,
    faceClassSum_eq_faceBit a 0 (3 * l + 2, 3 * j + 1) l j (by adjacent_faces),
    faceClassSum_eq_faceBit a 1 (3 * l + 2, 3 * j + 1) l j (by adjacent_faces),
    faceClassSum_eq_faceBit a 2 (3 * l + 2, 3 * j + 1) l j (by adjacent_faces)]
  ring

/-- The spin at the qubit `(3 * l + 2, 3 * j + 2)` of row `b` of layer `l`. -/
lemma spinAt_b_odd {r : ℕ} (a : Face r → ZMod 2) (l j : ℕ) :
    spinAt a (3 * l + 2, 3 * j + 2) =
      1 + faceBit a 2 l j + faceBit a 0 l j + faceBit a 1 l (j + 1) := by
  rw [spinAt, Fin.sum_univ_three,
    faceClassSum_eq_faceBit a 0 (3 * l + 2, 3 * j + 2) l j (by adjacent_faces),
    faceClassSum_eq_faceBit a 1 (3 * l + 2, 3 * j + 2) l (j + 1) (by adjacent_faces),
    faceClassSum_eq_faceBit a 2 (3 * l + 2, 3 * j + 2) l j (by adjacent_faces)]
  ring

/-- The spin at the leftmost qubit of row `c` of layer `l`, which also lies on
a face of the next layer. -/
lemma spinAt_c0 {r : ℕ} (a : Face r → ZMod 2) (l : ℕ) :
    spinAt a (3 * l + 3, 0) = 1 + faceBit a 1 l 0 + faceBit a 0 (l + 1) 0 := by
  rw [spinAt, Fin.sum_univ_three,
    faceClassSum_eq_faceBit a 0 (3 * l + 3, 0) (l + 1) 0 (by adjacent_faces),
    faceClassSum_eq_faceBit a 1 (3 * l + 3, 0) l 0 (by adjacent_faces),
    faceClassSum_zero a 2 (3 * l + 3, 0) (by adjacent_faces)]
  ring

/-- The spin at the qubit `(3 * l + 3, 3 * j + 1)` of row `c` of layer `l`,
which also lies on a face of the next layer. -/
lemma spinAt_c_odd {r : ℕ} (a : Face r → ZMod 2) (l j : ℕ) :
    spinAt a (3 * l + 3, 3 * j + 1) =
      1 + faceBit a 2 l j + faceBit a 1 l j + faceBit a 0 (l + 1) j := by
  rw [spinAt, Fin.sum_univ_three,
    faceClassSum_eq_faceBit a 0 (3 * l + 3, 3 * j + 1) (l + 1) j (by adjacent_faces),
    faceClassSum_eq_faceBit a 1 (3 * l + 3, 3 * j + 1) l j (by adjacent_faces),
    faceClassSum_eq_faceBit a 2 (3 * l + 3, 3 * j + 1) l j (by adjacent_faces)]
  ring

/-- The spin at the qubit `(3 * l + 3, 3 * j + 3)` of row `c` of layer `l`,
which also lies on a face of the next layer. -/
lemma spinAt_c_even_succ {r : ℕ} (a : Face r → ZMod 2) (l j : ℕ) :
    spinAt a (3 * l + 3, 3 * j + 3) =
      1 + faceBit a 2 l j + faceBit a 1 l (j + 1) +
        faceBit a 0 (l + 1) (j + 1) := by
  rw [spinAt, Fin.sum_univ_three,
    faceClassSum_eq_faceBit a 0 (3 * l + 3, 3 * j + 3) (l + 1) (j + 1) (by adjacent_faces),
    faceClassSum_eq_faceBit a 1 (3 * l + 3, 3 * j + 3) l (j + 1) (by adjacent_faces),
    faceClassSum_eq_faceBit a 2 (3 * l + 3, 3 * j + 3) l j (by adjacent_faces)]
  ring

end Quantum.StabilizerGroup.ColorCode
