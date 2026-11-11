import Mathlib.Tactic

/-!
# Geometry of the triangular honeycomb color code

The patch of parameter `r` consists of the lattice points `(row, column)` with
`0 ≤ column ≤ row ≤ 3 * r` (`InPatch`). A point with `(row + column) % 3 = 2`
is the center of a face (`IsFace`); every other point carries a data qubit
(`IsSite`). A face contains its six lattice neighbors (`Adjacent`) that lie in
the patch.

The qubits and the faces are enumerated row by row by the finite types
`Qubit r` and `Face r`, with coordinates `qubitCoord` and `faceCoord`. Both
enumerations are bijections onto the sites and the face centers
(`qubitEquivSite`, `faceEquivCenter`). There are `numQubits r = 3r(r+1) + 1`
qubits (`card_qubit`) and `numFaces r = 3r(r+1)/2` faces (`card_face`), so
that `numQubits r = 2 * numFaces r + 1` (`twice_numFaces`).

`faceSupport f` is the set of qubits of the face `f` and `incidence f` its
indicator vector over `ZMod 2`. Pairing a chain with `incidence f` sums the
chain over the face (`sum_incidence_mul`).
-/

namespace Quantum.StabilizerGroup.ColorCode

open scoped BigOperators

/-! ## Coordinates and index types -/

/-- Lattice coordinates, ordered as `(row, column)`. -/
abbrev Coord := ℕ × ℕ

/-- A layer `l < r` of the patch together with a position `< l + 1` in a row
of faces of that layer. -/
abbrev FaceRow (r : ℕ) := (l : Fin r) × Fin (l.val + 1)

/-- Faces: each layer has three rows of faces, and the rows of layer `l` have
`l + 1` faces each. -/
abbrev Face (r : ℕ) := Fin 3 × FaceRow r

/-- Qubits other than the apex: row `k` of layer `l` has `2 * l + 1 + k`
qubits. -/
abbrev LayerQubit (r : ℕ) :=
  (l : Fin r) × (k : Fin 3) × Fin (2 * l.val + 1 + k.val)

/-- Data qubits: the apex and the three rows of qubits of each layer. -/
abbrev Qubit (r : ℕ) := Unit ⊕ LayerQubit r

/-- The number of data qubits of the patch of parameter `r`. -/
def numQubits (r : ℕ) : ℕ := 3 * r * (r + 1) + 1

/-- The number of faces of the patch of parameter `r`. -/
def numFaces (r : ℕ) : ℕ := 3 * (r * (r + 1) / 2)

/-- The distance `2 * r + 1` of the color code of parameter `r`. -/
def distance (r : ℕ) : ℕ := 2 * r + 1

/-- The coordinates of the center of a face: row `k` of layer `l` is the
lattice row `3 * l + 1 + k`. -/
def faceCoord {r : ℕ} (f : Face r) : Coord :=
  (3 * f.2.1.val + 1 + f.1.val,
    3 * f.2.2.val + if f.1.val = 0 then 1 else if f.1.val = 1 then 0 else 2)

/-- The coordinates of a qubit: the apex is `(0, 0)`, and row `k` of layer `l`
is the lattice row `3 * l + 1 + k`. -/
def qubitCoord {r : ℕ} : Qubit r → Coord
  | .inl _ => (0, 0)
  | .inr ⟨l, k, j⟩ =>
      (3 * l.val + 1 + k.val,
        3 * (j.val / 2) +
          if k.val = 0 then 2 * (j.val % 2)
          else if k.val = 1 then 1 + j.val % 2 else j.val % 2)

/-- A point lies in the triangular patch: `column ≤ row ≤ 3 * r`. -/
def InPatch (r : ℕ) (p : Coord) : Prop := p.2 ≤ p.1 ∧ p.1 ≤ 3 * r

/-- A point of the patch carries a data qubit. -/
def IsSite (r : ℕ) (p : Coord) : Prop :=
  InPatch r p ∧ (p.1 + p.2) % 3 ≠ 2

/-- A point of the patch is the center of a face. -/
def IsFace (r : ℕ) (p : Coord) : Prop :=
  InPatch r p ∧ (p.1 + p.2) % 3 = 2

/-- `q` is one of the six lattice neighbors of `f`: the points `f ± (1, 0)`,
`f ± (0, 1)` and `f ± (1, 1)`, stated without subtraction. -/
def Adjacent (f q : Coord) : Prop :=
  (q.1 + 1 = f.1 ∧ q.2 = f.2) ∨
  (q.1 = f.1 + 1 ∧ q.2 = f.2) ∨
  (q.1 = f.1 ∧ q.2 + 1 = f.2) ∨
  (q.1 = f.1 ∧ q.2 = f.2 + 1) ∨
  (q.1 + 1 = f.1 ∧ q.2 + 1 = f.2) ∨
  (q.1 = f.1 + 1 ∧ q.2 = f.2 + 1)

/-- Adjacency of two lattice points is decidable. -/
instance (f q : Coord) : Decidable (Adjacent f q) := inferInstanceAs (Decidable (_ ∨ _))

/-! ## Faces as sets of qubits -/

/-- The qubits of a face: those at a lattice neighbor of its center. -/
def faceSupport {r : ℕ} (f : Face r) : Finset (Qubit r) :=
  Finset.univ.filter fun q => Adjacent (faceCoord f) (qubitCoord q)

/-- The indicator vector of a face over `ZMod 2`. -/
def incidence {r : ℕ} (f : Face r) (q : Qubit r) : ZMod 2 :=
  if q ∈ faceSupport f then 1 else 0

/-- A qubit lies on a face iff it is at a lattice neighbor of its center. -/
@[simp] lemma mem_faceSupport {r : ℕ} (f : Face r) (q : Qubit r) :
    q ∈ faceSupport f ↔ Adjacent (faceCoord f) (qubitCoord q) := by
  simp [faceSupport]

/-- Pairing a chain with the indicator vector of a face sums the chain over
the qubits of the face. -/
lemma sum_incidence_mul {r : ℕ} (f : Face r) (c : Qubit r → ZMod 2) :
    ∑ q, incidence f q * c q = ∑ q ∈ faceSupport f, c q := by
  simp only [incidence, ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]

/-- The pairing of the indicator vectors of two faces counts their common
qubits modulo `2`. -/
lemma sum_incidence_mul_incidence {r : ℕ} (f g : Face r) :
    ∑ q, incidence f q * incidence g q =
      ∑ _q ∈ faceSupport f ∩ faceSupport g, (1 : ZMod 2) :=
  (sum_incidence_mul f _).trans (Finset.sum_ite_mem _ _ _)

/-! ## Counting qubits and faces -/

/-- The sum `1 + 2 + ⋯ + r`, stated without division. -/
private lemma twice_sum_rows (r : ℕ) :
    2 * (∑ l : Fin r, (l.val + 1)) = r * (r + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    linarith

/-- There are `r(r+1)/2` pairs of a layer and a position in a row of faces of
that layer. -/
lemma card_faceRow (r : ℕ) : Fintype.card (FaceRow r) = r * (r + 1) / 2 := by
  simp only [FaceRow, Fintype.card_sigma, Fintype.card_fin]
  have h := twice_sum_rows r
  omega

/-- The patch has `3r(r+1)/2` faces. -/
theorem card_face (r : ℕ) : Fintype.card (Face r) = numFaces r := by
  rw [Fintype.card_prod, Fintype.card_fin, card_faceRow, numFaces]

/-- The patch has `3r(r+1) + 1` data qubits. -/
theorem card_qubit (r : ℕ) : Fintype.card (Qubit r) = numQubits r := by
  have h := twice_sum_rows r
  have hs (l : Fin r) : ∑ k : Fin 3, (2 * l.val + 1 + k.val) = 6 * (l.val + 1) := by
    simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two]
    ring
  simp only [Qubit, LayerQubit, Fintype.card_sum, Fintype.card_unit, Fintype.card_sigma,
    Fintype.card_fin, hs, ← Finset.mul_sum, numQubits]
  linarith

/-- The number of qubits is one more than twice the number of faces. -/
lemma twice_numFaces (r : ℕ) : 2 * numFaces r + 1 = numQubits r := by
  have h := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self r)
  simp only [numFaces, numQubits]
  linarith

/-- The cardinality form of `twice_numFaces`: there is one more qubit than
there are X-checks and Z-checks together. -/
lemma card_qubit_eq_two_mul_card_face_add_one (r : ℕ) :
    Fintype.card (Qubit r) = 2 * Fintype.card (Face r) + 1 := by
  rw [card_qubit, card_face, twice_numFaces]

/-- In terms of the distance `d = 2r + 1`, the number of qubits is
`(3d² + 1) / 4`. -/
lemma numQubits_eq_distance (r : ℕ) :
    numQubits r = (3 * (distance r) ^ 2 + 1) / 4 := by
  have h : 4 * numQubits r = 3 * (distance r) ^ 2 + 1 := by
    simp only [numQubits, distance]
    ring
  omega

/-- The distance `2 * r + 1` is odd. -/
lemma distance_odd (r : ℕ) : Odd (distance r) := ⟨r, rfl⟩

/-! ## The enumerations are bijections onto the sites and the face centers -/

/-- The center of every face of the enumeration is a face center of the
patch. -/
lemma faceCoord_isFace {r : ℕ} (f : Face r) : IsFace r (faceCoord f) := by
  rcases f with ⟨k, l, c⟩
  have hl := l.isLt
  have hc := c.isLt
  fin_cases k <;> simp [faceCoord, IsFace, InPatch] <;> omega

/-- Every qubit of the enumeration sits at a site of the patch. -/
lemma qubitCoord_isSite {r : ℕ} (q : Qubit r) : IsSite r (qubitCoord q) := by
  rcases q with u | ⟨l, k, j⟩
  · simp [qubitCoord, IsSite, InPatch]
  · have hl := l.isLt
    have hj := j.isLt
    fin_cases k <;> simp [qubitCoord, IsSite, InPatch] <;> simp at hj <;> omega

/-- Distinct faces have distinct centers. -/
lemma faceCoord_injective (r : ℕ) : Function.Injective (@faceCoord r) := by
  rintro ⟨k, l, c⟩ ⟨k', l', c'⟩ h
  have hrow := congrArg Prod.fst h
  have hcol := congrArg Prod.snd h
  have hk := k.isLt
  have hk' := k'.isLt
  simp only [faceCoord] at hrow hcol
  obtain rfl : l = l' := Fin.ext (by omega)
  obtain rfl : k = k' := Fin.ext (by omega)
  obtain rfl : c = c' := Fin.ext (by omega)
  rfl

/-- Distinct qubits have distinct coordinates. -/
lemma qubitCoord_injective (r : ℕ) : Function.Injective (@qubitCoord r) := by
  rintro (_ | ⟨l, k, j⟩) (_ | ⟨l', k', j'⟩) h
  · rfl
  · have hrow : 0 = 3 * l'.val + 1 + k'.val := congrArg Prod.fst h
    omega
  · have hrow : 3 * l.val + 1 + k.val = 0 := congrArg Prod.fst h
    omega
  · have hrow := congrArg Prod.fst h
    have hcol := congrArg Prod.snd h
    have hk := k.isLt
    have hk' := k'.isLt
    simp only [qubitCoord] at hrow hcol
    obtain rfl : l = l' := Fin.ext (by omega)
    obtain rfl : k = k' := Fin.ext (by omega)
    obtain rfl : j = j' := Fin.ext (by fin_cases k <;> simp at hcol <;> omega)
    rfl

/-- Every site of the patch is the position of a qubit of the enumeration. -/
lemma exists_qubitCoord {r : ℕ} (p : Coord) (hp : IsSite r p) :
    ∃ q : Qubit r, qubitCoord q = p := by
  rcases p with ⟨a, b⟩
  rcases hp with ⟨⟨hba, har⟩, hmod⟩
  obtain rfl | ha := Nat.eq_zero_or_pos a
  · obtain rfl : b = 0 := by omega
    exact ⟨.inl (), rfl⟩
  have hcases : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · refine ⟨.inr ⟨⟨(a - 1) / 3, by omega⟩, ⟨2, by omega⟩,
      ⟨2 * (b / 3) + b % 3, by dsimp; omega⟩⟩, ?_⟩
    apply Prod.ext <;> dsimp [qubitCoord] <;> omega
  · refine ⟨.inr ⟨⟨a / 3, by omega⟩, ⟨0, by omega⟩,
      ⟨2 * (b / 3) + b % 3 / 2, by dsimp; omega⟩⟩, ?_⟩
    apply Prod.ext <;> dsimp [qubitCoord] <;> omega
  · refine ⟨.inr ⟨⟨a / 3, by omega⟩, ⟨1, by omega⟩,
      ⟨2 * (b / 3) + (b % 3 - 1), by dsimp; omega⟩⟩, ?_⟩
    apply Prod.ext <;> dsimp [qubitCoord] <;> omega

/-- Every face center of the patch is the center of a face of the
enumeration. -/
lemma exists_faceCoord {r : ℕ} (p : Coord) (hp : IsFace r p) :
    ∃ f : Face r, faceCoord f = p := by
  rcases p with ⟨a, b⟩
  rcases hp with ⟨⟨hba, har⟩, hmod⟩
  have ha : 0 < a := by omega
  have hcases : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · refine ⟨⟨⟨2, by omega⟩, ⟨(a - 1) / 3, by omega⟩,
      ⟨b / 3, by dsimp; omega⟩⟩, ?_⟩
    apply Prod.ext <;> dsimp [faceCoord] <;> omega
  · refine ⟨⟨⟨0, by omega⟩, ⟨a / 3, by omega⟩,
      ⟨b / 3, by dsimp; omega⟩⟩, ?_⟩
    apply Prod.ext <;> dsimp [faceCoord] <;> omega
  · refine ⟨⟨⟨1, by omega⟩, ⟨a / 3, by omega⟩,
      ⟨b / 3, by dsimp; omega⟩⟩, ?_⟩
    apply Prod.ext <;> dsimp [faceCoord] <;> omega

/-- The qubits of the enumeration correspond bijectively to the sites of the
patch. -/
noncomputable def qubitEquivSite (r : ℕ) : Qubit r ≃ {p : Coord // IsSite r p} :=
  Equiv.ofBijective (fun q => ⟨qubitCoord q, qubitCoord_isSite q⟩)
    ⟨fun _ _ h => qubitCoord_injective r (congrArg Subtype.val h),
      fun ⟨p, hp⟩ => (exists_qubitCoord p hp).imp fun _ hq => Subtype.ext hq⟩

/-- The faces of the enumeration correspond bijectively to the face centers of
the patch. -/
noncomputable def faceEquivCenter (r : ℕ) : Face r ≃ {p : Coord // IsFace r p} :=
  Equiv.ofBijective (fun f => ⟨faceCoord f, faceCoord_isFace f⟩)
    ⟨fun _ _ h => faceCoord_injective r (congrArg Subtype.val h),
      fun ⟨p, hp⟩ => (exists_faceCoord p hp).imp fun _ hf => Subtype.ext hf⟩

end Quantum.StabilizerGroup.ColorCode
