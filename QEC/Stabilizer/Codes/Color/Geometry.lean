import Mathlib.Tactic

/-!
# Triangular honeycomb color-code geometry

The parameter `r` gives distance `2 * r + 1`. Coordinates follow the triangular
honeycomb convention: `0 ≤ column ≤ row ≤ 3 * r`; faces have
`(row + column) % 3 = 2`, and the remaining positions are data qubits.

The finite index types enumerate the rows explicitly. This keeps the physical
qubit and face counts separate from any linear-algebra or distance assumptions.
-/

namespace Quantum.StabilizerGroup.ColorCode

open scoped BigOperators

/-- Triangular honeycomb coordinates, ordered as `(row, column)`. -/
abbrev Coord := ℕ × ℕ

/-- A row of faces in one of the three-row layers of the patch. -/
abbrev FaceRow (r : ℕ) := (l : Fin r) × Fin (l.val + 1)

/-- Faces, with a row class and a triangular row index. -/
abbrev Face (r : ℕ) := Fin 3 × FaceRow r

/-- Non-apex qubits, enumerated by layer, row within that layer, and site. -/
abbrev LayerQubit (r : ℕ) :=
  (l : Fin r) × (k : Fin 3) × Fin (2 * l.val + 1 + k.val)

/-- Data qubits: the apex and the three rows in each successive layer. -/
abbrev Qubit (r : ℕ) := Unit ⊕ LayerQubit r

/-- Number of physical data qubits in the distance-`2r+1` patch. -/
def numQubits (r : ℕ) : ℕ := 3 * r * (r + 1) + 1

/-- Number of independent face checks of either Pauli type. -/
def numFaces (r : ℕ) : ℕ := 3 * (r * (r + 1) / 2)

/-- The odd distance parameter of the triangular patch. -/
def distance (r : ℕ) : ℕ := 2 * r + 1

/-- Coordinates of a face in row classes `0`, `1`, and `2`. -/
def faceCoord {r : ℕ} (f : Face r) : Coord :=
  (3 * f.2.1.val + 1 + f.1.val,
    3 * f.2.2.val + if f.1.val = 0 then 1 else if f.1.val = 1 then 0 else 2)

/-- Coordinates of a physical site in its explicitly enumerated row. -/
def qubitCoord {r : ℕ} : Qubit r → Coord
  | .inl _ => (0, 0)
  | .inr ⟨l, k, j⟩ =>
      (3 * l.val + 1 + k.val,
        3 * (j.val / 2) +
          if k.val = 0 then 2 * (j.val % 2)
          else if k.val = 1 then 1 + j.val % 2 else j.val % 2)

/-- A coordinate belongs to the triangular patch. -/
def InPatch (r : ℕ) (p : Coord) : Prop := p.2 ≤ p.1 ∧ p.1 ≤ 3 * r

/-- A coordinate is a data-qubit site of the triangular honeycomb patch. -/
def IsSite (r : ℕ) (p : Coord) : Prop :=
  InPatch r p ∧ (p.1 + p.2) % 3 ≠ 2

/-- A coordinate is a face center of the triangular honeycomb patch. -/
def IsFace (r : ℕ) (p : Coord) : Prop :=
  InPatch r p ∧ (p.1 + p.2) % 3 = 2

/-- The six face neighbors, expressed without truncated subtraction. -/
def Adjacent (f q : Coord) : Prop :=
  (q.1 + 1 = f.1 ∧ q.2 = f.2) ∨
  (q.1 = f.1 + 1 ∧ q.2 = f.2) ∨
  (q.1 = f.1 ∧ q.2 + 1 = f.2) ∨
  (q.1 = f.1 ∧ q.2 = f.2 + 1) ∨
  (q.1 + 1 = f.1 ∧ q.2 + 1 = f.2) ∨
  (q.1 = f.1 + 1 ∧ q.2 = f.2 + 1)

instance (f q : Coord) : Decidable (Adjacent f q) := inferInstanceAs (Decidable (_ ∨ _))

/-- Face qubits, clipped to the triangular patch by their index type. -/
def faceSupport {r : ℕ} (f : Face r) : Finset (Qubit r) :=
  Finset.univ.filter fun q => Adjacent (faceCoord f) (qubitCoord q)

/-- Binary incidence vector of one color-code face. -/
def incidence {r : ℕ} (f : Face r) (q : Qubit r) : ZMod 2 :=
  if q ∈ faceSupport f then 1 else 0

/-- Membership in a face is exactly adjacency of its lattice coordinates. -/
@[simp] theorem mem_faceSupport {r : ℕ} (f : Face r) (q : Qubit r) :
    q ∈ faceSupport f ↔ Adjacent (faceCoord f) (qubitCoord q) := by
  simp [faceSupport]

/-- The triangular row sum, stated without natural-number division. -/
private theorem twice_sum_rows (r : ℕ) :
    2 * (∑ l : Fin r, (l.val + 1)) = r * (r + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      nlinarith

/-- The number of triangular face-row slots. -/
theorem card_faceRow (r : ℕ) : Fintype.card (FaceRow r) = r * (r + 1) / 2 := by
  simp only [FaceRow, Fintype.card_sigma, Fintype.card_fin]
  have h := twice_sum_rows r
  omega

/-- The patch contains `3r(r+1)/2` faces. -/
theorem card_face (r : ℕ) : Fintype.card (Face r) = numFaces r := by
  change Fintype.card (Fin 3 × FaceRow r) = numFaces r
  rw [Fintype.card_prod, Fintype.card_fin, card_faceRow]
  rfl

/-- The patch contains `3r(r+1)+1` physical data qubits. -/
theorem card_qubit (r : ℕ) : Fintype.card (Qubit r) = numQubits r := by
  simp only [Qubit, LayerQubit, Fintype.card_sum, Fintype.card_unit,
    Fintype.card_sigma, Fintype.card_fin, Fin.sum_univ_three]
  have h := twice_sum_rows r
  have hs : (∑ l : Fin r, ((2 * l.val + 1) + (2 * l.val + 1 + 1) +
      (2 * l.val + 1 + 2))) = 6 * ∑ l : Fin r, (l.val + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  change 1 + (∑ l : Fin r, ((2 * l.val + 1) + (2 * l.val + 1 + 1) +
    (2 * l.val + 1 + 2))) = numQubits r
  rw [hs]
  dsimp [numQubits]
  nlinarith

/-- Twice the face count is one less than the number of physical qubits. -/
theorem twice_numFaces (r : ℕ) : 2 * numFaces r + 1 = numQubits r := by
  have h := twice_sum_rows r
  have hd : 2 * (r * (r + 1) / 2) = r * (r + 1) := by omega
  dsimp [numFaces, numQubits]
  nlinarith

/-- The row enumeration places every face at a genuine face center. -/
theorem faceCoord_isFace {r : ℕ} (f : Face r) : IsFace r (faceCoord f) := by
  rcases f with ⟨k, l, c⟩
  have hl := l.isLt
  have hc := c.isLt
  fin_cases k <;> simp [faceCoord, IsFace, InPatch] <;> omega

/-- The row enumeration places every data qubit at a genuine physical site. -/
theorem qubitCoord_isSite {r : ℕ} (q : Qubit r) : IsSite r (qubitCoord q) := by
  rcases q with u | ⟨l, k, j⟩
  · simp [qubitCoord, IsSite, InPatch]
  · have hl := l.isLt
    have hj := j.isLt
    fin_cases k <;> simp [qubitCoord, IsSite, InPatch] <;> simp at hj <;> omega

/-- Distinct face indices have distinct lattice coordinates. -/
theorem faceCoord_injective (r : ℕ) : Function.Injective (@faceCoord r) := by
  rintro ⟨k, l, c⟩ ⟨k', l', c'⟩ h
  have hrow := congrArg Prod.fst h
  have hcol := congrArg Prod.snd h
  have hk := k.isLt
  have hk' := k'.isLt
  simp only [faceCoord] at hrow hcol
  have hl : l = l' := Fin.ext (by omega)
  have heq : k = k' := Fin.ext (by omega)
  subst l'
  subst k'
  have hc : c = c' := Fin.ext (by omega)
  subst c'
  rfl

/-- Distinct physical-qubit indices have distinct lattice coordinates. -/
theorem qubitCoord_injective (r : ℕ) : Function.Injective (@qubitCoord r) := by
  rintro (u | ⟨l, k, j⟩) (u' | ⟨l', k', j'⟩) h
  · cases u
    cases u'
    rfl
  · have hrow := congrArg Prod.fst h
    simp only [qubitCoord] at hrow
    omega
  · have hrow := congrArg Prod.fst h
    simp only [qubitCoord] at hrow
    omega
  · have hrow := congrArg Prod.fst h
    have hcol := congrArg Prod.snd h
    have hk := k.isLt
    have hk' := k'.isLt
    simp only [qubitCoord] at hrow hcol
    have hl : l = l' := Fin.ext (by omega)
    have heq : k = k' := Fin.ext (by omega)
    subst l'
    subst k'
    have hj : j = j' := by
      apply Fin.ext
      fin_cases k <;> simp at hcol <;> omega
    subst j'
    rfl

/-- Every physical site of the triangle occurs in the finite row enumeration. -/
theorem exists_qubitCoord {r : ℕ} (p : Coord) (hp : IsSite r p) :
    ∃ q : Qubit r, qubitCoord q = p := by
  rcases p with ⟨a, b⟩
  rcases hp with ⟨⟨hba, har⟩, hmod⟩
  by_cases ha : a = 0
  · have hb : b = 0 := by omega
    subst a
    subst b
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

/-- Every face center of the triangle occurs in the finite face enumeration. -/
theorem exists_faceCoord {r : ℕ} (p : Coord) (hp : IsFace r p) :
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

/-- The row enumeration is equivalent to the geometric set of physical sites. -/
noncomputable def qubitEquivSite (r : ℕ) : Qubit r ≃ {p : Coord // IsSite r p} :=
  Equiv.ofBijective (fun q => ⟨qubitCoord q, qubitCoord_isSite q⟩) (by
    constructor
    · intro q q' h
      exact qubitCoord_injective r (congrArg Subtype.val h)
    · rintro ⟨p, hp⟩
      obtain ⟨q, hq⟩ := exists_qubitCoord p hp
      exact ⟨q, Subtype.ext hq⟩)

/-- The row enumeration is equivalent to the geometric set of face centers. -/
noncomputable def faceEquivCenter (r : ℕ) : Face r ≃ {p : Coord // IsFace r p} :=
  Equiv.ofBijective (fun f => ⟨faceCoord f, faceCoord_isFace f⟩) (by
    constructor
    · intro f f' h
      exact faceCoord_injective r (congrArg Subtype.val h)
    · rintro ⟨p, hp⟩
      obtain ⟨f, hf⟩ := exists_faceCoord p hp
      exact ⟨f, Subtype.ext hf⟩)

/-- The physical-qubit count has the paper's expression in the odd distance. -/
theorem numQubits_eq_distance (r : ℕ) :
    numQubits r = (3 * (distance r) ^ 2 + 1) / 4 := by
  have h : 4 * numQubits r = 3 * (distance r) ^ 2 + 1 := by
    simp only [numQubits, distance]
    ring
  omega

/-- The code-distance parameter is always odd. -/
theorem distance_odd (r : ℕ) : Odd (distance r) := ⟨r, rfl⟩

end Quantum.StabilizerGroup.ColorCode
