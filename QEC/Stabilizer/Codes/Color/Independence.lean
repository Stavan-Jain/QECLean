import QEC.Stabilizer.Codes.Color.Geometry
import QEC.Stabilizer.Framework.Homological.SelfDual

/-!
# Independent face checks of the triangular color code

Every face has a physical site immediately above it. At that site, the only
face in the same row is the original face; all other incident faces are in
earlier rows. A nonzero linear relation therefore has a contradiction at the
upper site of a face in its first nonzero row.
-/

namespace Quantum.StabilizerGroup.ColorCode

open scoped BigOperators

/-- An upper neighboring site of a face, chosen inside the triangle. -/
def upperSite (p : Coord) : Coord :=
  (p.1 - 1, if p.2 = 0 then 0 else p.2 - 1)

/-- The chosen upper neighbor of a face is a physical site. -/
theorem upperSite_isSite {r : ℕ} {p : Coord} (hp : IsFace r p) :
    IsSite r (upperSite p) := by
  rcases p with ⟨a, b⟩
  rcases hp with ⟨⟨hba, har⟩, hmod⟩
  by_cases hb : b = 0 <;> simp [upperSite, IsSite, InPatch, hb] <;> omega

/-- A face is adjacent to its chosen upper site. -/
theorem adjacent_upperSite {r : ℕ} {p : Coord} (hp : IsFace r p) :
    Adjacent p (upperSite p) := by
  rcases p with ⟨a, b⟩
  rcases hp with ⟨⟨hba, har⟩, hmod⟩
  by_cases hb : b = 0 <;> simp [upperSite, Adjacent, hb] <;> omega

/-- A face incident to an upper site cannot be in a later row. -/
theorem row_le_of_adjacent_upperSite {r : ℕ} {p g : Coord}
    (hp : IsFace r p) (hg : Adjacent g (upperSite p)) : g.1 ≤ p.1 := by
  rcases p with ⟨a, b⟩
  rcases g with ⟨c, d⟩
  rcases hp with ⟨⟨hba, har⟩, hmod⟩
  dsimp [upperSite, Adjacent] at hg ⊢
  omega

/-- The original face is the unique incident face in its row at an upper
site. -/
theorem eq_of_adjacent_upperSite_of_row_eq {r : ℕ} {p g : Coord}
    (hp : IsFace r p) (hg : IsFace r g) (hadj : Adjacent g (upperSite p))
    (hrow : g.1 = p.1) : g = p := by
  rcases p with ⟨a, b⟩
  rcases g with ⟨c, d⟩
  rcases hp with ⟨⟨hba, har⟩, hmod⟩
  rcases hg with ⟨⟨hdc, hcr⟩, hgmod⟩
  apply Prod.ext
  · exact hrow
  · by_cases hb : b = 0 <;> simp [upperSite, Adjacent, hb] at hadj <;> dsimp at * <;>
      omega

/-- The binary incidence vectors of all color-code faces are independent. -/
theorem linearIndependent_incidence (r : ℕ) :
    LinearIndependent (ZMod 2) (@incidence r) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hsum i
  by_contra hi
  let s : Finset (Face r) := Finset.univ.filter fun f => c f ≠ 0
  have hs : s.Nonempty := ⟨i, by simp [s, hi]⟩
  obtain ⟨f, hf, hmin⟩ := s.exists_min_image (fun f => (faceCoord f).1) hs
  obtain ⟨q, hq⟩ := exists_qubitCoord (upperSite (faceCoord f))
    (upperSite_isSite (faceCoord_isFace f))
  have hsumq := congr_fun hsum q
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hsumq
  have hother : ∀ g ∈ (Finset.univ : Finset (Face r)), g ≠ f →
      c g * incidence g q = 0 := by
    intro g _ hgf
    by_cases hc : c g = 0
    · simp [hc]
    have hrow : (faceCoord f).1 ≤ (faceCoord g).1 :=
      hmin g (by simp [s, hc])
    by_cases ha : Adjacent (faceCoord g) (qubitCoord q)
    · rw [hq] at ha
      have hle := row_le_of_adjacent_upperSite (faceCoord_isFace f) ha
      have heq := eq_of_adjacent_upperSite_of_row_eq (faceCoord_isFace f)
        (faceCoord_isFace g) ha (Nat.le_antisymm hle hrow)
      exact (hgf (faceCoord_injective r heq)).elim
    · simp [incidence, mem_faceSupport, ha]
  have hface : incidence f q = 1 := by
    simp [incidence, mem_faceSupport, hq, adjacent_upperSite (faceCoord_isFace f)]
  rw [Finset.sum_eq_single f hother (fun h => (h (Finset.mem_univ f)).elim),
    hface, mul_one] at hsumq
  exact (Finset.mem_filter.mp hf).2 hsumq

/-- No nonzero combination of color-code face checks vanishes. -/
theorem checkCombination_injective (r : ℕ) :
    Function.Injective (Stabilizer.Homological.SelfDual.checkCombination (@incidence r)) := by
  intro c c' h
  apply (linearIndependent_incidence r).fintypeLinearCombination_injective
  ext q
  simpa [Stabilizer.Homological.SelfDual.checkCombination, Fintype.linearCombination_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congr_fun h q

end Quantum.StabilizerGroup.ColorCode
