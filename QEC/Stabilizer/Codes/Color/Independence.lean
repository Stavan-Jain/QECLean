import QEC.Stabilizer.Codes.Color.Geometry
import QEC.Stabilizer.Framework.Homological.SelfDual

/-!
# Independence of the face checks of the color code

Every face has a qubit in the lattice row above its center, `upperSite`. The
other faces containing that qubit lie in strictly earlier rows
(`row_le_of_adjacent_upperSite`, `eq_of_adjacent_upperSite_of_row_eq`). Hence
the indicator vectors of the faces are linearly independent over `ZMod 2`
(`linearIndependent_incidence`): in a vanishing combination, a face with
nonzero coefficient in the earliest possible row would be the only such face
at its upper qubit. Equivalently the check-combination map is injective
(`checkCombination_injective`).
-/

namespace Quantum.StabilizerGroup.ColorCode

open scoped BigOperators
open Stabilizer.Homological

/-- The qubit position in the row above a face center `p`: its upper-left
neighbor, or its upper neighbor when `p` is in column `0`. -/
def upperSite (p : Coord) : Coord :=
  (p.1 - 1, if p.2 = 0 then 0 else p.2 - 1)

/-- The upper site of a face center is a site of the patch. -/
lemma upperSite_isSite {r : ℕ} {p : Coord} (hp : IsFace r p) :
    IsSite r (upperSite p) := by
  rcases p with ⟨a, b⟩
  rcases hp with ⟨⟨hba, har⟩, hmod⟩
  by_cases hb : b = 0 <;> simp [upperSite, IsSite, InPatch, hb] <;> omega

/-- A face contains its upper site. -/
lemma adjacent_upperSite {r : ℕ} {p : Coord} (hp : IsFace r p) :
    Adjacent p (upperSite p) := by
  rcases p with ⟨a, b⟩
  rcases hp with ⟨⟨hba, har⟩, hmod⟩
  by_cases hb : b = 0 <;> simp [upperSite, Adjacent, hb] <;> omega

/-- A face containing the upper site of `p` is not in a later row than `p`. -/
lemma row_le_of_adjacent_upperSite {r : ℕ} {p g : Coord}
    (hp : IsFace r p) (hg : Adjacent g (upperSite p)) : g.1 ≤ p.1 := by
  rcases p with ⟨a, b⟩
  rcases g with ⟨c, d⟩
  rcases hp with ⟨⟨hba, har⟩, hmod⟩
  dsimp [upperSite, Adjacent] at hg ⊢
  omega

/-- The only face in the row of `p` that contains the upper site of `p` is `p`
itself. -/
lemma eq_of_adjacent_upperSite_of_row_eq {r : ℕ} {p g : Coord}
    (hp : IsFace r p) (hg : IsFace r g) (hadj : Adjacent g (upperSite p))
    (hrow : g.1 = p.1) : g = p := by
  rcases p with ⟨a, b⟩
  rcases g with ⟨c, d⟩
  rcases hp with ⟨⟨hba, har⟩, hmod⟩
  rcases hg with ⟨⟨hdc, hcr⟩, hgmod⟩
  apply Prod.ext
  · exact hrow
  · by_cases hb : b = 0 <;> simp [upperSite, Adjacent, hb] at hadj <;> dsimp at * <;> omega

/-- The indicator vectors of the faces are linearly independent over `ZMod 2`:
in a vanishing combination, a face with nonzero coefficient in the earliest
row is the only face with nonzero coefficient at its upper site. -/
theorem linearIndependent_incidence (r : ℕ) :
    LinearIndependent (ZMod 2) (@incidence r) := by
  rw [Fintype.linearIndependent_iff]
  intro c hsum i
  by_contra hi
  obtain ⟨f, hf, hmin⟩ := (Finset.univ.filter fun f => c f ≠ 0).exists_min_image
    (fun f => (faceCoord f).1) ⟨i, by simpa using hi⟩
  have hF := faceCoord_isFace f
  obtain ⟨q, hq⟩ := exists_qubitCoord _ (upperSite_isSite hF)
  have hother : ∀ g ∈ Finset.univ, g ≠ f → c g * incidence g q = 0 := by
    intro g _ hgf
    by_cases hc : c g = 0
    · rw [hc, zero_mul]
    refine mul_eq_zero_of_right _ (if_neg fun hmem => hgf (faceCoord_injective r ?_))
    have ha : Adjacent (faceCoord g) (upperSite (faceCoord f)) :=
      hq ▸ (mem_faceSupport g q).mp hmem
    exact eq_of_adjacent_upperSite_of_row_eq hF (faceCoord_isFace g) ha
      ((row_le_of_adjacent_upperSite hF ha).antisymm (hmin g (by simpa using hc)))
  have hface : incidence f q = 1 :=
    if_pos ((mem_faceSupport f q).mpr (hq ▸ adjacent_upperSite hF))
  have hsumq := congr_fun hsum q
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hsumq
  rw [Finset.sum_eq_single f hother (fun h => (h (Finset.mem_univ f)).elim),
    hface, mul_one] at hsumq
  exact (Finset.mem_filter.mp hf).2 hsumq

/-- The map sending face labels to the corresponding combination of face
checks is injective. -/
theorem checkCombination_injective (r : ℕ) :
    Function.Injective (SelfDual.checkCombination (@incidence r)) := by
  intro c c' h
  apply (linearIndependent_incidence r).fintypeLinearCombination_injective
  ext q
  simpa [Fintype.linearCombination_apply] using congr_fun h q

end Quantum.StabilizerGroup.ColorCode
