import QEC.Stabilizer.Codes.Color.Geometry
import QEC.Stabilizer.Codes.Color.FaceParity

/-!
# Orthogonality of triangular color-code face checks

Two distinct faces have a paired intersection: reflection in their midpoint
exchanges the endpoints of their common edge. The reflection stays inside the
triangular patch, including its boundaries.
-/

namespace Quantum.StabilizerGroup.ColorCode

open scoped BigOperators

/-- Reflection of a lattice site in the midpoint of two face centers. -/
def midpointReflect (f g q : Coord) : Coord :=
  (f.1 + g.1 - q.1, f.2 + g.2 - q.2)

set_option maxHeartbeats 800000 in
-- The six neighbor choices for each of the two faces give 36 arithmetic cases.
/-- A common neighbor of distinct faces has a distinct reflected common
neighbor in the patch, and reflecting twice recovers the original site. -/
theorem midpointReflect_properties {r : ℕ} (f g q : Coord)
    (hf : IsFace r f) (hg : IsFace r g) (hne : f ≠ g)
    (hq : IsSite r q) (hfq : Adjacent f q) (hgq : Adjacent g q) :
    IsSite r (midpointReflect f g q) ∧
      Adjacent f (midpointReflect f g q) ∧
      Adjacent g (midpointReflect f g q) ∧
      midpointReflect f g q ≠ q ∧
      midpointReflect f g (midpointReflect f g q) = q := by
  rcases f with ⟨a, b⟩
  rcases g with ⟨c, d⟩
  rcases q with ⟨x, y⟩
  rcases hf with ⟨⟨hba, har⟩, hfm⟩
  rcases hg with ⟨⟨hdc, hcr⟩, hgm⟩
  rcases hq with ⟨⟨hyx, hxr⟩, hqm⟩
  dsimp at hba har hfm hdc hcr hgm hyx hxr hqm
  have hne' : a ≠ c ∨ b ≠ d := by
    by_contra h
    apply hne
    apply Prod.ext <;> tauto
  dsimp only [Adjacent] at hfq hgq
  dsimp only [IsSite, InPatch, midpointReflect, Adjacent]
  simp only [ne_eq, Prod.mk.injEq]
  rcases hfq with h | h | h | h | h | h <;>
    rcases hgq with h' | h' | h' | h' | h' | h' <;> omega

/-- Distinct face checks have zero binary inner product. -/
theorem incidence_orthogonal_of_ne {r : ℕ} (f g : Face r) (hne : f ≠ g) :
    ∑ q, incidence f q * incidence g q = 0 := by
  classical
  have hsum : (∑ q ∈ faceSupport f ∩ faceSupport g, (1 : ZMod 2)) = 0 := by
    have hp (q : Qubit r) (hq : q ∈ faceSupport f ∩ faceSupport g) :=
      midpointReflect_properties _ _ _ (faceCoord_isFace f) (faceCoord_isFace g)
        (fun h => hne (faceCoord_injective r h)) (qubitCoord_isSite q)
        ((mem_faceSupport f q).mp (Finset.mem_inter.mp hq).1)
        ((mem_faceSupport g q).mp (Finset.mem_inter.mp hq).2)
    apply sum_one_eq_zero_of_coord_pairing _ (midpointReflect (faceCoord f) (faceCoord g))
    · exact fun q hq => (hp q hq).1
    · intro q hq p heq
      simp only [Finset.mem_inter, mem_faceSupport, heq]
      exact ⟨(hp q hq).2.1, (hp q hq).2.2.1⟩
    · exact fun q hq => (hp q hq).2.2.2.1
    · exact fun q hq => (hp q hq).2.2.2.2
  calc
    (∑ q, incidence f q * incidence g q) =
        ∑ q ∈ faceSupport f ∩ faceSupport g, incidence f q * incidence g q := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro q _ hq
      simp only [Finset.mem_inter, not_and_or] at hq
      rcases hq with hq | hq <;> simp only [incidence, if_neg hq, zero_mul, mul_zero]
    _ = ∑ q ∈ faceSupport f ∩ faceSupport g, (1 : ZMod 2) := by
      apply Finset.sum_congr rfl
      intro q hq
      simp only [incidence, if_pos (Finset.mem_inter.mp hq).1,
        if_pos (Finset.mem_inter.mp hq).2, mul_one]
    _ = 0 := hsum

/-- All face incidence vectors are mutually orthogonal over the binary field. -/
theorem incidence_orthogonal {r : ℕ} (f g : Face r) :
    ∑ q, incidence f q * incidence g q = 0 := by
  obtain rfl | hne := eq_or_ne f g
  · exact incidence_self_orthogonal f
  · exact incidence_orthogonal_of_ne f g hne

end Quantum.StabilizerGroup.ColorCode
