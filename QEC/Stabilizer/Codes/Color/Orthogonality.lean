import QEC.Stabilizer.Codes.Color.FaceParity

/-!
# Orthogonality of the face checks of the color code

Two distinct faces share an even number of qubits: the point reflection in the
midpoint of their centers, `midpointReflect`, maps the common qubits to common
qubits without fixed points (`midpointReflect_properties`). Together with the
evenness of each face this makes the indicator vectors of the faces mutually
orthogonal over `ZMod 2` (`incidence_orthogonal`), which is the commutation of
the X-checks with the Z-checks.
-/

namespace Quantum.StabilizerGroup.ColorCode

open scoped BigOperators

/-- The point reflection of `q` in the midpoint of `f` and `g`. -/
def midpointReflect (f g q : Coord) : Coord :=
  (f.1 + g.1 - q.1, f.2 + g.2 - q.2)

set_option maxHeartbeats 800000 in
-- The six neighbors of each of the two faces give 36 arithmetic goals.
/-- `midpointReflect` maps the common qubits of two distinct faces to common
qubits, without fixed points and involutively. -/
lemma midpointReflect_properties {r : ℕ} (f g q : Coord)
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
  have hne' : a ≠ c ∨ b ≠ d := not_and_or.mp fun h => hne (Prod.ext h.1 h.2)
  dsimp only [Adjacent] at hfq hgq
  dsimp only [IsSite, InPatch, midpointReflect, Adjacent]
  simp only [ne_eq, Prod.mk.injEq]
  rcases hfq with h | h | h | h | h | h <;>
    rcases hgq with h' | h' | h' | h' | h' | h' <;> omega

/-- The indicator vectors of two distinct faces are orthogonal over `ZMod 2`:
the faces share an even number of qubits. -/
lemma incidence_orthogonal_of_ne {r : ℕ} (f g : Face r) (hne : f ≠ g) :
    ∑ q, incidence f q * incidence g q = 0 := by
  have hp (q : Qubit r) (hq : q ∈ faceSupport f ∩ faceSupport g) :=
    midpointReflect_properties _ _ _ (faceCoord_isFace f) (faceCoord_isFace g)
      (fun h => hne (faceCoord_injective r h)) (qubitCoord_isSite q)
      ((mem_faceSupport f q).mp (Finset.mem_inter.mp hq).1)
      ((mem_faceSupport g q).mp (Finset.mem_inter.mp hq).2)
  rw [sum_incidence_mul_incidence]
  refine sum_one_eq_zero_of_coord_pairing _ (midpointReflect (faceCoord f) (faceCoord g))
    (fun q hq => (hp q hq).1) (fun q hq p heq => ?_)
    (fun q hq => (hp q hq).2.2.2.1) (fun q hq => (hp q hq).2.2.2.2)
  simp only [Finset.mem_inter, mem_faceSupport, heq]
  exact ⟨(hp q hq).2.1, (hp q hq).2.2.1⟩

/-- The indicator vectors of the faces are mutually orthogonal over
`ZMod 2`. -/
theorem incidence_orthogonal {r : ℕ} (f g : Face r) :
    ∑ q, incidence f q * incidence g q = 0 := by
  obtain rfl | hne := eq_or_ne f g
  · exact incidence_self_orthogonal f
  · exact incidence_orthogonal_of_ne f g hne

end Quantum.StabilizerGroup.ColorCode
