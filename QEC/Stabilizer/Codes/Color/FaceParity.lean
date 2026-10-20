import QEC.Stabilizer.Codes.Color.Geometry

/-!
# Even color-code faces

Every honeycomb face has a fixed-point-free reflection of its physical sites.
The reflection axis is chosen along the boundary for a clipped face and through
the center for an interior face. Pairing the sites proves even incidence parity.
-/

namespace Quantum.StabilizerGroup.ColorCode

open scoped BigOperators

/-- A coordinate pairing makes the binary cardinality of a support vanish. -/
theorem sum_one_eq_zero_of_coord_pairing {r : ℕ} (s : Finset (Qubit r))
    (t : Coord → Coord)
    (hsite : ∀ q ∈ s, IsSite r (t (qubitCoord q)))
    (hmem : ∀ q ∈ s, ∀ p, qubitCoord p = t (qubitCoord q) → p ∈ s)
    (hne : ∀ q ∈ s, t (qubitCoord q) ≠ qubitCoord q)
    (hinv : ∀ q ∈ s, t (t (qubitCoord q)) = qubitCoord q) :
    (∑ _q ∈ s, (1 : ZMod 2)) = 0 := by
  classical
  let g (q : Qubit r) (hq : q ∈ s) : Qubit r :=
    Classical.choose (exists_qubitCoord (t (qubitCoord q)) (hsite q hq))
  have hg (q : Qubit r) (hq : q ∈ s) : qubitCoord (g q hq) = t (qubitCoord q) :=
    Classical.choose_spec (exists_qubitCoord (t (qubitCoord q)) (hsite q hq))
  have hgm (q : Qubit r) (hq : q ∈ s) : g q hq ∈ s := hmem q hq _ (hg q hq)
  refine Finset.sum_involution g ?_ ?_ hgm ?_
  · intro q hq
    decide
  · intro q hq _ heq
    exact hne q hq ((hg q hq).symm.trans (congrArg qubitCoord heq))
  · intro q hq
    apply qubitCoord_injective r
    rw [hg (g q hq) (hgm q hq), hg q hq, hinv q hq]

/-- A reflection preserving the sites of an interior or boundary face. -/
def faceReflection (r : ℕ) (f p : Coord) : Coord :=
  if f.2 = 0 then (2 * f.1 + p.2 - p.1, p.2)
  else if f.1 = f.2 then (2 * f.1 - p.2, 2 * f.1 - p.1)
  else if f.1 = 3 * r then (p.1, 2 * f.2 + p.1 - f.1 - p.2)
  else (2 * f.1 - p.1, 2 * f.2 - p.2)

set_option maxHeartbeats 800000 in
-- The six neighbor directions and four boundary cases require 24 arithmetic checks.
/-- Reflection pairs the physical sites of each face without fixed points. -/
theorem faceReflection_properties {r : ℕ} (f p : Coord) (hf : IsFace r f)
    (hp : IsSite r p) (ha : Adjacent f p) :
    IsSite r (faceReflection r f p) ∧
      Adjacent f (faceReflection r f p) ∧
      faceReflection r f p ≠ p ∧
      faceReflection r f (faceReflection r f p) = p := by
  rcases f with ⟨a, b⟩
  rcases p with ⟨x, y⟩
  rcases hf with ⟨⟨hba, har⟩, hfmod⟩
  rcases hp with ⟨⟨hyx, hxr⟩, hpmod⟩
  dsimp at hba har hfmod hyx hxr hpmod
  clear hpmod
  simp only [Adjacent] at ha
  rcases ha with h | h | h | h | h | h <;> rcases h with ⟨hxa, hyb⟩
  all_goals simp only [faceReflection]
  all_goals split_ifs <;>
    simp only [IsSite, InPatch, Adjacent, Prod.mk.injEq, ne_eq] <;>
    (repeat' apply And.intro) <;> first | trivial | omega

/-- The number of qubits on a face is zero as an element of `ZMod 2`. -/
theorem faceSupport_sum_one {r : ℕ} (f : Face r) :
    (∑ _q ∈ faceSupport f, (1 : ZMod 2)) = 0 := by
  apply sum_one_eq_zero_of_coord_pairing (faceSupport f) (faceReflection r (faceCoord f))
  · intro q hq
    exact (faceReflection_properties _ _ (faceCoord_isFace f)
      (qubitCoord_isSite q) ((mem_faceSupport f q).mp hq)).1
  · intro q hq p hp
    rw [mem_faceSupport, hp]
    exact (faceReflection_properties _ _ (faceCoord_isFace f)
      (qubitCoord_isSite q) ((mem_faceSupport f q).mp hq)).2.1
  · intro q hq
    exact (faceReflection_properties _ _ (faceCoord_isFace f)
      (qubitCoord_isSite q) ((mem_faceSupport f q).mp hq)).2.2.1
  · intro q hq
    exact (faceReflection_properties _ _ (faceCoord_isFace f)
      (qubitCoord_isSite q) ((mem_faceSupport f q).mp hq)).2.2.2

/-- A face incidence vector is self-orthogonal over `ZMod 2`. -/
theorem incidence_self_orthogonal {r : ℕ} (f : Face r) :
    (∑ q, incidence f q * incidence f q) = 0 := by
  classical
  have h : (∑ q, incidence f q * incidence f q) =
      ∑ _q ∈ faceSupport f, (1 : ZMod 2) := by
    simp only [incidence, faceSupport, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q _
    split_ifs <;> norm_num
  exact h.trans (faceSupport_sum_one f)

end Quantum.StabilizerGroup.ColorCode
