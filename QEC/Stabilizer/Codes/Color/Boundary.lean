import QEC.Stabilizer.Codes.Color.Logicals

/-!
# A boundary logical of the triangular color code

The qubits in the left column meet every face evenly. There are exactly
`2r+1` such qubits, so this boundary chain is a nontrivial logical cycle
of weight equal to the claimed distance parameter.
-/

namespace Quantum.StabilizerGroup.ColorCode

open scoped BigOperators
open Stabilizer.Homological

/-- The physical qubits on the left boundary of the triangle. -/
def leftBoundarySupport (r : ℕ) : Finset (Qubit r) :=
  Finset.univ.filter fun q => (qubitCoord q).2 = 0

/-- The binary chain supported on the left boundary. -/
def leftBoundary (r : ℕ) (q : Qubit r) : ZMod 2 :=
  if (qubitCoord q).2 = 0 then 1 else 0

/-- The left boundary has an apex and two physical sites in each layer. -/
private abbrev LeftBoundaryIndex (r : ℕ) := Unit ⊕ (Fin r ⊕ Fin r)

/-- Enumerate the two leftmost physical sites of each three-row layer. -/
private def leftBoundaryQubit {r : ℕ} : LeftBoundaryIndex r → Qubit r
  | .inl _ => .inl ()
  | .inr (.inl l) => .inr ⟨l, ⟨0, by omega⟩, ⟨0, by omega⟩⟩
  | .inr (.inr l) => .inr ⟨l, ⟨2, by omega⟩, ⟨0, by omega⟩⟩

/-- The left-boundary enumeration does not repeat any physical site. -/
private theorem leftBoundaryQubit_injective (r : ℕ) :
    Function.Injective (@leftBoundaryQubit r) := by
  rintro (u | (l | l)) (u' | (l' | l')) h
  all_goals have hrow := congrArg (fun q => (qubitCoord q).1) h
  all_goals simp only [leftBoundaryQubit, qubitCoord] at hrow
  · cases u
    cases u'
    rfl
  · omega
  · omega
  · omega
  · have hl : l = l' := Fin.ext (by omega)
    subst l'
    rfl
  · omega
  · omega
  · omega
  · have hl : l = l' := Fin.ext (by omega)
    subst l'
    rfl

/-- Every leftmost site occurs in the explicit boundary enumeration. -/
private theorem leftBoundarySupport_eq_image (r : ℕ) :
    leftBoundarySupport r = Finset.univ.image (@leftBoundaryQubit r) := by
  classical
  ext q
  simp only [leftBoundarySupport, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_image]
  constructor
  · intro h
    rcases q with u | ⟨l, k, j⟩
    · cases u
      exact ⟨.inl (), rfl⟩
    · fin_cases k
      · have hj : j.val = 0 := by
          norm_num [qubitCoord] at h
          omega
        refine ⟨.inr (.inl l), ?_⟩
        apply qubitCoord_injective r
        simp [leftBoundaryQubit, qubitCoord, hj]
      · norm_num [qubitCoord] at h
      · have hj : j.val = 0 := by
          norm_num [qubitCoord] at h
          omega
        refine ⟨.inr (.inr l), ?_⟩
        apply qubitCoord_injective r
        simp [leftBoundaryQubit, qubitCoord, hj]
  · rintro ⟨a, rfl⟩
    rcases a with u | (l | l) <;> simp [leftBoundaryQubit, qubitCoord]

/-- The left boundary contains exactly `2r+1` physical qubits. -/
theorem leftBoundarySupport_card (r : ℕ) :
    (leftBoundarySupport r).card = distance r := by
  classical
  rw [leftBoundarySupport_eq_image,
    Finset.card_image_of_injective _ (leftBoundaryQubit_injective r)]
  simp only [Finset.card_univ, LeftBoundaryIndex, Fintype.card_sum,
    Fintype.card_unit, Fintype.card_fin, distance]
  omega

/-- Reflect the left-edge sites adjacent to a face in column zero or one. -/
private def leftBoundaryReflection (f p : Coord) : Coord :=
  (2 * f.1 - f.2 - p.1, 0)

/-- A face pairs its incident left-boundary sites without fixed points. -/
private theorem leftBoundaryReflection_properties {r : ℕ} (f p : Coord)
    (hf : IsFace r f) (hp : IsSite r p) (ha : Adjacent f p) (hy : p.2 = 0) :
    IsSite r (leftBoundaryReflection f p) ∧
      Adjacent f (leftBoundaryReflection f p) ∧
      leftBoundaryReflection f p ≠ p ∧
      leftBoundaryReflection f (leftBoundaryReflection f p) = p := by
  rcases f with ⟨a, b⟩
  rcases p with ⟨x, y⟩
  rcases hf with ⟨⟨hba, har⟩, hfmod⟩
  rcases hp with ⟨⟨hyx, hxr⟩, hpmod⟩
  dsimp at hba har hfmod hyx hxr hpmod hy
  subst y
  simp only [Adjacent] at ha
  rcases ha with h | h | h | h | h | h <;> rcases h with ⟨hxa, hyb⟩
  all_goals
    simp only [leftBoundaryReflection, IsSite, InPatch, Adjacent,
      Prod.mk.injEq, ne_eq]
    (repeat' apply And.intro) <;> first | trivial | omega

/-- Each face meets the left boundary in an even number of sites. -/
theorem leftBoundary_face_sum_zero {r : ℕ} (f : Face r) :
    (∑ q, incidence f q * leftBoundary r q) = 0 := by
  classical
  let s := (faceSupport f).filter fun q => (qubitCoord q).2 = 0
  have hs : (∑ _q ∈ s, (1 : ZMod 2)) = 0 := by
    apply sum_one_eq_zero_of_coord_pairing s (leftBoundaryReflection (faceCoord f))
    · intro q hq
      have h := Finset.mem_filter.mp hq
      exact (leftBoundaryReflection_properties _ _ (faceCoord_isFace f)
        (qubitCoord_isSite q) ((mem_faceSupport f q).mp h.1) h.2).1
    · intro q hq p hp
      have h := Finset.mem_filter.mp hq
      apply Finset.mem_filter.mpr
      constructor
      · rw [mem_faceSupport, hp]
        exact (leftBoundaryReflection_properties _ _ (faceCoord_isFace f)
          (qubitCoord_isSite q) ((mem_faceSupport f q).mp h.1) h.2).2.1
      · rw [hp]
        rfl
    · intro q hq
      have h := Finset.mem_filter.mp hq
      exact (leftBoundaryReflection_properties _ _ (faceCoord_isFace f)
        (qubitCoord_isSite q) ((mem_faceSupport f q).mp h.1) h.2).2.2.1
    · intro q hq
      have h := Finset.mem_filter.mp hq
      exact (leftBoundaryReflection_properties _ _ (faceCoord_isFace f)
        (qubitCoord_isSite q) ((mem_faceSupport f q).mp h.1) h.2).2.2.2
  have heq : (∑ q, incidence f q * leftBoundary r q) =
      ∑ _q ∈ s, (1 : ZMod 2) := by
    simp only [s, faceSupport, incidence, leftBoundary, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q _
    split_ifs <;> norm_num
  exact heq.trans hs

/-- The left-boundary chain has zero face-check syndrome. -/
theorem leftBoundary_mem_cycles (r : ℕ) :
    leftBoundary r ∈ (homologicalCode r).cycles := by
  change (homologicalCode r).boundary1 (leftBoundary r) = 0
  ext f
  change (∑ q, incidence f q * leftBoundary r q) = 0
  exact leftBoundary_face_sum_zero f

/-- Self-duality makes the left boundary a dual cycle as well. -/
theorem leftBoundary_mem_dualCycles (r : ℕ) :
    leftBoundary r ∈ (homologicalCode r).dualCycles := by
  rw [dualCycles_eq_cycles]
  exact leftBoundary_mem_cycles r

/-- The boundary chain has precisely the support of the leftmost column. -/
theorem leftBoundary_chainSupport (r : ℕ) :
    (homologicalCode r).chainSupport (leftBoundary r) = leftBoundarySupport r := by
  classical
  change Finset.univ.filter (fun q : Qubit r => leftBoundary r q ≠ 0) =
    Finset.univ.filter (fun q : Qubit r => (qubitCoord q).2 = 0)
  ext q
  simp [leftBoundary]

/-- The left-boundary logical chain has weight `2r+1`. -/
theorem leftBoundary_weight (r : ℕ) :
    (homologicalCode r).chainWeight (leftBoundary r) = distance r := by
  rw [HomologicalCode.chainWeight, leftBoundary_chainSupport]
  exact leftBoundarySupport_card r

/-- The left-boundary chain has odd binary parity. -/
theorem leftBoundary_sum_one (r : ℕ) : ∑ q, leftBoundary r q = 1 := by
  classical
  have h : (∑ q, leftBoundary r q) =
      ∑ _q ∈ leftBoundarySupport r, (1 : ZMod 2) := by
    simp [leftBoundary, leftBoundarySupport]
  rw [h, Finset.sum_const, nsmul_eq_mul, mul_one, leftBoundarySupport_card]
  simp [distance, show (2 : ZMod 2) = 0 from rfl]

/-- The boundary logical pairs oddly with the transversal logical. -/
theorem leftBoundary_innerProduct_allOnes (r : ℕ) :
    (homologicalCode r).chainInnerProduct (leftBoundary r) (allOnes r) = 1 := by
  simpa only [HomologicalCode.chainInnerProduct, allOnes, mul_one] using
    leftBoundary_sum_one r

/-- Odd pairing with the transversal cycle excludes a stabilizer boundary. -/
theorem leftBoundary_not_mem_boundaries (r : ℕ) :
    leftBoundary r ∉ (homologicalCode r).boundaries := by
  apply HomologicalCode.not_mem_boundaries_of_dual_witness
    (w := allOnes r)
  · exact allOnes_mem_dualCycles r
  · simpa only [allOnes, one_mul] using leftBoundary_sum_one r

end Quantum.StabilizerGroup.ColorCode
