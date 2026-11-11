import QEC.Stabilizer.Codes.Color.Logicals

/-!
# A logical operator on the left side of the color-code patch

The chain `leftBoundary r` is supported on the qubits in column `0`, the left
side of the triangular patch. It is a cycle (`leftBoundary_mem_cycles`): the
qubits of a face on the left side are paired by a reflection of the column,
so there is an even number of them. It has `2 * r + 1` qubits
(`leftBoundary_weight`), an odd number, so it pairs to `1` with the all-ones
cycle and is not a boundary (`leftBoundary_not_mem_boundaries`). Its X-chain
operator is therefore a nontrivial logical operator of weight `distance r`.
-/

namespace Quantum.StabilizerGroup.ColorCode

open scoped BigOperators
open Stabilizer.Homological

/-- The qubits on the left side of the patch: those in column `0`. -/
def leftBoundarySupport (r : ℕ) : Finset (Qubit r) :=
  Finset.univ.filter fun q => (qubitCoord q).2 = 0

/-- The chain supported on the left side of the patch. -/
def leftBoundary (r : ℕ) (q : Qubit r) : ZMod 2 :=
  if (qubitCoord q).2 = 0 then 1 else 0

/-! ## The left side has `2 * r + 1` qubits -/

/-- There are `2 * r + 1` numbers `x ≤ 3 * r` with `x % 3 ≠ 2`. -/
private lemma count_mod_three_ne_two (r : ℕ) :
    Nat.count (fun x => x % 3 ≠ 2) (3 * r + 1) = 2 * r + 1 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have h1 : (3 * r + 1) % 3 ≠ 2 := by omega
    have h2 : ¬(3 * r + 1 + 1) % 3 ≠ 2 := by omega
    have h3 : (3 * r + 1 + 1 + 1) % 3 ≠ 2 := by omega
    rw [show 3 * (r + 1) + 1 = 3 * r + 1 + 1 + 1 + 1 by ring, Nat.count_succ, Nat.count_succ,
      Nat.count_succ, ih, if_pos h1, if_neg h2, if_pos h3]
    omega

/-- The left side of the patch has `2 * r + 1` qubits: the row of a qubit
identifies them with the rows `x ≤ 3 * r` such that `(x, 0)` is a site. -/
theorem leftBoundarySupport_card (r : ℕ) :
    (leftBoundarySupport r).card = distance r := by
  rw [distance, ← count_mod_three_ne_two, Nat.count_eq_card_filter_range]
  refine Finset.card_bij (fun q _ => (qubitCoord q).1) (fun q hq => ?_)
    (fun q hq q' hq' h => qubitCoord_injective r (Prod.ext h
      ((Finset.mem_filter.mp hq).2.trans (Finset.mem_filter.mp hq').2.symm)))
    fun x hx => ?_
  · have hs := qubitCoord_isSite q
    have h0 : (qubitCoord q).2 = 0 := (Finset.mem_filter.mp hq).2
    simp only [IsSite, InPatch, h0] at hs
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  · obtain ⟨hx, hmod⟩ := Finset.mem_filter.mp hx
    obtain ⟨q, hq⟩ := exists_qubitCoord (r := r) (x, 0)
      ⟨⟨Nat.zero_le _, Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)⟩, hmod⟩
    exact ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrArg Prod.snd hq⟩,
      congrArg Prod.fst hq⟩

/-- The left-side chain has odd parity. -/
lemma leftBoundary_sum_one (r : ℕ) : ∑ q, leftBoundary r q = 1 :=
  (Finset.sum_boole _ _).trans <|
    (congrArg Nat.cast (leftBoundarySupport_card r)).trans <|
      ZMod.natCast_eq_one_iff_odd.mpr (distance_odd r)

/-! ## The left side is a cycle -/

/-- The reflection of column `0` that pairs the left-side qubits of the face
with center `f`. -/
private def leftBoundaryReflection (f p : Coord) : Coord :=
  (2 * f.1 - f.2 - p.1, 0)

/-- `leftBoundaryReflection` maps the left-side qubits of a face to left-side
qubits of that face, without fixed points and involutively. -/
private lemma leftBoundaryReflection_properties {r : ℕ} (f p : Coord)
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

/-- The left-side chain is a cycle: every face has an even number of qubits on
the left side. -/
theorem leftBoundary_mem_cycles (r : ℕ) :
    leftBoundary r ∈ (homologicalCode r).cycles := by
  refine (mem_cycles_iff_sum_faceSupport _).mpr fun f => ?_
  have hp (q : Qubit r) (hq : q ∈ (faceSupport f).filter fun q => (qubitCoord q).2 = 0) :=
    leftBoundaryReflection_properties _ _ (faceCoord_isFace f) (qubitCoord_isSite q)
      ((mem_faceSupport f q).mp (Finset.mem_filter.mp hq).1) (Finset.mem_filter.mp hq).2
  exact (Finset.sum_filter _ fun _ => (1 : ZMod 2)).symm.trans
    (sum_one_eq_zero_of_coord_pairing _ (leftBoundaryReflection (faceCoord f))
      (fun q hq => (hp q hq).1)
      (fun q hq p hpq => Finset.mem_filter.mpr
        ⟨(mem_faceSupport f p).mpr (hpq ▸ (hp q hq).2.1), congrArg Prod.snd hpq⟩)
      (fun q hq => (hp q hq).2.2.1) fun q hq => (hp q hq).2.2.2)

/-- The left-side chain is a dual cycle. -/
lemma leftBoundary_mem_dualCycles (r : ℕ) :
    leftBoundary r ∈ (homologicalCode r).dualCycles :=
  (dualCycles_eq_cycles r).symm ▸ leftBoundary_mem_cycles r

/-! ## Weight and nontriviality -/

/-- The support of the left-side chain is the left side of the patch. -/
lemma leftBoundary_chainSupport (r : ℕ) :
    (homologicalCode r).chainSupport (leftBoundary r) = leftBoundarySupport r := by
  change Finset.univ.filter (fun q : Qubit r => leftBoundary r q ≠ 0) =
    Finset.univ.filter (fun q : Qubit r => (qubitCoord q).2 = 0)
  ext q
  simp [leftBoundary]

/-- The left-side chain has weight `2 * r + 1`. -/
theorem leftBoundary_weight (r : ℕ) :
    (homologicalCode r).chainWeight (leftBoundary r) = distance r := by
  rw [HomologicalCode.chainWeight, leftBoundary_chainSupport]
  exact leftBoundarySupport_card r

/-- The left-side chain is not a boundary: it pairs to `1` with the all-ones
dual cycle. -/
theorem leftBoundary_not_mem_boundaries (r : ℕ) :
    leftBoundary r ∉ (homologicalCode r).boundaries :=
  HomologicalCode.not_mem_boundaries_of_dual_witness (X := homologicalCode r) (w := allOnes r)
    (allOnes_mem_dualCycles r) (by simpa only [allOnes, one_mul] using leftBoundary_sum_one r)

end Quantum.StabilizerGroup.ColorCode
