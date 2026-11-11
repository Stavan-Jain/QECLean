import QEC.Stabilizer.Codes.Color.Geometry

/-!
# Faces of the color code have an even number of qubits

A set of qubits that is invariant under a fixed-point-free involution of the
lattice coordinates has even cardinality (`sum_one_eq_zero_of_coord_pairing`).
Every face has such an involution, `faceReflection`: the point reflection in
the center for an interior face, and a reflection that preserves the side for
a face on a side of the patch. Hence every face has an even number of qubits
(`faceSupport_sum_one`), and its indicator vector is orthogonal to itself over
`ZMod 2` (`incidence_self_orthogonal`).
-/

namespace Quantum.StabilizerGroup.ColorCode

open scoped BigOperators

/-- A set `s` of qubits has even cardinality if a map `t` of the lattice
coordinates sends the qubits of `s` to qubits of `s`, without fixed points and
involutively. -/
lemma sum_one_eq_zero_of_coord_pairing {r : ℕ} (s : Finset (Qubit r))
    (t : Coord → Coord)
    (hsite : ∀ q ∈ s, IsSite r (t (qubitCoord q)))
    (hmem : ∀ q ∈ s, ∀ p, qubitCoord p = t (qubitCoord q) → p ∈ s)
    (hne : ∀ q ∈ s, t (qubitCoord q) ≠ qubitCoord q)
    (hinv : ∀ q ∈ s, t (t (qubitCoord q)) = qubitCoord q) :
    (∑ _q ∈ s, (1 : ZMod 2)) = 0 := by
  choose g hg using fun q (hq : q ∈ s) => exists_qubitCoord _ (hsite q hq)
  have hgm (q : Qubit r) (hq : q ∈ s) : g q hq ∈ s := hmem q hq _ (hg q hq)
  refine Finset.sum_involution g (fun _ _ => rfl)
    (fun q hq _ heq => hne q hq ((hg q hq).symm.trans (congrArg qubitCoord heq))) hgm
    fun q hq => qubitCoord_injective r ?_
  rw [hg (g q hq) (hgm q hq), hg q hq, hinv q hq]

/-- The involution of the qubits of the face with center `f`. For a face on a
side of the patch it is a reflection that preserves that side: it fixes the
column on the left side (`column = 0`), exchanges rows and columns on the
diagonal side (`row = column`), and fixes the row on the bottom side
(`row = 3 * r`). For every other face it is the point reflection in `f`. -/
def faceReflection (r : ℕ) (f p : Coord) : Coord :=
  if f.2 = 0 then (2 * f.1 + p.2 - p.1, p.2)
  else if f.1 = f.2 then (2 * f.1 - p.2, 2 * f.1 - p.1)
  else if f.1 = 3 * r then (p.1, 2 * f.2 + p.1 - f.1 - p.2)
  else (2 * f.1 - p.1, 2 * f.2 - p.2)

set_option maxHeartbeats 800000 in
-- The six neighbors and the four cases of `faceReflection` give 24 arithmetic goals.
/-- `faceReflection` maps the qubits of a face to qubits of that face, without
fixed points and involutively. -/
lemma faceReflection_properties {r : ℕ} (f p : Coord) (hf : IsFace r f)
    (hp : IsSite r p) (ha : Adjacent f p) :
    IsSite r (faceReflection r f p) ∧
      Adjacent f (faceReflection r f p) ∧
      faceReflection r f p ≠ p ∧
      faceReflection r f (faceReflection r f p) = p := by
  rcases f with ⟨a, b⟩
  rcases p with ⟨x, y⟩
  rcases hf with ⟨⟨hba, har⟩, hfmod⟩
  rcases hp with ⟨⟨hyx, hxr⟩, -⟩
  dsimp at hba har hfmod hyx hxr
  simp only [Adjacent] at ha
  rcases ha with h | h | h | h | h | h <;> rcases h with ⟨hxa, hyb⟩
  all_goals simp only [faceReflection]
  all_goals split_ifs <;>
    simp only [IsSite, InPatch, Adjacent, Prod.mk.injEq, ne_eq] <;>
    (repeat' apply And.intro) <;> first | trivial | omega

/-- Every face has an even number of qubits. -/
theorem faceSupport_sum_one {r : ℕ} (f : Face r) :
    (∑ _q ∈ faceSupport f, (1 : ZMod 2)) = 0 := by
  have hp (q : Qubit r) (hq : q ∈ faceSupport f) :=
    faceReflection_properties _ _ (faceCoord_isFace f) (qubitCoord_isSite q)
      ((mem_faceSupport f q).mp hq)
  exact sum_one_eq_zero_of_coord_pairing _ (faceReflection r (faceCoord f))
    (fun q hq => (hp q hq).1)
    (fun q hq p hpq => (mem_faceSupport f p).mpr (hpq ▸ (hp q hq).2.1))
    (fun q hq => (hp q hq).2.2.1) (fun q hq => (hp q hq).2.2.2)

/-- The indicator vector of a face is orthogonal to itself over `ZMod 2`. -/
lemma incidence_self_orthogonal {r : ℕ} (f : Face r) :
    (∑ q, incidence f q * incidence f q) = 0 := by
  rw [sum_incidence_mul_incidence, Finset.inter_self]
  exact faceSupport_sum_one f

end Quantum.StabilizerGroup.ColorCode
