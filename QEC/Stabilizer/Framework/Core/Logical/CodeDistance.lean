import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode
import QEC.Stabilizer.Framework.Core.Logical.LogicalOperators
import QEC.Stabilizer.Foundations.PauliGroup.NQubitElement

/-!
# Code distance `[[n, k, d]]`

The distance `d` of a stabilizer code is the minimum weight of a nontrivial
logical operator: a centralizer element whose operator part is not that of any
stabilizer. A code of distance `d` detects every error of weight less than `d`
and corrects every error of weight less than `d / 2`.

- `HasCodeDistance C d`: `d ≥ 1`, every nontrivial logical operator of positive
  weight has weight at least `d`, and some nontrivial logical operator has
  weight exactly `d`;
- `hasCodeDistance_of`, `hasCodeDistance_of_isLeast`: two ways to establish
  `HasCodeDistance`;
- `StabilizerCodeWithDistance n k d`: a stabilizer code bundled with a proof
  that its distance is `d`.
-/

namespace Quantum
namespace StabilizerGroup

variable {n k : ℕ}

open NQubitPauliGroupElement

/-- The code `C` has distance `d`: `d ≥ 1`, every nontrivial logical operator of
positive weight has weight at least `d`, and some nontrivial logical operator
has weight exactly `d`. -/
def HasCodeDistance (C : StabilizerCode n k) (d : ℕ) : Prop :=
  d ≥ 1 ∧
  (∀ g, IsNontrivialLogicalOperator g C.toStabilizerGroup → 0 < weight g → weight g ≥ d) ∧
  (∃ g, IsNontrivialLogicalOperator g C.toStabilizerGroup ∧ weight g = d)

/-- A code distance is at least `1`. -/
theorem HasCodeDistance.one_le_d (C : StabilizerCode n k) (d : ℕ) (h : HasCodeDistance C d) :
    d ≥ 1 :=
  h.1

/-- If `C` has distance `d`, every nontrivial logical operator of positive
weight has weight at least `d`. -/
theorem HasCodeDistance.min_weight (C : StabilizerCode n k) (d : ℕ)
    (h : HasCodeDistance C d) (g : NQubitPauliGroupElement n)
    (hg : IsNontrivialLogicalOperator g C.toStabilizerGroup) (hw : 0 < weight g) :
    weight g ≥ d :=
  h.2.1 g hg hw

/-- If `C` has distance `d`, some nontrivial logical operator has weight `d`. -/
theorem HasCodeDistance.exists_weight_eq (C : StabilizerCode n k) (d : ℕ)
    (h : HasCodeDistance C d) :
    ∃ g, IsNontrivialLogicalOperator g C.toStabilizerGroup ∧ weight g = d :=
  h.2.2

/-- To prove `HasCodeDistance C d` it suffices to show `d ≥ 1`, exhibit a
nontrivial logical operator of weight `d`, and show that no Pauli element of
weight `w` with `1 ≤ w < d` is a nontrivial logical operator. -/
theorem hasCodeDistance_of (C : StabilizerCode n k) (d : ℕ)
    (hd : d ≥ 1)
    (h_witness : ∃ g, IsNontrivialLogicalOperator g C.toStabilizerGroup ∧ weight g = d)
    (h_min : ∀ w, 1 ≤ w → w < d → ∀ g, weight g = w →
      ¬IsNontrivialLogicalOperator g C.toStabilizerGroup) :
    HasCodeDistance C d :=
  ⟨hd, fun g hg hw => not_lt.mp fun h => h_min (weight g) hw h g rfl hg, h_witness⟩

/-- If `d` is the least weight of a nontrivial logical operator of a stabilizer
group `S` with the same subgroup as the code `C`, then `C` has distance `d`;
`d ≥ 1` because a nontrivial logical operator has positive weight. -/
theorem hasCodeDistance_of_isLeast (C : StabilizerCode n k)
    {S : StabilizerGroup n} {d : ℕ}
    (hS : C.toStabilizerGroup.toSubgroup = S.toSubgroup)
    (hleast : IsLeast {w : ℕ | ∃ g : NQubitPauliGroupElement n,
      IsNontrivialLogicalOperator g S ∧ weight g = w} d) :
    HasCodeDistance C d := by
  obtain ⟨g, hg, rfl⟩ := hleast.1
  exact ⟨hg.weight_pos,
    fun g' hg' _ => hleast.2 ⟨g', (IsNontrivialLogicalOperator_of_toSubgroup_eq g' hS).mp hg', rfl⟩,
    g, (IsNontrivialLogicalOperator_of_toSubgroup_eq g hS).mpr hg, rfl⟩

/-!
## `StabilizerCodeWithDistance`: the full `[[n, k, d]]` packaging

`StabilizerCode n k` carries the first two parameters of `[[n, k, d]]`. Distance
is the separate proposition `HasCodeDistance`, so that a code can be formalized
before its distance is established. `StabilizerCodeWithDistance` bundles the
two, giving a single object with all three parameters in its type.
-/

/-- A stabilizer code together with a proof that its distance is `d`. -/
structure StabilizerCodeWithDistance (n k d : ℕ) extends StabilizerCode n k where
  /-- The underlying stabilizer code has distance exactly `d`. -/
  hasDistance : HasCodeDistance toStabilizerCode d

namespace StabilizerCodeWithDistance

variable {n k d : ℕ}

/-- A code with distance `d` satisfies `d ≥ 1`. -/
theorem one_le_d (C : StabilizerCodeWithDistance n k d) : 1 ≤ d :=
  C.hasDistance.1

/-- Every nontrivial logical operator of positive weight has weight at least
`d`. -/
theorem min_weight (C : StabilizerCodeWithDistance n k d)
    (g : NQubitPauliGroupElement n)
    (hg : IsNontrivialLogicalOperator g C.toStabilizerCode.toStabilizerGroup)
    (hw : 0 < weight g) :
    weight g ≥ d :=
  C.hasDistance.2.1 g hg hw

/-- Some nontrivial logical operator has weight exactly `d`. -/
theorem exists_weight_eq (C : StabilizerCodeWithDistance n k d) :
    ∃ g, IsNontrivialLogicalOperator g C.toStabilizerCode.toStabilizerGroup ∧
         weight g = d :=
  C.hasDistance.2.2

end StabilizerCodeWithDistance

end StabilizerGroup
end Quantum
