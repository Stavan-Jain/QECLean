import QEC.Stabilizer.Framework.Homological.Distance
import QEC.Stabilizer.Codes.Toric.LogicalCorrespondenceX
import QEC.Stabilizer.Codes.Toric.WrappingInvariants

/-!
# The X-distance of the toric code is `L`

On chains:

* `le_edgeWeight_of_not_mem_toricBoundaries`: a cycle that is not a boundary
  has weight at least `L`. One of its wrapping numbers is nonzero, so it has an
  odd number of horizontal edges in each of the `L` columns, or an odd number
  of vertical edges in each of the `L` rows.
* `loopChain_mem_toricBoundaries_iff`, `edgeWeight_loopChain_one_zero`,
  `edgeWeight_loopChain_zero_one`: the horizontal loop `loopChain L 1 0` and
  the vertical loop `loopChain L 0 1` are not boundaries and have weight `L`.

On operators:

* `horizontalLoopXOperator L` and `verticalLoopXOperator L` are the X-chain
  operators of the two loops: X-type nontrivial logical operators of weight
  `L`.
* `HasToricXDistance L d` says that `d` is the least weight of an X-type
  nontrivial logical operator of the toric code, and `toricCodeN_dX_eq_L` that
  this distance is `L`.
-/

namespace Quantum
namespace Stabilizer
namespace Lattice

open scoped ToricChain
open Homological

/-! ## Nontrivial cycles have weight at least `L` -/

/-- A 1-chain that is nonzero on `L` distinct edges has weight at least `L`. -/
lemma le_edgeWeight_of_injective {L : ℕ} {c : C1 L} {e : Fin L → EdgeIdx L}
    (he : Function.Injective e) (h : ∀ i, c (e i) ≠ 0) : L ≤ edgeWeight c := by
  simpa [edgeWeight] using Finset.card_le_card_of_injOn (s := Finset.univ) (t := edgeSupport c) e
    (fun i _ => Finset.mem_coe.2 ((mem_edgeSupport _ _).2 (h i))) he.injOn

/-- A 1-chain with odd horizontal-edge parity in every column has weight at
least `L`: it has a horizontal edge in each of the `L` columns. -/
lemma le_edgeWeight_of_forall_hAt_ne_zero {L : ℕ} {c : C1 L} (h : ∀ x, hAt L x c ≠ 0) :
    L ≤ edgeWeight c := by
  choose y _ hy using fun x => Finset.exists_ne_zero_of_sum_ne_zero (h x)
  exact le_edgeWeight_of_injective (e := fun x => EdgeIdx.h x (y x))
    (fun _ _ hab => (EdgeIdx.h.inj hab).1) hy

/-- A 1-chain with odd vertical-edge parity in every row has weight at least
`L`: it has a vertical edge in each of the `L` rows. -/
lemma le_edgeWeight_of_forall_vAt_ne_zero {L : ℕ} {c : C1 L} (h : ∀ y, vAt L y c ≠ 0) :
    L ≤ edgeWeight c := by
  choose x _ hx using fun y => Finset.exists_ne_zero_of_sum_ne_zero (h y)
  exact le_edgeWeight_of_injective (e := fun y => EdgeIdx.v (x y) y)
    (fun _ _ hab => (EdgeIdx.v.inj hab).2) hx

variable (L : ℕ) [Fact (0 < L)]

variable {L} in
/-- A cycle that is not a boundary has weight at least `L`: one of its wrapping
numbers is nonzero, and that parity is the same in every column or row. -/
theorem le_edgeWeight_of_not_mem_toricBoundaries {c : C1 L} (hc : c ∈ Z₁ L) (hb : c ∉ B₁ L) :
    L ≤ edgeWeight c := by
  rcases not_and_or.1 (mt (mem_toricBoundaries_iff_wrap_eq_zero L ⟨c, hc⟩).2 hb) with h | h
  · exact le_edgeWeight_of_forall_hAt_ne_zero fun x =>
      (hAt_independent_on_cycles L ⟨c, hc⟩ x (zeroCoord L)).trans_ne h
  · exact le_edgeWeight_of_forall_vAt_ne_zero fun y =>
      (vAt_independent_on_cycles L ⟨c, hc⟩ y (zeroCoord L)).trans_ne h

/-! ## The loops -/

/-- `loopChain L a b` is a boundary only for `a = b = 0`. -/
lemma loopChain_mem_toricBoundaries_iff (a b : ZMod 2) :
    loopChain L a b ∈ B₁ L ↔ a = 0 ∧ b = 0 :=
  (mem_toricBoundaries_iff_wrap_eq_zero L ⟨_, loopChain_mem_toricCycles L a b⟩).trans
    (by simp [hWrap, vWrap, hAt, vAt, loopChain])

/-- The horizontal loop `loopChain L 1 0` consists of the `L` horizontal edges
of one row. -/
lemma edgeWeight_loopChain_one_zero : edgeWeight (loopChain L 1 0) = L := by
  have h : edgeSupport (loopChain L 1 0) =
      Finset.univ.image fun x => EdgeIdx.h x (zeroCoord L) := by
    ext e
    cases e <;> simp [loopChain, eq_comm]
  rw [edgeWeight, h, Finset.card_image_of_injective _ fun _ _ h => (EdgeIdx.h.inj h).1,
    Finset.card_univ, Fintype.card_fin]

/-- The vertical loop `loopChain L 0 1` consists of the `L` vertical edges of
one column. -/
lemma edgeWeight_loopChain_zero_one : edgeWeight (loopChain L 0 1) = L := by
  have h : edgeSupport (loopChain L 0 1) =
      Finset.univ.image fun y => EdgeIdx.v (zeroCoord L) y := by
    ext e
    cases e <;> simp [loopChain, eq_comm]
  rw [edgeWeight, h, Finset.card_image_of_injective _ fun _ _ h => (EdgeIdx.v.inj h).2,
    Finset.card_univ, Fintype.card_fin]

/-- The X-chain operator of `c` has the weight of `c`. -/
lemma weight_toricXOperatorOfChain (c : C1 L) :
    NQubitPauliGroupElement.weight (toricXOperatorOfChain L c) = edgeWeight c :=
  HomologicalCode.weight_chainXOperator (X := toricHomologicalCode L) c

end Lattice
end Stabilizer

namespace StabilizerGroup
namespace ToricCodeN

open NQubitPauliGroupElement Stabilizer.Lattice
open scoped ToricChain

/-! ## The X-distance -/

/-- `HasToricXDistance L d`: every X-type nontrivial logical operator of the
`L × L` toric code has weight at least `d`, and weight `d` is attained. -/
def HasToricXDistance (L d : ℕ) [Fact (2 ≤ L)] : Prop :=
  d ≥ 1 ∧
  (∀ g : NQubitPauliGroupElement (numQubits L),
      NQubitPauliGroupElement.IsXTypeElement g →
      IsNontrivialLogicalOperator g (stabilizerGroup L) →
      0 < weight g →
      weight g ≥ d) ∧
  (∃ g : NQubitPauliGroupElement (numQubits L),
      NQubitPauliGroupElement.IsXTypeElement g ∧
      IsNontrivialLogicalOperator g (stabilizerGroup L) ∧
      weight g = d)

/-- The horizontal X-loop: `X` on the horizontal edges of the row
`zeroCoord L`. -/
def horizontalLoopXOperator (L : ℕ) [Fact (0 < L)] : NQubitPauliGroupElement (numQubits L) :=
  toricXOperatorOfChain L (loopChain L 1 0)

/-- The vertical X-loop: `X` on the vertical edges of the column
`zeroCoord L`. -/
def verticalLoopXOperator (L : ℕ) [Fact (0 < L)] : NQubitPauliGroupElement (numQubits L) :=
  toricXOperatorOfChain L (loopChain L 0 1)

lemma horizontalLoopXOperator_isXType (L : ℕ) [Fact (0 < L)] :
    IsXTypeElement (horizontalLoopXOperator L) :=
  toricXOperatorOfChain_isXType L _

lemma verticalLoopXOperator_isXType (L : ℕ) [Fact (0 < L)] :
    IsXTypeElement (verticalLoopXOperator L) :=
  toricXOperatorOfChain_isXType L _

variable (L : ℕ) [Fact (2 ≤ L)]

/-- The horizontal X-loop is a nontrivial logical operator. -/
theorem horizontalLoopXOperator_isNontrivialLogical :
    IsNontrivialLogicalOperator (horizontalLoopXOperator L) (stabilizerGroup L) :=
  (toricXOperatorOfChain_isNontrivialLogical_iff L _).2 ⟨loopChain_mem_toricCycles L 1 0,
    fun h => one_ne_zero ((loopChain_mem_toricBoundaries_iff L 1 0).1 h).1⟩

/-- The vertical X-loop is a nontrivial logical operator. -/
theorem verticalLoopXOperator_isNontrivialLogical :
    IsNontrivialLogicalOperator (verticalLoopXOperator L) (stabilizerGroup L) :=
  (toricXOperatorOfChain_isNontrivialLogical_iff L _).2 ⟨loopChain_mem_toricCycles L 0 1,
    fun h => one_ne_zero ((loopChain_mem_toricBoundaries_iff L 0 1).1 h).2⟩

/-- The horizontal X-loop has weight `L`. -/
lemma weight_horizontalLoopXOperator : weight (horizontalLoopXOperator L) = L :=
  (weight_toricXOperatorOfChain L _).trans (edgeWeight_loopChain_one_zero L)

/-- The vertical X-loop has weight `L`. -/
lemma weight_verticalLoopXOperator : weight (verticalLoopXOperator L) = L :=
  (weight_toricXOperatorOfChain L _).trans (edgeWeight_loopChain_zero_one L)

/-- There is an X-type nontrivial logical operator of weight `L`: the
horizontal X-loop. -/
theorem exists_nontrivial_x_logical_weight_eq_L :
    ∃ g : NQubitPauliGroupElement (numQubits L),
      NQubitPauliGroupElement.IsXTypeElement g ∧
      IsNontrivialLogicalOperator g (stabilizerGroup L) ∧
      weight g = L :=
  ⟨horizontalLoopXOperator L, horizontalLoopXOperator_isXType L,
    horizontalLoopXOperator_isNontrivialLogical L, weight_horizontalLoopXOperator L⟩

/-- Every X-type nontrivial logical operator has weight at least `L`: it is
the X-chain operator of a cycle that is not a boundary. -/
theorem nontrivial_x_logical_weight_ge_L (g : NQubitPauliGroupElement (numQubits L))
    (hgX : NQubitPauliGroupElement.IsXTypeElement g)
    (hgLogical : IsNontrivialLogicalOperator g (stabilizerGroup L)) :
    weight g ≥ L := by
  obtain ⟨c, rfl⟩ : ∃ c, toricXOperatorOfChain L c = g := ⟨_, toricXOperatorOfChain_xChainOf L hgX⟩
  obtain ⟨hc, hb⟩ := (toricXOperatorOfChain_isNontrivialLogical_iff L c).1 hgLogical
  rw [weight_toricXOperatorOfChain]
  exact le_edgeWeight_of_not_mem_toricBoundaries hc hb

/-- The X-distance of the toric code is `L`. -/
theorem toricCodeN_dX_eq_L : HasToricXDistance L L :=
  ⟨le_trans one_le_two Fact.out, fun g hgX hgLogical _ =>
    nontrivial_x_logical_weight_ge_L L g hgX hgLogical, exists_nontrivial_x_logical_weight_eq_L L⟩

end ToricCodeN
end StabilizerGroup
end Quantum
