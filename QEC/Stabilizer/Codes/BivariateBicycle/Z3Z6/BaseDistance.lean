/-
# Base floor for the [[36,4,4]] pair: `d(base) ≥ 4` in strong form

`base36_strong_floor : coverData.StrongBaseFloor 4` — every nonzero base
1-cycle (logical or stabilizer) has weight ≥ 4.  Proof: exhaustive kernel
sweeps kill weights 1, 2 and 3 (72, 72² and 72³ candidate supports); a
chain of weight `k ≤ 3` over `ZMod 2` is a sum of `k` distinct `δ`-chains
(extracted via the `indF2` indicator machinery of `BBDoubling.lean`).

As a corollary the parametric Theorem-B floor gives the unconditional
cover floor `d(cover) ≥ 4` (`pair72_cover_floor`).

SAT cross-check: `qec-lab:experiments/bb_lab/scripts/gen_pair72_z6z6_data.py`
(base d = 4 exactly; the weight-4 logical is `Witness.lean`'s `uStar36`).
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z3Z6.Defs

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z3Z6

open scoped BigOperators

/-! ## Support extraction: small chains are sums of `δ`-chains -/

private lemma zmod2_ne_zero_eq_one : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by
  decide

/-- The support indicator reproduces the chain (`ZMod 2` values are 0/1). -/
lemma eq_indF2_support {I : Type} [Fintype I] [DecidableEq I]
    (u : I → ZMod 2) :
    u = indF2 (Finset.univ.filter fun i => u i ≠ 0) :=
  self_eq_indF2_filter u

lemma indF2_singleton {I : Type} [DecidableEq I] (p : I) :
    indF2 ({p} : Finset I) = Pi.single p 1 := by
  have h := indF2_insert (a := p) (S := (∅ : Finset I)) (Finset.notMem_empty p)
  rw [Finset.insert_empty] at h
  rw [h, indF2_empty, add_zero]

lemma eq_single_of_card_eq_one {I : Type} [Fintype I] [DecidableEq I]
    {u : I → ZMod 2}
    (h : (Finset.univ.filter fun i => u i ≠ 0).card = 1) :
    ∃ p : I, u = Pi.single p 1 := by
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h
  exact ⟨p, by rw [eq_indF2_support u, hp, indF2_singleton]⟩

lemma eq_two_singles_of_card_eq_two {I : Type} [Fintype I] [DecidableEq I]
    {u : I → ZMod 2}
    (h : (Finset.univ.filter fun i => u i ≠ 0).card = 2) :
    ∃ p q : I, p ≠ q ∧ u = Pi.single p 1 + Pi.single q 1 := by
  obtain ⟨p, q, hpq, hs⟩ := Finset.card_eq_two.mp h
  refine ⟨p, q, hpq, ?_⟩
  rw [eq_indF2_support u, hs,
    indF2_insert (Finset.notMem_singleton.mpr hpq), indF2_singleton]

lemma eq_three_singles_of_card_eq_three {I : Type} [Fintype I] [DecidableEq I]
    {u : I → ZMod 2}
    (h : (Finset.univ.filter fun i => u i ≠ 0).card = 3) :
    ∃ p q r : I, p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
      u = Pi.single p 1 + (Pi.single q 1 + Pi.single r 1) := by
  obtain ⟨p, q, r, hpq, hpr, hqr, hs⟩ := Finset.card_eq_three.mp h
  refine ⟨p, q, r, hpq, hpr, hqr, ?_⟩
  have hp_notmem : p ∉ ({q, r} : Finset I) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    rintro (h1 | h1)
    · exact hpq h1
    · exact hpr h1
  rw [eq_indF2_support u, hs, indF2_insert hp_notmem,
    indF2_insert (Finset.notMem_singleton.mpr hqr), indF2_singleton]

/-! ## The kernel sweeps: no cycle of weight 1, 2 or 3 -/

theorem no_weight_one_cycle :
    ∀ p : G36 × Fin 2, bbBoundary1Fn a36 b36 (Pi.single p 1) ≠ 0 := by
  native_decide

theorem no_weight_two_cycle :
    ∀ p q : G36 × Fin 2, p ≠ q →
      bbBoundary1Fn a36 b36 (Pi.single p 1 + Pi.single q 1) ≠ 0 := by
  native_decide

/-- No cycle is a sum of three `δ`-chains — stated without distinctness
hypotheses (degenerate cases collapse to a single `δ`-chain in char 2, and
those have nonzero boundary too), which keeps the `Decidable` instance
simple. -/
theorem no_weight_three_cycle :
    ∀ p q r : G36 × Fin 2,
      bbBoundary1Fn a36 b36
        (Pi.single p 1 + (Pi.single q 1 + Pi.single r 1)) ≠ 0 := by
  native_decide

/-! ## The strong base floor -/

/-- **`d(base) ≥ 4` in strong small-cycle form**: every nonzero base
1-cycle has weight ≥ 4. -/
theorem base36_strong_floor : coverData.StrongBaseFloor 4 := by
  intro u hu hne
  by_contra hlt
  push Not at hlt
  rw [coverData.baseComplex_chainWeight_eq] at hlt
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have hi' : u i ≠ 0 := by simpa using hi
  have hpos : 0 < (Finset.univ.filter fun j => u j ≠ 0).card :=
    Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'⟩⟩
  have hcases : (Finset.univ.filter fun j => u j ≠ 0).card = 1 ∨
      (Finset.univ.filter fun j => u j ≠ 0).card = 2 ∨
      (Finset.univ.filter fun j => u j ≠ 0).card = 3 := by
    omega
  rcases hcases with h1 | h2 | h3
  · obtain ⟨p, rfl⟩ := eq_single_of_card_eq_one h1
    exact no_weight_one_cycle p hu
  · obtain ⟨p, q, hpq, rfl⟩ := eq_two_singles_of_card_eq_two h2
    exact no_weight_two_cycle p q hpq hu
  · obtain ⟨p, q, r, _, _, _, rfl⟩ := eq_three_singles_of_card_eq_three h3
    exact no_weight_three_cycle p q r hu

/-! ## The unconditional Theorem-B cover floor -/

/-- **`d(cover) ≥ 4`, unconditionally**: every nontrivial cycle of the
`[[72,4,8]]` cover complex has weight ≥ 4 (the parametric Theorem-B floor
instantiated on `base36_strong_floor`). -/
theorem pair72_cover_floor :
    ∀ v : G72 × Fin 2 → ZMod 2,
      v ∈ coverData.coverComplex.cycles →
      v ∉ coverData.coverComplex.boundaries →
      4 ≤ coverData.coverComplex.chainWeight v :=
  coverData.chainWeight_ge_of_strongBaseFloor base36_strong_floor

end Z3Z6
end BB
end Homological
end Stabilizer
end Quantum
