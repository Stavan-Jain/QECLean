import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.History

/-!
# The unconditional cyclic distance lower bound

Every open-history coordinate is a sum of at most `s+1` physical cyclic
coordinates. Averaging the Pascal lower bound over all translations therefore
gives `3^(s+1) ≤ 2*(s+1)*weight(c)` for each nonzero seed word.
-/

namespace Quantum.Stabilizer.Homological.BB.Fractal

open Polynomial
open scoped BigOperators

/-- Each open-history coordinate has a fixed list of at most `s+1` physical
offsets, valid for every functional and every cyclic translation. -/
theorem history_coordinate_taps (s : ℕ) (e : HistoryIndex s) :
    ∃ taps : List ℕ, taps.length ≤ s + 1 ∧
      ∀ (f : Module.Dual (ZMod 2) (SeedAlgebra s)) (j : SeedIndex s),
        openHistory s (shiftedFunctional s f j) e =
          ∑ i : Fin taps.length, functionalWord s f (j + (taps.get i : SeedIndex s)) := by
  have hroot : AdjoinRoot.mk (checkPolynomial (s + 1)) (1 + Polynomial.X) =
      AdjoinRoot.mk (checkPolynomial (s + 1)) Polynomial.X ^ width (s + 1) := by
    simpa only [map_add, map_one, AdjoinRoot.mk_X, seedRoot] using (seedRoot_width s).symm
  obtain ⟨taps, hlen, hsum⟩ := historyFunctional_map_eq_sum_powers
    (AdjoinRoot.mk (checkPolynomial (s + 1))) (s + 1) e.1 e.2
    (Nat.succ_pos s) e.1.isLt hroot
  refine ⟨taps, hlen, ?_⟩
  intro f j
  rw [openHistory, initialPolynomial_history_coeff, hsum, map_list_sum, List.map_map]
  rw [← Fin.sum_univ_fun_getElem]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_apply, functionalWord_apply, seedPower_add, seedPower_natCast,
    List.get_eq_getElem, AdjoinRoot.mk_X]
  rfl

/-- The full open history has at most twice as many sites as the cyclic word. -/
theorem history_card_le_twice_seed (s : ℕ) :
    Fintype.card (HistoryIndex s) ≤ 2 * Fintype.card (SeedIndex s) := by
  simp only [HistoryIndex, Fintype.card_prod, Fintype.card_fin, SeedIndex, ZMod.card]
  have hq : 2 ≤ width (s + 1) := two_le_width (Nat.succ_pos s)
  have hperiod : period (s + 1) + 1 = width (s + 1) ^ 2 := by
    unfold period
    apply Nat.sub_add_cancel
    nlinarith
  have hrow : (2 * width (s + 1) - 1) + 1 = 2 * width (s + 1) :=
    Nat.sub_add_cancel (by omega)
  nlinarith

/-- Every nonzero functional word satisfies the unconditional fractal distance
floor, with the logarithmic loss coming only from dyadic truncation. -/
theorem functionalWord_weight_lower (s : ℕ)
    (f : Module.Dual (ZMod 2) (SeedAlgebra s)) (hf : f ≠ 0) :
    3 ^ (s + 1) ≤ 2 * (s + 1) * hammingNorm (functionalWord s f) := by
  classical
  choose taps hlen htaps using history_coordinate_taps s
  let lengths : HistoryIndex s → ℕ := fun e => (taps e).length
  let offsets : ∀ e : HistoryIndex s, Fin (lengths e) → SeedIndex s :=
    fun e i => ((taps e).get i : SeedIndex s)
  have heq (j : SeedIndex s) :
      openHistory s (shiftedFunctional s f j) =
        sparseObservation lengths offsets (functionalWord s f) j := by
    funext e
    exact htaps e f j
  apply sparse_observation_lower_bound lengths offsets (functionalWord s f)
    (3 ^ (s + 1)) (s + 1)
  · intro j
    rw [← heq]
    exact openHistory_weight_ge s _ (shiftedFunctional_ne_zero s f hf j)
  · exact hlen
  · exact history_card_le_twice_seed s

/-- Every nonzero word in the concrete trinomial seed space satisfies the
proved lower bound used by the BB distance theorem. -/
theorem seedSpace_weight_lower (s : ℕ) (c : SeedIndex s → ZMod 2)
    (hc : c ∈ seedSpace s) (h0 : c ≠ 0) :
    3 ^ (s + 1) ≤ 2 * (s + 1) * hammingNorm c := by
  obtain ⟨f, rfl⟩ := hc
  apply functionalWord_weight_lower s f
  intro hf
  apply h0
  rw [hf, map_zero]

end Quantum.Stabilizer.Homological.BB.Fractal
