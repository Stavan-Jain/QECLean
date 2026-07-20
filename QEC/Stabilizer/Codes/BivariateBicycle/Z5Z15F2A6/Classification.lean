/-
# Z5Z15F2A6 — the light-boundary classification interface

The single certificate hypothesis of the (M) kernel route, and the two
kernel lemmas that gate the dispatch:

* `LightClassification` — every nonzero base boundary of weight ≤ 14 is a
  base translate of one of the 113 tabulated class representatives.  This
  is the exhaustive-enumeration completeness statement (a 2⁷⁵-quantified
  Prop): certified by the SAT enumeration with translation-orbit blocking
  (final UNSAT = completeness, 9.6 h; Φ-closure cross-check;
  `qec-lab:experiments/bb_lab/data/a17/f2a6_light_classes.jsonl`;
  DRAT upgrade path = kissat on the blocked n = 75 CNF).
* `boundary_chainWeight_even` — every boundary has even weight (the
  parity gate turning "≤ 15" into "≤ 14" in the dispatch), by the
  `funLiftF2` basis lift from the generated `parity_basis_certs`.
* `proj_lift` — every base translation lifts through the covering
  projection (the input `weight_floor_translate1_reduce` needs to walk
  the whole translation orbit).
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.CertSweep

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z5Z15F2A6

open scoped BigOperators

set_option maxRecDepth 4096

/-- **The light-boundary classification** — the certificate hypothesis:
every nonzero boundary of the `[[150,8,8]]` base with weight ≤ 14 is a
base translate of one of the 113 class representatives. -/
def LightClassification : Prop :=
  ∀ f : G150 → ZMod 2, bbBoundary2Fn a150 b150 f ≠ 0 →
    (Finset.univ.filter fun j : G150 × Fin 2 =>
      bbBoundary2Fn a150 b150 f j ≠ 0).card ≤ 14 →
    ∃ i : Fin 113, ∃ c : G150,
      bbBoundary2Fn a150 b150 f = translate1 c (repChain i)

/-! ## Parity of boundary weights -/

/-- The `ZMod 2` sum of a chain is its weight mod 2. -/
lemma sum_eq_chainWeight_zmod2 (u : G150 × Fin 2 → ZMod 2) :
    (∑ j : G150 × Fin 2, u j)
      = ((Finset.univ.filter fun j : G150 × Fin 2 => u j ≠ 0).card
          : ZMod 2) := by
  rw [← Finset.sum_filter_ne_zero]
  have hone : ∀ j ∈ Finset.univ.filter
      (fun j : G150 × Fin 2 => u j ≠ 0), u j = 1 := by
    intro j hj
    have hj' : u j ≠ 0 := (Finset.mem_filter.mp hj).2
    have hkey : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
    exact hkey _ hj'
  rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **Every boundary has even weight**: the `ZMod 2` weight of `∂₂ f`
vanishes for every 2-chain `f` (basis lift of the generated parity
certificates). -/
theorem boundary_sum_zero (f : G150 → ZMod 2) :
    (∑ j : G150 × Fin 2, bbBoundary2Fn a150 b150 f j) = 0 := by
  refine funLiftF2
    (fun f => ∑ j : G150 × Fin 2, bbBoundary2Fn a150 b150 f j)
    (fun _ => (0 : ZMod 2)) ?_ rfl ?_ ?_ parity_basis_certs f
  · show (∑ j : G150 × Fin 2, bbBoundary2Fn a150 b150 0 j) = 0
    have h0 : bbBoundary2Fn a150 b150 (0 : G150 → ZMod 2) = 0 := by
      have h : (bbChainComplex a150 b150).boundary2 0 = 0 := map_zero _
      exact h
    rw [h0]
    exact Finset.sum_const_zero
  · intro a b
    show (∑ j : G150 × Fin 2, bbBoundary2Fn a150 b150 (a + b) j)
      = (∑ j : G150 × Fin 2, bbBoundary2Fn a150 b150 a j)
        + (∑ j : G150 × Fin 2, bbBoundary2Fn a150 b150 b j)
    rw [bbBoundary2Fn_add]
    simp only [Pi.add_apply]
    exact Finset.sum_add_distrib
  · intro a b
    show (0 : ZMod 2) = 0 + 0
    rw [add_zero]

/-- The parity gate: a boundary of weight ≤ 15 has weight ≤ 14. -/
theorem boundary_chainWeight_le_14 (f : G150 → ZMod 2)
    (h15 : (Finset.univ.filter fun j : G150 × Fin 2 =>
      bbBoundary2Fn a150 b150 f j ≠ 0).card ≤ 15) :
    (Finset.univ.filter fun j : G150 × Fin 2 =>
      bbBoundary2Fn a150 b150 f j ≠ 0).card ≤ 14 := by
  have heven : ((Finset.univ.filter fun j : G150 × Fin 2 =>
      bbBoundary2Fn a150 b150 f j ≠ 0).card : ZMod 2) = 0 := by
    rw [← sum_eq_chainWeight_zmod2]
    exact boundary_sum_zero f
  have hdvd : 2 ∣ (Finset.univ.filter fun j : G150 × Fin 2 =>
      bbBoundary2Fn a150 b150 f j ≠ 0).card :=
    (CharP.cast_eq_zero_iff (ZMod 2) 2 _).mp heven
  omega

/-! ## Lifting base translations through the projection -/

/-- The canonical lift of a base translation. -/
def liftEl (c : G150) : G300 := (c.1, (c.2.val : ZMod 30))

/-- Every base translation lifts through the covering projection. -/
lemma proj_lift : ∀ c : G150, coverData.proj (liftEl c) = c := by
  native_decide

end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum
