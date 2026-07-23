/-
# A21: the weight-6 coset sweeps (`native_decide` leaves)

The five translation-reduced sweeps discharging the weight-6 split map
of `weight6_cycle_is_boundary` (`BaseFloor.lean`), plus the kernel
weight fact for the one-sided splits.  Soundness rests on the coset
structure: a cycle's `u_R` over a fixed `u_L` ranges over the 16-element
coset `wAB ⋆ u_L + kerElt` (`kerA_classify`), so per normalized `u_L`
only 16 candidates exist — the sweeps check all of them.

Quantifiers run over ALL translates `t`, `t₁`, `t₂` (degenerate values
included — the numpy emitter verified the degenerate slots hold, so no
side hypotheses are needed and the soundness argument passes raw
support cells).  Ground truth and falsify-first verification:
`qec-lab:experiments/bb_lab/scripts/a21_gen_basefloor_data.py`
(the sweep facts S0–S2′ in its header).

Measured cost (2026-07-22): `sweepA3` ≈ 1.6 s per `t₁`-slice — ≈ 2–3
min total; everything else is sub-second.  Keep this file a leaf so
iteration elsewhere does not re-pay it.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Z5Z15F2A6.BaseFloorKernel

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z5Z15F2A6

set_option maxRecDepth 4096

/-- **S0**: no kernel-span element has weight 6 (nonzero elements all
weigh 40).  Kills the one-sided splits `(0,6)` and `(6,0)`. -/
lemma kerElt_card_ne_six : ∀ e1 e2 e3 e4 : ZMod 2,
    (Finset.univ.filter fun g : G150 =>
      kerElt e1 e2 e3 e4 g ≠ 0).card ≠ 6 := by
  native_decide

/-- **S1** `(1,5)` kill: no candidate `u_R` over `u_L = δ₀` has
weight 5. -/
lemma sweepA1 : ∀ e1 e2 e3 e4 : ZMod 2,
    (Finset.univ.filter fun g : G150 =>
      wABf g + kerElt e1 e2 e3 e4 g ≠ 0).card ≠ 5 := by
  native_decide

/-- **S2** `(2,4)` kill: no candidate `u_R` over a normalized weight-2
`u_L = χ_{0,t}` has weight 4 (all `t`, degenerate included). -/
lemma sweepA2 : ∀ t : G150, ∀ e1 e2 e3 e4 : ZMod 2,
    (Finset.univ.filter fun g : G150 =>
      wABf g + wABf (g - t) + kerElt e1 e2 e3 e4 g ≠ 0).card ≠ 4 := by
  native_decide

/-- **S3** `(3,3)` classification: every weight-3 candidate `u_R` over a
normalized weight-3 `u_L = χ_{0,t₁,t₂}` pairs with it into a generator
column `∂₂ δ_t` (fires at exactly 6 ordered `(t₁, t₂)` slots). -/
lemma sweepA3 : ∀ t₁ t₂ : G150, ∀ e1 e2 e3 e4 : ZMod 2,
    (Finset.univ.filter fun g : G150 =>
        wABf g + wABf (g - t₁) + wABf (g - t₂)
          + kerElt e1 e2 e3 e4 g ≠ 0).card = 3 →
    ∃ t : G150,
      (∀ g : G150,
        (if g = 0 ∨ g = t₁ ∨ g = t₂ then (1 : ZMod 2) else 0)
          = a150 (g - t))
      ∧ ∀ g : G150,
          wABf g + wABf (g - t₁) + wABf (g - t₂)
            + kerElt e1 e2 e3 e4 g = b150 (g - t) := by
  native_decide

/-- **S1′** `(5,1)` kill: no candidate `u_L` over `u_R = δ₀` has
weight 5 (`B`-side mirror through `wBA`). -/
lemma sweepB1 : ∀ e1 e2 e3 e4 : ZMod 2,
    (Finset.univ.filter fun g : G150 =>
      wBAf g + kerElt e1 e2 e3 e4 g ≠ 0).card ≠ 5 := by
  native_decide

/-- **S2′** `(4,2)` kill: no candidate `u_L` over a normalized weight-2
`u_R = χ_{0,t}` has weight 4. -/
lemma sweepB2 : ∀ t : G150, ∀ e1 e2 e3 e4 : ZMod 2,
    (Finset.univ.filter fun g : G150 =>
      wBAf g + wBAf (g - t) + kerElt e1 e2 e3 e4 g ≠ 0).card ≠ 4 := by
  native_decide

end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum
