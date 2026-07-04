/-
# The [[36,4,4]] → [[72,4,8]] doubling pair over `Z₃×Z₆ → Z₆×Z₆` — definitions

The second full instance of the free-ℤ₂ doubling template
(`Framework/Homological/BBDoubling.lean`), outside the gross lineage:

* **base** `[[36,4,4]]` on `G36 = Z₃ × Z₆`, `A = x² + y + y³`,
  `B = 1 + x + y²` (the verified pair of
  `docs/gross-distance-extensibility.md` §5);
* **cover** `[[72,4,8]]` on `G72 = Z₆ × Z₆`, same polynomials, free ℤ₂
  cover doubling `x` (deck `σ = ·x³`).

This file instantiates the two chain complexes and the parametric cover
bundle `coverData : XDoubleCoverData G72 G36`.  All finite obligations are
discharged by kernel computation; the offline provenance (SAT distances,
seam census, witness search) is
`experiments/bb_lab/scripts/gen_pair72_z6z6_data.py`
(data: `experiments/bb_lab/data/a9/pair72_z6z6_data.json`).

Note the cover group `Z₆ × Z₆` coincides with the *base* group of the gross
pair (`BB.BaseGroup`); this development consistently uses the local names
`G36`/`G72` and never mixes the two instantiations.

## Convention bridge (lab notes → repo)

Repo convention: `∂₂ f = (A⋆f | B⋆f)`, `∂₁ c = B⋆c_L + A⋆c_R`; cycle
condition `B⋆v_L = A⋆v_R`.  **Repo-left = lab-right.**
-/

import QEC.Stabilizer.Framework.Homological.BBDoubling

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z3Z6

/-! ## Groups -/

/-- The base group `Z₃ × Z₆` (`x` has order 3, `y` has order 6). -/
abbrev G36 : Type := ZMod 3 × ZMod 6

/-- The cover group `Z₆ × Z₆` (free ℤ₂ cover of `G36` doubling `x`). -/
abbrev G72 : Type := ZMod 6 × ZMod 6

/-! ## Polynomials -/

/-- Base `A = x² + y + y³`. -/
def a36 : G36 → ZMod 2 := fun g =>
  if g = (2, 0) ∨ g = (0, 1) ∨ g = (0, 3) then 1 else 0

/-- Base `B = 1 + x + y²`. -/
def b36 : G36 → ZMod 2 := fun g =>
  if g = (0, 0) ∨ g = (1, 0) ∨ g = (0, 2) then 1 else 0

/-- Cover `A = x² + y + y³` (over `Z₆ × Z₆`). -/
def a72 : G72 → ZMod 2 := fun g =>
  if g = (2, 0) ∨ g = (0, 1) ∨ g = (0, 3) then 1 else 0

/-- Cover `B = 1 + x + y²` (over `Z₆ × Z₆`). -/
def b72 : G72 → ZMod 2 := fun g =>
  if g = (0, 0) ∨ g = (1, 0) ∨ g = (0, 2) then 1 else 0

/-! ## Chain complexes -/

/-- The base `[[36,4,4]]` chain complex. -/
noncomputable def pair36Complex : HomologicalCode := bbChainComplex a36 b36

/-- The cover `[[72,4,8]]` chain complex. -/
noncomputable def pair72Complex : HomologicalCode := bbChainComplex a72 b72

theorem pair36Complex_numQubits : pair36Complex.numQubits = 36 := by
  change bbNumQubits G36 = 36
  unfold bbNumQubits
  rw [Fintype.card_prod, ZMod.card, ZMod.card]

theorem pair72Complex_numQubits : pair72Complex.numQubits = 72 := by
  change bbNumQubits G72 = 72
  unfold bbNumQubits
  rw [Fintype.card_prod, ZMod.card]

/-! ## The cover bundle -/

/-- The parametric cover data: projection `Z₆×Z₆ →+ Z₃×Z₆` (reduce `x`
mod 3), deck `x³ = (3,0)`, canonical section, and the two polynomial
pairs.  (Computable — the kernel sweeps of the sibling files evaluate
through it.) -/
def coverData : XDoubleCoverData G72 G36 where
  proj := AddMonoidHom.prodMap
    (ZMod.castHom (by norm_num : (3 : ℕ) ∣ 6) (ZMod 3)).toAddMonoidHom
    (AddMonoidHom.id (ZMod 6))
  deckS := (3, 0)
  sec := fun p => ((p.1.val : ZMod 6), p.2)
  Ac := a72
  Bc := b72
  Ab := a36
  Bb := b36
  deckS_ne_zero := by decide
  proj_fiber := by native_decide
  proj_sec := by native_decide
  push_A := by native_decide
  push_B := by native_decide

lemma coverData_coverComplex : coverData.coverComplex = pair72Complex := rfl

lemma coverData_baseComplex : coverData.baseComplex = pair36Complex := rfl

end Z3Z6
end BB
end Homological
end Stabilizer
end Quantum
