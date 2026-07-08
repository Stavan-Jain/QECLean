/-
# The [[150,8,8]] → [[300,8,16]] doubling pair over `Z₅×Z₁₅ → Z₅×Z₃₀` — definitions

The first `d ≥ 7` instance of the free-ℤ₂ doubling template
(`Framework/Homological/BBDoubling.lean`), from the A15 hunt
(`experiments/bb_lab/notes/A15_d7plus_doubling_hunt_plan.md` §6.1):

* **base** `[[150,8,8]]` on `G150 = Z₅ × Z₁₅`, `A = 1 + y + x`,
  `B = xy⁶ + xy¹⁰ + x²y¹²` (corpus instance `f2a6f17e1c41ff96`,
  `bb_neigh_z5z15_f2a6f17e`; `d(base) = 8` by SAT);
* **cover** `[[300,8,16]]` on `G300 = Z₅ × Z₃₀`, the literal-lift
  polynomials (same exponent supports), free ℤ₂ cover doubling `y`
  (deck `σ = ·y¹⁵`).

This is the tightness cell of the A15 docket: its safe floor is
S4-certified at `16 = 2d` (CryptoMiniSat XOR-native `UNSAT@14` on the
seam-coset orbit rep + the parity lemma; kissat cross-proof with a DRAT
certificate), and the cover ladder's weight-16 witness pins the safe
minimum at exactly `16`.  This file instantiates the two chain complexes
and the parametric cover bundle `coverData : XDoubleCoverData G300 G150`;
all finite obligations are discharged by kernel computation.  The offline
provenance (SAT distances, certificates, witness search) is
`experiments/bb_lab/scripts/gen_f2a6_z5z30_data.py`
(data: `experiments/bb_lab/data/a15/f2a6_z5z30_lean_data.json`).

## Convention bridge (lab → repo)

Repo convention: `∂₂ f = (A⋆f | B⋆f)`, `∂₁ c = B⋆c_L + A⋆c_R`; cycle
condition `B⋆v_L = A⋆v_R`.  Lab `H_Z`-kernel vectors translate to repo
cycles by the global reflection `g ↦ −g` (blocks unchanged); the
generator script performs and re-verifies that translation.
-/

import QEC.Stabilizer.Framework.Homological.BBDoubling

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace Z5Z15F2A6

-- Defeq checks through the `bbChainComplex` structure projections unfold
-- deep `Prod`/`ZMod` instance chains (same as the gross instantiation,
-- `CoverTransfer.lean`; the `Z₃₀` factor is one notch past the default).
set_option maxRecDepth 4096

/-! ## Groups -/

/-- The base group `Z₅ × Z₁₅` (`x` has order 5, `y` has order 15). -/
abbrev G150 : Type := ZMod 5 × ZMod 15

/-- The cover group `Z₅ × Z₃₀` (free ℤ₂ cover of `G150` doubling `y`). -/
abbrev G300 : Type := ZMod 5 × ZMod 30

/-! ## Polynomials -/

/-- Base `A = 1 + y + x`. -/
def a150 : G150 → ZMod 2 := fun g =>
  if g = (0, 0) ∨ g = (0, 1) ∨ g = (1, 0) then 1 else 0

/-- Base `B = xy⁶ + xy¹⁰ + x²y¹²`. -/
def b150 : G150 → ZMod 2 := fun g =>
  if g = (1, 6) ∨ g = (1, 10) ∨ g = (2, 12) then 1 else 0

/-- Cover `A = 1 + y + x` (the literal lift, over `Z₅ × Z₃₀`). -/
def a300 : G300 → ZMod 2 := fun g =>
  if g = (0, 0) ∨ g = (0, 1) ∨ g = (1, 0) then 1 else 0

/-- Cover `B = xy⁶ + xy¹⁰ + x²y¹²` (the literal lift, over `Z₅ × Z₃₀`). -/
def b300 : G300 → ZMod 2 := fun g =>
  if g = (1, 6) ∨ g = (1, 10) ∨ g = (2, 12) then 1 else 0

/-! ## Chain complexes -/

/-- The base `[[150,8,8]]` chain complex. -/
noncomputable def base150Complex : HomologicalCode := bbChainComplex a150 b150

/-- The cover `[[300,8,16]]` chain complex. -/
noncomputable def cover300Complex : HomologicalCode := bbChainComplex a300 b300

theorem base150Complex_numQubits : base150Complex.numQubits = 150 := by
  change bbNumQubits G150 = 150
  unfold bbNumQubits
  rw [Fintype.card_prod, ZMod.card, ZMod.card]

theorem cover300Complex_numQubits : cover300Complex.numQubits = 300 := by
  change bbNumQubits G300 = 300
  unfold bbNumQubits
  rw [Fintype.card_prod, ZMod.card, ZMod.card]

/-! ## The cover bundle -/

/-- The parametric cover data: projection `Z₅×Z₃₀ →+ Z₅×Z₁₅` (reduce `y`
mod 15), deck `y¹⁵ = (0,15)`, canonical section, and the two polynomial
pairs.  (Computable — the kernel checks of the sibling files evaluate
through it.) -/
def coverData : XDoubleCoverData G300 G150 where
  proj := AddMonoidHom.prodMap
    (AddMonoidHom.id (ZMod 5))
    (ZMod.castHom (by norm_num : (15 : ℕ) ∣ 30) (ZMod 15)).toAddMonoidHom
  deckS := (0, 15)
  sec := fun p => (p.1, (p.2.val : ZMod 30))
  Ac := a300
  Bc := b300
  Ab := a150
  Bb := b150
  deckS_ne_zero := by decide
  proj_fiber := by native_decide
  proj_sec := by native_decide
  push_A := by native_decide
  push_B := by native_decide

lemma coverData_coverComplex : coverData.coverComplex = cover300Complex := rfl

lemma coverData_baseComplex : coverData.baseComplex = base150Complex := rfl

end Z5Z15F2A6
end BB
end Homological
end Stabilizer
end Quantum
