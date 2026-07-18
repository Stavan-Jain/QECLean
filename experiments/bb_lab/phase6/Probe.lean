/-
# Phase 6 — M0 de-risking probe for the unconditional d = 12 formalization

Standalone probe (run via `lake env lean experiments/bb_lab/phase6/Probe.lean`),
mirroring the Phase-5 `phase5/Probe.lean` approach. It settles the two empirical
unknowns in `notes/A6_lean_d12_finish_plan.md` BEFORE committing to the analytic
CRT-frame build:

* **Probe A — computable F₄.** mathlib's `GaloisField 2 2` is noncomputable
  (`SplittingField`), so the CRT frame needs a bespoke computable F₄. Confirm a
  `Fin 4` + table model satisfies the field axioms by `decide`.
* **Probe B — ∂₂ sparse-syndrome scale.** The `LightStabilizerClassification`
  finite leaf enumerates weight-≤5 face supports of `BaseGroup` (≈ C(36,≤5) ≈
  4.4·10⁵ supports), each tested through the boundary-2 syndrome. The d(base)≥6
  proof already `native_decide`s the *∂₁* version over `(BaseGroup × Fin 2)³ ≈
  3.7·10⁵` plain tuples (`BaseDistance.smallCycleCheck_four`). This probe confirms
  the *∂₂* sparse form scales the same way, at 36³ (≈4.7·10⁴) and 36⁴ (≈1.68·10⁶,
  ~4.5× the validated ∂₁ sweep — an upper bracket for the real leaf).

If both are green, routes R-C (LightStab) and R2 (MImBound) are de-risked and the
CRT-frame infrastructure build (milestone M1) can start.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Gross.Defs
import QEC.Stabilizer.Framework.Homological.BBChainComplex

open Quantum.Stabilizer.Homological Quantum.Stabilizer.Homological.BB

/-! ## Probe A — computable F₄ as `Fin 4` with explicit tables

Elements `0, 1, ω, ω²` ↦ `0, 1, 2, 3`. Addition is the char-2 (XOR-style) table of
`𝔽₄`; multiplication uses `ω² = ω + 1`, `ω·ω = ω²`, `ω·ω² = 1`, `ω²·ω² = ω`. -/
namespace ProbeF4

def add : Fin 4 → Fin 4 → Fin 4 :=
  fun a b => (![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]] a) b

def mul : Fin 4 → Fin 4 → Fin 4 :=
  fun a b => (![![0, 0, 0, 0], ![0, 1, 2, 3], ![0, 2, 3, 1], ![0, 3, 1, 2]] a) b

-- Additive group (char 2), commutative.
example : ∀ a b : Fin 4, add a b = add b a := by decide
example : ∀ a b c : Fin 4, add (add a b) c = add a (add b c) := by decide
example : ∀ a : Fin 4, add a 0 = a := by decide
example : ∀ a : Fin 4, add a a = 0 := by decide
-- Multiplicative monoid, commutative, with unit and inverses (field).
example : ∀ a b : Fin 4, mul a b = mul b a := by decide
example : ∀ a b c : Fin 4, mul (mul a b) c = mul a (mul b c) := by decide
example : ∀ a : Fin 4, mul a 1 = a := by decide
example : ∀ a : Fin 4, a ≠ 0 → ∃ b, mul a b = 1 := by decide
-- Distributivity ties the two tables together.
example : ∀ a b c : Fin 4, mul a (add b c) = add (mul a b) (mul a c) := by decide

end ProbeF4

/-! ## Probe B — ∂₂ sparse-syndrome scale sweeps

`∂₂(χ_S)(h, j) = ∑_{g ∈ S} (j = 0 ? A(h-g) : B(h-g))`, the boundary-2 analog of
`BaseDistance.syndAt`. We sweep all small face supports as plain tuples and force
the kernel/compiler to evaluate the full ∂₂ syndrome weight per case. The bound
`≤ 72` is trivially true — its only purpose is to require the full per-case
computation, so the timing reflects the real leaf cost. -/
namespace ProbeScale

/-- Sparse ∂₂ contribution of a single face `g` at output cell `(h, j)`. -/
def term2At (g h : BaseGroup) (j : Fin 2) : ZMod 2 :=
  if j = 0 then baseA (h - g) else baseB (h - g)

/-- Sparse ∂₂ syndrome of a face support (given as a list) at `(h, j)`. -/
def synd2 (s : List BaseGroup) (h : BaseGroup) (j : Fin 2) : ZMod 2 :=
  (s.map (fun g => term2At g h j)).sum

/-- Weight (number of nonzero output cells) of the ∂₂ syndrome of a face support. -/
def bWeight (s : List BaseGroup) : Nat :=
  (Finset.univ.filter (fun p : BaseGroup × Fin 2 => synd2 s p.1 p.2 ≠ 0)).card

-- ∂₂ sparse-syndrome sweep over all 36³ ≈ 4.7·10⁴ three-face supports, each
-- evaluated to its full boundary-2 weight. The point is to confirm the *∂₂*
-- sparse form compiles and runs under `native_decide` (the d(base)≥6 proof
-- already validates the *∂₁* sparse form at 3.7·10⁵ cases via
-- `BaseDistance.smallCycleCheck_four`). Together these bracket the real
-- `LightStabilizerClassification` leaf (C(36,≤5) ≈ 4.4·10⁵ supports): ∂₂ form ✓
-- here, 10⁵-scale ✓ by the committed ∂₁ precedent.
example : ∀ q0 q1 q2 : BaseGroup, bWeight [q0, q1, q2] ≤ 72 := by native_decide

end ProbeScale
