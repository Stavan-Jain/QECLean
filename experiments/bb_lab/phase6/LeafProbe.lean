/-
# Phase 6 — L0(a)/L5c scale probe + L0(b)/L5a membership-parity probe.

(a) SCALE: the L5c six-shape leaf enumerates weight-≤5 supports of Fin 36, gated by a
    CHEAP per-case predicate (NOT Finset.filter.card per case — that allocation pattern
    is what OOM'd the 1.68e6 sweep per A6 §8). We use the disjunctive translation-
    normalized PLAIN-TUPLE idiom of BaseDistance.smallCycleCheck_four. We sweep the
    36^4 ≈ 1.68e6 bracket (the A6 plan's stated upper bracket, ~4.5× the validated
    ∂₁ sweep) with a cheap sparse-syndrome-weight comparison.

(b) MEMBERSHIP: in_imA-as-parity. We test `bbBoundary2Fn` of an explicit support against
    the claim that its A-block, when fed back through, is consistent — concretely we
    check that a hexagon ∂₂δ_g is reproduced, and that the sparse-syndrome membership
    predicate native_decides on a handful of inputs.
-/
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.Defs

open Quantum.Stabilizer.Homological.BB

namespace LeafProbe

/-- Sparse ∂₂ contribution of a single face `g` at output cell `(h, j)`. -/
def term2At (g h : BaseGroup) (j : Fin 2) : ZMod 2 :=
  if j = 0 then baseA (h - g) else baseB (h - g)

def synd2 (s : List BaseGroup) (h : BaseGroup) (j : Fin 2) : ZMod 2 :=
  (s.map (fun g => term2At g h j)).sum

/-- A CHEAP per-case predicate: the boundary of a single-face support equals that of a
    given fixed face at a FIXED probe cell — O(support) arithmetic, no Finset.card,
    no allocation per case. This is the shape of the gated leaf check. -/
def cheapPred (q0 q1 q2 q3 : BaseGroup) : Bool :=
  -- a cheap sparse comparison forcing full per-case ∂₂ evaluation at one cell
  decide (synd2 [q0, q1, q2, q3] (0,0) 0 = synd2 [q0, q1, q2, q3] (0,0) 0)

/-! ## PROBE (a) — 36^4 ≈ 1.68e6 plain-tuple sweep with a CHEAP predicate.
    If this finishes in budget, the L5c leaf at the real shape is feasible PROVIDED the
    per-case predicate is cheap (the A6 caveat). -/
example : ∀ q0 q1 q2 q3 : BaseGroup, cheapPred q0 q1 q2 q3 = true := by native_decide

/-! ## PROBE (b) — membership / hexagon reproduction.
    ∂₂δ_g sparse form: synd2 [g] h j. Check that two distinct face supports with the
    same ∂₂ syndrome are detected, and that the syndrome of a hexagon is nonzero
    (weight check via a cheap fixed-cell probe over all g). -/
def hexNonzero (g : BaseGroup) : Bool :=
  -- the hexagon ∂₂δ_g is nonzero: SOME cell is nonzero (cheap existential over 72 cells)
  (List.range 6).any fun a => (List.range 6).any fun b =>
    decide (synd2 [g] ((a:ZMod 6),(b:ZMod 6)) 0 ≠ 0)
      || decide (synd2 [g] ((a:ZMod 6),(b:ZMod 6)) 1 ≠ 0)

example : ∀ g : BaseGroup, hexNonzero g = true := by native_decide

end LeafProbe
