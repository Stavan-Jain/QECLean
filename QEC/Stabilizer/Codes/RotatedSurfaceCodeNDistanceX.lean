import Mathlib.Tactic
import QEC.Stabilizer.Codes.RotatedSurfaceCodeNStabilizerCode

/-!
# Rotated-surface-code X-distance — Stage 5 foundations

For the parametric rotated surface code (L odd, L ≥ 3), the eventual goal
is to prove that every non-trivial X-type logical has weight ≥ L (lower
bound), witnessed exactly by the middle-column X-string `logicalX L`.

This file currently establishes the **row-parity invariant** infrastructure:
the `rowParity` linear functional, its key value on `middleColChain` (= 1
for every row), and the linearity properties that anchor the eventual
proof that `rowParity` vanishes on boundaries and is constant in `y` on
cycles.

The full lower bound `weight g ≥ L` for non-trivial X-logicals, plus the
witness packaging `HasCodeDistance`, will follow from:

* `rowParity (∂₂ f) y = 0` for every X-face 2-chain `f` and row `y`
  (each `xSupport xf` projected to any row has even cardinality —
   proven by direct case analysis on the three face types).
* `rowParity c y` is constant in `y` on cycles `c` (summing the relevant
  interior + boundary Z-face constraints between adjacent rows).
* `dim H₁ = 1` (Stage 3) ⟹ any non-trivial cycle is homologous to
  `middleColChain`, so `rowParity c y = 1` for all `y`.
* Each row contributes ≥ 1 qubit to the support of `c`, giving weight ≥ L.

These remaining steps require substantial Finset bookkeeping over the
six cases (interior × Z-face, top/bottom-bdy × Z-face) and are deferred
to follow-up commits.
-/

namespace Quantum
namespace StabilizerGroup
namespace RotatedSurfaceCodeN

open scoped BigOperators
open NQubitPauliGroupElement
open Stabilizer.Lattice

variable (L : ℕ) [Fact (Odd L)] [Fact (3 ≤ L)]

/-! ## §A — Row parity functional -/

/-- The row-parity functional at row `y`: parity of `c (x, y)` over `x`. -/
def rowParity (c : RotatedSurface.VtxIdx L → ZMod 2) (y : Fin L) : ZMod 2 :=
  ∑ x : Fin L, c (x, y)

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
@[simp] lemma rowParity_add (c c' : RotatedSurface.VtxIdx L → ZMod 2) (y : Fin L) :
    rowParity L (c + c') y = rowParity L c y + rowParity L c' y := by
  unfold rowParity
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intros; simp [Pi.add_apply]

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
@[simp] lemma rowParity_zero (y : Fin L) :
    rowParity L (0 : RotatedSurface.VtxIdx L → ZMod 2) y = 0 := by
  unfold rowParity
  apply Finset.sum_eq_zero
  intros; rfl

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
lemma rowParity_smul (a : ZMod 2) (c : RotatedSurface.VtxIdx L → ZMod 2)
    (y : Fin L) :
    rowParity L (a • c) y = a * rowParity L c y := by
  unfold rowParity
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros; simp [Pi.smul_apply, smul_eq_mul]

/-! ## §B — Row parity of `middleColChain` is `1`

The middle column intersects each row in exactly one qubit (at `x = mid`),
so the row parity is `1` for every row.  This is the non-zero side of the
eventual `H₁ → ZMod 2` functional.
-/

omit [Fact (Odd L)] in
theorem rowParity_middleColChain (y : Fin L) :
    rowParity L (middleColChain L) y = 1 := by
  classical
  unfold rowParity
  -- ∑ x, middleColChain (x, y) = if x = mid then 1 else 0 summed → 1.
  rw [Finset.sum_eq_single (midIdx L)]
  · unfold middleColChain
    simp
  · intro x _ hne
    unfold middleColChain
    rw [if_neg]
    intro hx
    apply hne
    apply Fin.ext
    show x.val = (midIdx L).val
    rw [midIdx_val]
    exact hx
  · intro hcontra; exact absurd (Finset.mem_univ _) hcontra

end RotatedSurfaceCodeN
end StabilizerGroup
end Quantum
