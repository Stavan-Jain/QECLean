import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.Polynomial
import QEC.Stabilizer.Framework.Homological.BBChainComplex

/-!
# The weight-six separable fractal BB family

The zero-based parameter `s` denotes the mathematical index `s+1`.
The period is `4^(s+1)-1`; the two checks are `1+x+x^(2^(s+1))`
and `1+y+y^(2^(s+1))`. This module defines the actual chain complex
and proves the check support sizes without claiming its distance.
-/

namespace Quantum.Stabilizer.Homological.BB.Fractal

/-- The positive-index period gives a finite cyclic coordinate. -/
instance periodNeZero (s : ℕ) : NeZero (period (s + 1)) :=
  ⟨by
    have hn : 3 ≤ period (s + 1) := three_le_period (Nat.succ_pos s)
    omega⟩

/-- The square translation group of the BB family. -/
abbrev Grid (s : ℕ) := ZMod (period (s + 1)) × ZMod (period (s + 1))

/-- Three horizontal monomials defining the first check. -/
def aSupport (s : ℕ) : Finset (Grid s) :=
  {(0, 0), (1, 0), ((width (s + 1) : ZMod (period (s + 1))), 0)}

/-- Three vertical monomials defining the second check. -/
def bSupport (s : ℕ) : Finset (Grid s) :=
  {(0, 0), (0, 1), (0, (width (s + 1) : ZMod (period (s + 1))))}

/-- The horizontal check coefficient function. -/
def checkA (s : ℕ) (g : Grid s) : ZMod 2 := if g ∈ aSupport s then 1 else 0

/-- The vertical check coefficient function. -/
def checkB (s : ℕ) (g : Grid s) : ZMod 2 := if g ∈ bSupport s then 1 else 0

/-- Small natural exponents inject into the cyclic coordinate. -/
private lemma cast_eq_iff {s a b : ℕ}
    (ha : a < period (s + 1)) (hb : b < period (s + 1)) :
    (a : ZMod (period (s + 1))) = (b : ZMod (period (s + 1))) ↔ a = b := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

/-- The first check has exactly three distinct monomials. -/
theorem aSupport_card (s : ℕ) : (aSupport s).card = 3 := by
  have hn : 3 ≤ period (s + 1) := three_le_period (Nat.succ_pos s)
  have hq : 2 ≤ width (s + 1) := two_le_width (Nat.succ_pos s)
  have hqn : width (s + 1) < period (s + 1) := width_lt_period (Nat.succ_pos s)
  have h01 : (0 : ZMod (period (s + 1))) ≠ 1 := by
    simpa only [Nat.cast_zero, Nat.cast_one] using
      (cast_eq_iff (s := s) (a := 0) (b := 1) (by omega) (by omega)).not.mpr (by omega)
  have h0q : (0 : ZMod (period (s + 1))) ≠ width (s + 1) := by
    simpa only [Nat.cast_zero] using
      (cast_eq_iff (s := s) (a := 0) (b := width (s + 1)) (by omega) hqn).not.mpr (by omega)
  have h1q : (1 : ZMod (period (s + 1))) ≠ width (s + 1) := by
    simpa only [Nat.cast_one] using
      (cast_eq_iff (s := s) (a := 1) (b := width (s + 1)) (by omega) hqn).not.mpr (by omega)
  simp [aSupport, h01, h0q, h1q]

/-- Swapping coordinates exchanges the two check supports. -/
theorem bSupport_eq_map (s : ℕ) :
    bSupport s = (aSupport s).map (Equiv.prodComm _ _).toEmbedding := by
  simp [aSupport, bSupport]

/-- The second check also has exactly three distinct monomials. -/
theorem bSupport_card (s : ℕ) : (bSupport s).card = 3 := by
  rw [bSupport_eq_map, Finset.card_map, aSupport_card]

/-- The natural CSS checks have total weight six across their disjoint blocks. -/
theorem check_weight_six (s : ℕ) : (aSupport s).card + (bSupport s).card = 6 := by
  rw [aSupport_card, bSupport_card]

/-- The actual BB chain complex, using the existing convolution construction. -/
noncomputable def chainComplex (s : ℕ) : HomologicalCode :=
  bbChainComplex (checkA s) (checkB s)

/-- The family has the advertised physical-qubit count. -/
theorem chainComplex_numQubits (s : ℕ) :
    (chainComplex s).numQubits = 2 * period (s + 1) ^ 2 := by
  simp [chainComplex, bbChainComplex, bbNumQubits, Grid, pow_two]

end Quantum.Stabilizer.Homological.BB.Fractal
