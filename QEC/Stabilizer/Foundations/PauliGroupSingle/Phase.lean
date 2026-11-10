import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic
import QEC.Foundations.Foundations
import QEC.Stabilizer.Foundations.PauliGroupSingle.Core

/-!
# Phase powers as complex numbers

The phase power `k : Fin 4` of a Pauli group element stands for the scalar
`i ^ k`. This file gives that scalar as a complex number
(`phasePowerToComplex`) and as a unit complex number
(`phasePowerToUnitComplex`).
-/

namespace Quantum

namespace PauliGroupElement

/-- The complex phase `i ^ k` of a phase power `k`. -/
def phasePowerToComplex (k : Fin 4) : ℂ :=
  Complex.I ^ (k : ℕ)

@[simp] lemma phasePowerToComplex_0 : phasePowerToComplex 0 = 1 := by
  simp [phasePowerToComplex]

@[simp] lemma phasePowerToComplex_1 : phasePowerToComplex 1 = Complex.I := by
  simp [phasePowerToComplex]

@[simp] lemma phasePowerToComplex_2 : phasePowerToComplex 2 = -1 := by
  simp [phasePowerToComplex]

@[simp] lemma phasePowerToComplex_3 : phasePowerToComplex 3 = -Complex.I := by
  simp [phasePowerToComplex]

/-- Phases multiply by adding phase powers: `i ^ a * i ^ b = i ^ (a + b)`. -/
lemma phasePowerToComplex_add (a b : Fin 4) :
    phasePowerToComplex a * phasePowerToComplex b = phasePowerToComplex (a + b) := by
  fin_cases a <;> fin_cases b <;> simp [phasePowerToComplex]

/-- Three-factor form of `phasePowerToComplex_add`. -/
lemma phasePowerToComplex_add3 (a b c : Fin 4) :
    phasePowerToComplex a * phasePowerToComplex b * phasePowerToComplex c =
      phasePowerToComplex (a + b + c) := by
  rw [phasePowerToComplex_add, phasePowerToComplex_add]

/-- The phase of a sum of phase powers is the product of the phases. -/
lemma phasePowerToComplex_sum {ι : Type*} (s : Finset ι) (k : ι → Fin 4) :
    phasePowerToComplex (∑ i ∈ s, k i) = ∏ i ∈ s, phasePowerToComplex (k i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, ← phasePowerToComplex_add, ih]

lemma phasePowerToComplex_ne_zero (k : Fin 4) : phasePowerToComplex k ≠ 0 :=
  pow_ne_zero _ Complex.I_ne_zero

/-- Distinct phase powers give distinct phases. -/
lemma phasePowerToComplex_injective : Function.Injective phasePowerToComplex := by
  simp [Function.Injective, Fin.forall_fin_succ, phasePowerToComplex, Complex.ext_iff]
  norm_num

/-- Conjugating a phase negates its phase power: `star (i ^ k) = i ^ (-k)`. -/
lemma phasePowerToComplex_star (k : Fin 4) :
    star (phasePowerToComplex k) = phasePowerToComplex (-k) := by
  fin_cases k <;>
    simp [phasePowerToComplex, show (-1 : Fin 4) = 3 from rfl, show (-2 : Fin 4) = 2 from rfl,
      show (-3 : Fin 4) = 1 from rfl, pow_succ]

/-- The phase `i ^ k` as a unit complex number. -/
def phasePowerToUnitComplex (k : Fin 4) : UnitComplex :=
  match k with
  | 0 => UnitComplex.one
  | 1 => UnitComplex.I
  | 2 => UnitComplex.negOne
  | 3 => UnitComplex.negI

@[simp] lemma phasePowerToUnitComplex_coe (k : Fin 4) :
    (phasePowerToUnitComplex k : ℂ) = phasePowerToComplex k := by
  fin_cases k <;> simp [phasePowerToUnitComplex, phasePowerToComplex,
    UnitComplex.one_coe, UnitComplex.negOne_coe, UnitComplex.I_coe, UnitComplex.negI_coe]

end PauliGroupElement

end Quantum
