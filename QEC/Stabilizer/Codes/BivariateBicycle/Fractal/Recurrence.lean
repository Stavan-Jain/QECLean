import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.SeedAlgebra
import QEC.Stabilizer.Codes.BivariateBicycle.Fractal.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Cyclic words from the recurrence algebra

Linear functionals on the recurrence algebra are exactly the cyclic words
satisfying the trinomial recurrence. The first `2^(s+1)` coordinates determine
such a word, without any irreducibility assumption.
-/

namespace Quantum.Stabilizer.Homological.BB.Fractal

open scoped BigOperators

/-- The physical cyclic index of a classical seed. -/
abbrev SeedIndex (s : ℕ) := ZMod (period (s + 1))

/-- A power of the recurrence root at a cyclic index. -/
noncomputable def seedPower (s : ℕ) (j : SeedIndex s) : SeedAlgebra s :=
  seedRoot s ^ j.val

/-- A natural exponent agrees with its cyclic representative. -/
@[simp] theorem seedPower_natCast (s n : ℕ) :
    seedPower s (n : SeedIndex s) = seedRoot s ^ n := by
  simp only [seedPower, ZMod.val_natCast, ← seedRoot_pow_mod]

/-- Addition of cyclic indices multiplies their root powers. -/
@[simp] theorem seedPower_add (s : ℕ) (i j : SeedIndex s) :
    seedPower s (i + j) = seedPower s i * seedPower s j := by
  simp only [seedPower, ZMod.val_add, ← seedRoot_pow_mod, pow_add]

/-- The cyclic coordinate at zero is the multiplicative unit. -/
@[simp] theorem seedPower_zero (s : ℕ) : seedPower s 0 = 1 := by
  simpa using seedPower_natCast s 0

/-- A functional determines a word by evaluation on the cyclic root powers. -/
noncomputable def functionalWord (s : ℕ) :
    Module.Dual (ZMod 2) (SeedAlgebra s) →ₗ[ZMod 2] (SeedIndex s → ZMod 2) where
  toFun f j := f (seedPower s j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation formula for a functional word. -/
@[simp] theorem functionalWord_apply (s : ℕ)
    (f : Module.Dual (ZMod 2) (SeedAlgebra s)) (j : SeedIndex s) :
    functionalWord s f j = f (seedPower s j) := rfl

/-- Functional words obey the cyclic recurrence. -/
theorem functionalWord_recurrence (s : ℕ)
    (f : Module.Dual (ZMod 2) (SeedAlgebra s)) (j : SeedIndex s) :
    functionalWord s f (j + (width (s + 1) : SeedIndex s)) =
      functionalWord s f j + functionalWord s f (j + 1) := by
  simp only [functionalWord_apply, seedPower_add, seedPower_natCast, seedRoot_width,
    mul_add, mul_one, map_add]
  rw [show seedPower s 1 = seedRoot s by simpa using seedPower_natCast s 1]

/-- The first recurrence-length coordinates already distinguish functionals. -/
theorem functionalWord_injective (s : ℕ) : Function.Injective (functionalWord s) := by
  intro f g h
  apply (seedBasis s).ext
  intro i
  simpa using congrFun h ((i : ℕ) : SeedIndex s)

/-- Extend specified initial coordinates to a functional on the power basis. -/
noncomputable def initialFunctional (s : ℕ) (c : SeedIndex s → ZMod 2) :
    Module.Dual (ZMod 2) (SeedAlgebra s) :=
  (seedBasis s).constr (ZMod 2) fun i => c ((i : ℕ) : SeedIndex s)

/-- The extension agrees with each specified initial coordinate. -/
theorem initialFunctional_initial (s : ℕ) (c : SeedIndex s → ZMod 2)
    (i : ℕ) (hi : i < width (s + 1)) :
    functionalWord s (initialFunctional s c) (i : SeedIndex s) = c (i : SeedIndex s) := by
  have h := (seedBasis s).constr_basis (ZMod 2)
    (fun i => c ((i : ℕ) : SeedIndex s)) (⟨i, hi⟩ : Fin (width (s + 1)))
  simpa only [functionalWord_apply, seedPower_natCast, initialFunctional, seedBasis_apply] using h

/-- A recurrence word is recovered by the functional determined by its prefix. -/
theorem functionalWord_initialFunctional (s : ℕ) (c : SeedIndex s → ZMod 2)
    (hc : ∀ j, c (j + (width (s + 1) : SeedIndex s)) = c j + c (j + 1)) :
    functionalWord s (initialFunctional s c) = c := by
  have hnat : ∀ n : ℕ, functionalWord s (initialFunctional s c) (n : SeedIndex s) =
      c (n : SeedIndex s) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n < width (s + 1)
      · exact initialFunctional_initial s c n hn
      · have hq : 2 ≤ width (s + 1) := two_le_width (Nat.succ_pos s)
        have hle : width (s + 1) ≤ n := Nat.le_of_not_gt hn
        have heq : ((n : ℕ) : SeedIndex s) =
            ((n - width (s + 1) : ℕ) : SeedIndex s) + (width (s + 1) : SeedIndex s) := by
          rw [← Nat.cast_add, Nat.sub_add_cancel hle]
        rw [heq, functionalWord_recurrence, hc, ih _ (by omega)]
        congr 1
        simpa only [Nat.cast_add, Nat.cast_one] using ih (n - width (s + 1) + 1) (by omega)
  funext j
  simpa using hnat j.val

/-- The classical seed consists of all functional words. -/
noncomputable def seedSpace (s : ℕ) : Submodule (ZMod 2) (SeedIndex s → ZMod 2) :=
  LinearMap.range (functionalWord s)

/-- The image definition is equivalent to the concrete trinomial recurrence. -/
theorem mem_seedSpace_iff (s : ℕ) (c : SeedIndex s → ZMod 2) :
    c ∈ seedSpace s ↔ ∀ j,
      c (j + (width (s + 1) : SeedIndex s)) = c j + c (j + 1) := by
  constructor
  · rintro ⟨f, rfl⟩
    exact functionalWord_recurrence s f
  · intro hc
    exact ⟨initialFunctional s c, functionalWord_initialFunctional s c hc⟩

/-- The recurrence algebra is finite-dimensional. -/
instance seedAlgebraFinite (s : ℕ) : Module.Finite (ZMod 2) (SeedAlgebra s) :=
  Module.Finite.of_basis (seedBasis s)

/-- The seed space has exactly the recurrence-length dimension. -/
theorem finrank_seedSpace (s : ℕ) :
    Module.finrank (ZMod 2) (seedSpace s) = width (s + 1) := by
  rw [seedSpace, LinearMap.finrank_range_of_inj (functionalWord_injective s),
    Subspace.dual_finrank_eq, finrank_seedAlgebra]

end Quantum.Stabilizer.Homological.BB.Fractal
