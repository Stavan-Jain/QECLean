import QEC.Stabilizer.Framework.Homological.BZCertificate
import Mathlib.LinearAlgebra.Pi

namespace Quantum.Stabilizer.Homological.F2Mask

variable {ι κ : Type} {n m : Nat} (e : ι ≃ Fin n) (f : κ ≃ Fin m)

/-- Reading a zero mask gives the zero chain. -/
theorem chainOfMask_zero : chainOfMask e 0 = 0 := by
  ext i
  simp [chainOfMask]

/-- Reading XOR masks gives the sum of their chains. -/
theorem chainOfMask_xor (a b : Nat) :
    chainOfMask e (a ^^^ b) = chainOfMask e a + chainOfMask e b := by
  ext i
  simp only [chainOfMask, Nat.testBit_xor, Pi.add_apply]
  cases a.testBit (e i) <;> cases b.testBit (e i) <;> decide

/--
A certified XOR reconstruction is a linear map between binary chain spaces.
-/
def reconLinear (w : List (Nat × Nat)) : (ι → ZMod 2) →ₗ[ZMod 2] (κ → ZMod 2) where
  toFun c := chainOfMask f (reconX w (maskOf e c))
  map_add' a b := by rw [maskOf_add, reconX_xor, chainOfMask_xor]
  map_smul' a c := by
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) a with rfl | rfl
    · simp [maskOf_zero, reconX_zero, chainOfMask_zero]
    · simp

/-- A point-mass chain has a mask with just its indexed bit set. -/
theorem maskOf_single [DecidableEq ι] (i : ι) :
    maskOf e (Pi.single i 1) = 2 ^ (e i).val := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_maskOf]
  by_cases hj : j < n
  · rw [dif_pos hj, Nat.testBit_two_pow]
    simp only [Pi.single_apply]
    by_cases he : e.symm ⟨j, hj⟩ = i
    · have hji : j = (e i).val := by simpa using congrArg (fun a => (e a).val) he
      simp [he, hji]
    · have hji : j ≠ (e i).val := by
        intro h
        apply he
        apply e.injective
        simpa using Fin.ext h
      simp [he, hji, Ne.symm hji]
  · rw [dif_neg hj, Nat.testBit_two_pow]
    have hji : j ≠ (e i).val := by have := (e i).isLt; omega
    simp [hji, Ne.symm hji]

/-- A mask with a single indexed bit decodes to its point-mass chain. -/
theorem chainOfMask_two_pow [DecidableEq ι] (i : ι) :
    chainOfMask e (2 ^ (e i).val) = Pi.single i 1 := by
  rw [← maskOf_single, chainOfMask_maskOf]

/-- A finite XOR of generators belongs to their XOR-span. -/
theorem xorList_mem_span (gens xs : List Nat)
    (h : ∀ x ∈ xs, x ∈ gens) : XorSpan gens (xorList xs) := by
  induction xs with
  | nil => exact .zero
  | cons x xs ih =>
    rw [xorList_cons]
    exact .step (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

/-- Reconstruction always belongs to the span of its output columns. -/
theorem reconX_mem_span (w : List (Nat × Nat)) (M : Nat) :
    XorSpan (w.map Prod.snd) (reconX w M) := by
  apply xorList_mem_span
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  exact List.mem_map.mpr ⟨p, (List.mem_filter.mp hp).1, rfl⟩

/-- A span of bounded masks contains only bounded masks. -/
theorem XorSpan.lt {gens : List Nat} {M n : Nat} (h : XorSpan gens M)
    (hgens : ∀ g ∈ gens, g < 2 ^ n) : M < 2 ^ n := by
  induction h with
  | zero => exact Nat.two_pow_pos n
  | step hg _ ih => exact Nat.xor_lt_two_pow (hgens _ hg) ih

/-- Reconstruction preserves the common output bit bound. -/
theorem reconX_lt (w : List (Nat × Nat)) (M n : Nat)
    (h : ∀ p ∈ w, p.2 < 2 ^ n) : reconX w M < 2 ^ n := by
  apply (reconX_mem_span w M).lt
  intro g hg
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
  exact h p hp

/--
Reading back a binary reconstruction gives the original bounded XOR result.
-/
theorem maskOf_reconLinear (w : List (Nat × Nat)) (c : ι → ZMod 2)
    (h : ∀ p ∈ w, p.2 < 2 ^ m) :
    maskOf f (reconLinear e f w c) = reconX w (maskOf e c) := by
  exact maskOf_chainOfMask f (reconX_lt w _ m h)

end Quantum.Stabilizer.Homological.F2Mask

namespace Quantum.Stabilizer.Homological

open scoped BigOperators

/--
A linear map on a finite binary coordinate space is determined by point
masses.
-/
theorem linearMap_eq_of_single {ι M : Type} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid M] [Module (ZMod 2) M]
    (T U : (ι → ZMod 2) →ₗ[ZMod 2] M)
    (h : ∀ i, T (Pi.single i 1) = U (Pi.single i 1)) : T = U := by
  apply LinearMap.pi_ext
  intro i z
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) z with rfl | rfl
  · simp
  · exact h i

/--
A left inverse checked on point masses proves injectivity of a binary linear
map.
-/
theorem injective_of_decoder_single {ι M : Type} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid M] [Module (ZMod 2) M]
    (T : (ι → ZMod 2) →ₗ[ZMod 2] M)
    (D : M →ₗ[ZMod 2] (ι → ZMod 2))
    (h : ∀ i, D (T (Pi.single i 1)) = Pi.single i 1) : Function.Injective T := by
  have hd : D.comp T = LinearMap.id := linearMap_eq_of_single _ _ h
  intro a b hab
  have h := congrArg D hab
  have hda := LinearMap.congr_fun hd a
  have hdb := LinearMap.congr_fun hd b
  simpa using hda.symm.trans (h.trans hdb)

end Quantum.Stabilizer.Homological
