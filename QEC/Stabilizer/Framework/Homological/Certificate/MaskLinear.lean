import QEC.Stabilizer.Framework.Homological.BZCertificate
import Mathlib.LinearAlgebra.Pi

/-!
# Window reconstructions as linear maps

`F2Mask.reconLinear e f w` is the reconstruction `F2Mask.reconX w` through a
window, read as a `ZMod 2`-linear map between chain spaces: it packs a chain
into its mask, reconstructs, and reads the result back as a chain.
`F2Mask.maskOf_reconLinear` identifies the mask of its value with the packed
reconstruction.

Linear maps out of a binary coordinate space are determined by their values on
point masses (`linearMap_eq_of_single`), so a left inverse checked on point
masses proves injectivity (`injective_of_decoder_single`).
-/

namespace Quantum.Stabilizer.Homological

namespace F2Mask

variable {ι κ : Type*} {n m : ℕ} (e : ι ≃ Fin n) (f : κ ≃ Fin m)

/-- The reconstruction through the window `w`, as a linear map between binary
chain spaces. -/
def reconLinear (w : List (ℕ × ℕ)) : (ι → ZMod 2) →ₗ[ZMod 2] (κ → ZMod 2) where
  toFun c := chainOfMask f (reconX w (maskOf e c))
  map_add' a b := by rw [maskOf_add, reconX_xor, chainOfMask_xor]
  map_smul' a c := by
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) a with rfl | rfl
    · simp [maskOf_zero, reconX_zero, chainOfMask_zero]
    · simp

/-- If the rows of the window fit in the output mask length, the mask of
`reconLinear e f w c` is the reconstruction of the mask of `c`. -/
theorem maskOf_reconLinear (w : List (ℕ × ℕ)) (c : ι → ZMod 2)
    (h : ∀ p ∈ w, p.2 < 2 ^ m) :
    maskOf f (reconLinear e f w c) = reconX w (maskOf e c) :=
  maskOf_chainOfMask f (reconX_lt w _ m h)

end F2Mask

/-- A linear map on a finite binary coordinate space is determined by its
values on point masses. -/
theorem linearMap_eq_of_single {ι M : Type*} [Finite ι] [DecidableEq ι]
    [AddCommMonoid M] [Module (ZMod 2) M]
    (T U : (ι → ZMod 2) →ₗ[ZMod 2] M)
    (h : ∀ i, T (Pi.single i 1) = U (Pi.single i 1)) : T = U := by
  refine LinearMap.pi_ext fun i z => ?_
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) z with rfl | rfl
  · simp
  · exact h i

/-- A binary linear map with a linear left inverse on point masses is
injective. -/
theorem injective_of_decoder_single {ι M : Type*} [Finite ι] [DecidableEq ι]
    [AddCommMonoid M] [Module (ZMod 2) M]
    (T : (ι → ZMod 2) →ₗ[ZMod 2] M)
    (D : M →ₗ[ZMod 2] (ι → ZMod 2))
    (h : ∀ i, D (T (Pi.single i 1)) = Pi.single i 1) : Function.Injective T :=
  Function.LeftInverse.injective (g := D)
    (LinearMap.congr_fun (linearMap_eq_of_single (D.comp T) LinearMap.id h))

end Quantum.Stabilizer.Homological
