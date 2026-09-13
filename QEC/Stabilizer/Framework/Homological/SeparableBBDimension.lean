import QEC.Stabilizer.Framework.Homological.SeparableBBChainComplex
import QEC.Stabilizer.Framework.Homological.SeparableBBHomology
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Dimension of separable bicycle homology

The simultaneous kernel of left and right multiplication is a Hom space
from the second cokernel to the first kernel. Square rank-nullity therefore
identifies its dimension with the product of the two classical nullities.
-/

namespace Quantum.Stabilizer.Homological.SeparableBB

open Matrix Module

variable {I J K : Type*} [Fintype I] [Fintype J] [Field K]

/-- Matrices killed by both separated boundary components. -/
def jointKernel (A : Matrix I I K) (B : Matrix J J K) :
    Submodule K (Matrix I J K) where
  carrier := {S | A * S = 0 ∧ S * Bᵀ = 0}
  zero_mem' := by simp
  add_mem' := by
    intro S T hS hT
    simp only [Set.mem_setOf_eq, Matrix.mul_add, Matrix.add_mul, hS.1, hS.2,
      hT.1, hT.2, zero_add, and_self]
  smul_mem' := by
    intro k S hS
    simp only [Set.mem_setOf_eq, Matrix.mul_smul, Matrix.smul_mul, hS.1, hS.2,
      smul_zero, and_self]

/-- Quotient-to-kernel maps produce matrices in the simultaneous kernel. -/
noncomputable def homToJointKernel (A : Matrix I I K) (B : Matrix J J K) :
    (((J → K) ⧸ Bᵀ.mulVecLin.range) →ₗ[K] A.mulVecLin.ker) →ₗ[K] jointKernel A B := by
  classical
  let P := A.mulVecLin.ker
  let Q := Bᵀ.mulVecLin.range
  let matrixOf := fun T : ((J → K) ⧸ Q) →ₗ[K] P =>
    LinearMap.toMatrix' (P.subtype.comp (T.comp Q.mkQ))
  have hmem : ∀ T, matrixOf T ∈ jointKernel A B := by
    intro T
    constructor
    · apply Matrix.toLin'.injective
      dsimp only [matrixOf]
      rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', map_zero]
      apply LinearMap.ext
      intro x
      funext i
      exact congrFun (T (Q.mkQ x)).property i
    · apply Matrix.toLin'.injective
      dsimp only [matrixOf]
      rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', map_zero]
      apply LinearMap.ext
      intro x
      funext i
      have hx : Q.mkQ (Bᵀ *ᵥ x) = 0 :=
        (Submodule.Quotient.mk_eq_zero Q).mpr ⟨x, rfl⟩
      change (T (Q.mkQ (Bᵀ *ᵥ x))).val i = 0
      rw [hx, map_zero]
      rfl
  refine { toFun := fun T => ⟨matrixOf T, hmem T⟩, map_add' := ?_, map_smul' := ?_ }
  · intro T U
    apply Subtype.ext
    simp only [matrixOf, LinearMap.add_comp, LinearMap.comp_add, map_add]
    rfl
  · intro k T
    apply Subtype.ext
    simp only [matrixOf, LinearMap.smul_comp, LinearMap.comp_smul, map_smul]
    rfl

/-- The quotient construction faithfully records every matrix coefficient. -/
theorem homToJointKernel_injective (A : Matrix I I K) (B : Matrix J J K) :
    Function.Injective (homToJointKernel A B) := by
  classical
  intro T U h
  apply Bᵀ.mulVecLin.range.quot_hom_ext
  intro x
  apply Subtype.ext
  have hm := congrArg (fun S : jointKernel A B => Matrix.toLin' S.val) h
  have hx := LinearMap.congr_fun hm x
  change (Matrix.toLin' (LinearMap.toMatrix'
    (A.mulVecLin.ker.subtype.comp (T.comp Bᵀ.mulVecLin.range.mkQ)))) x =
    (Matrix.toLin' (LinearMap.toMatrix'
      (A.mulVecLin.ker.subtype.comp (U.comp Bᵀ.mulVecLin.range.mkQ)))) x at hx
  simpa only [Matrix.toLin'_toMatrix', LinearMap.comp_apply,
    Submodule.subtype_apply, Submodule.mkQ_apply] using hx

/-- Every matrix in the simultaneous kernel descends to the second cokernel. -/
theorem homToJointKernel_surjective (A : Matrix I I K) (B : Matrix J J K) :
    Function.Surjective (homToJointKernel A B) := by
  classical
  intro S
  let P := A.mulVecLin.ker
  let Q := Bᵀ.mulVecLin.range
  have hcod : ∀ x, Matrix.toLin' S.val x ∈ P := by
    intro x
    change A *ᵥ (S.val *ᵥ x) = 0
    rw [Matrix.mulVec_mulVec, S.property.1, Matrix.zero_mulVec]
  let g : (J → K) →ₗ[K] P := (Matrix.toLin' S.val).codRestrict P hcod
  have hker : Q ≤ g.ker := by
    rintro x ⟨y, rfl⟩
    apply Subtype.ext
    change S.val *ᵥ (Bᵀ *ᵥ y) = 0
    rw [Matrix.mulVec_mulVec, S.property.2, Matrix.zero_mulVec]
  refine ⟨Q.liftQ g hker, ?_⟩
  apply Subtype.ext
  apply Matrix.toLin'.injective
  change Matrix.toLin' (LinearMap.toMatrix'
    (P.subtype.comp ((Q.liftQ g hker).comp Q.mkQ))) = Matrix.toLin' S.val
  rw [Matrix.toLin'_toMatrix', Submodule.liftQ_mkQ]
  rfl

/-- The simultaneous kernel is the Hom space between the two classical ends. -/
noncomputable def jointKernelEquivHom (A : Matrix I I K) (B : Matrix J J K) :
    jointKernel A B ≃ₗ[K]
      (((J → K) ⧸ Bᵀ.mulVecLin.range) →ₗ[K] A.mulVecLin.ker) :=
  (LinearEquiv.ofBijective (homToJointKernel A B)
    ⟨homToJointKernel_injective A B, homToJointKernel_surjective A B⟩).symm

/-- A square matrix and its transpose have equal nullity. -/
theorem finrank_kernel_transpose (B : Matrix J J K) :
    finrank K Bᵀ.mulVecLin.ker = finrank K B.mulVecLin.ker := by
  have hB := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  have hBT := LinearMap.finrank_range_add_finrank_ker Bᵀ.mulVecLin
  have hr : finrank K Bᵀ.mulVecLin.range = finrank K B.mulVecLin.range :=
    Matrix.rank_transpose B
  omega

/-- A square transpose cokernel has the dimension of the original kernel. -/
theorem finrank_cokernel_transpose (B : Matrix J J K) :
    finrank K ((J → K) ⧸ Bᵀ.mulVecLin.range) = finrank K B.mulVecLin.ker := by
  have hq := Submodule.finrank_quotient_add_finrank (R := K) Bᵀ.mulVecLin.range
  have hn := LinearMap.finrank_range_add_finrank_ker Bᵀ.mulVecLin
  rw [finrank_kernel_transpose] at hn
  omega

/-- The two classical nullities multiply in the simultaneous matrix kernel. -/
theorem finrank_jointKernel (A : Matrix I I K) (B : Matrix J J K) :
    finrank K (jointKernel A B) =
      finrank K A.mulVecLin.ker * finrank K B.mulVecLin.ker := by
  rw [(jointKernelEquivHom A B).finrank_eq, Module.finrank_linearMap,
    finrank_cokernel_transpose, Nat.mul_comm]


section Circulant

variable {I₀ J₀ : Type} [Fintype I₀] [Fintype J₀]
  [AddCommGroup I₀] [AddCommGroup J₀]

/-- Currying identifies the second boundary kernel with the simultaneous kernel. -/
noncomputable def boundary2KernelEquivJointKernel
    (f : I₀ → ZMod 2) (g : J₀ → ZMod 2) :
    (complex f g).boundary2.ker ≃ₗ[ZMod 2]
      jointKernel (Matrix.circulant f) (Matrix.circulant g) := by
  classical
  refine
    { toFun := fun s => ⟨Function.curry s.val, ?_⟩
      invFun := fun S => ⟨Function.uncurry S.val, ?_⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl }
  · constructor
    · ext i j
      have h := congrFun s.property ((i, j), 0)
      change BB.conv (horizontal f) s.val (i, j) = 0 at h
      rw [conv_horizontal_eq] at h
      exact h
    · ext i j
      have h := congrFun s.property ((i, j), 1)
      change BB.conv (vertical g) s.val (i, j) = 0 at h
      rw [conv_vertical_eq] at h
      exact h
  · change (complex f g).boundary2 (Function.uncurry S.val) = 0
    funext ⟨⟨i, j⟩, b⟩
    fin_cases b
    · change BB.conv (horizontal f) (Function.uncurry S.val) (i, j) = 0
      rw [conv_horizontal_eq]
      exact congrFun (congrFun S.property.1 i) j
    · change BB.conv (vertical g) (Function.uncurry S.val) (i, j) = 0
      rw [conv_vertical_eq]
      exact congrFun (congrFun S.property.2 i) j
/-- A separated second boundary has nullity equal to the classical product. -/
theorem finrank_boundary2_kernel (f : I₀ → ZMod 2) (g : J₀ → ZMod 2) :
    finrank (ZMod 2) (complex f g).boundary2.ker =
      finrank (ZMod 2) (Matrix.circulant f).mulVecLin.ker *
        finrank (ZMod 2) (Matrix.circulant g).mulVecLin.ker := by
  rw [(boundary2KernelEquivJointKernel f g).finrank_eq, finrank_jointKernel]

/-- The logical dimension is twice the product of the two classical nullities. -/
theorem finrank_H1 (f : I₀ → ZMod 2) (g : J₀ → ZMod 2) :
    finrank (ZMod 2) (complex f g).H1 =
      2 * finrank (ZMod 2) (Matrix.circulant f).mulVecLin.ker *
        finrank (ZMod 2) (Matrix.circulant g).mulVecLin.ker := by
  classical
  change finrank (ZMod 2) (BB.bbChainComplex (horizontal f) (vertical g)).H1 = _
  rw [BB.finrank_H1_eq_two_mul_boundary2_nullity]
  change 2 * finrank (ZMod 2) (complex f g).boundary2.ker = _
  rw [finrank_boundary2_kernel, Nat.mul_assoc]

end Circulant

end Quantum.Stabilizer.Homological.SeparableBB
