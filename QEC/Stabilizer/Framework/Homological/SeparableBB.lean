import QEC.Stabilizer.Framework.Homological.Distance
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.InformationTheory.Hamming

/-!
# Distance bounds for separable bicycle complexes

The cycle equation is `A U + V Bᵀ = 0`, with boundaries `(S Bᵀ, A S)`.
Contraction against either classical transpose kernel detects every nonzero
homology class. Each contraction is a physical Hamming contraction, so the
classical kernel distances bound the quantum chain distance.
-/

namespace Quantum.Stabilizer.Homological.SeparableBB

open Matrix
open scoped BigOperators

/-- A linear map vanishing on the kernel of another map factors through it. -/
private theorem exists_factor_of_ker_le
    {K V W Z : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup Z] [Module K Z]
    (f : V →ₗ[K] W) (g : V →ₗ[K] Z) (h : f.ker ≤ g.ker) :
    ∃ t : W →ₗ[K] Z, t.comp f = g := by
  let q : f.range →ₗ[K] Z :=
    (f.ker.liftQ g h).comp f.quotKerEquivRange.symm.toLinearMap
  obtain ⟨t, ht⟩ := q.exists_extend
  refine ⟨t, LinearMap.ext fun v => ?_⟩
  have hv := congrArg (fun r : f.range →ₗ[K] Z => r ⟨f v, ⟨v, rfl⟩⟩) ht
  simpa only [LinearMap.comp_apply, Submodule.subtype_apply, q,
    LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image,
    Submodule.mkQ_apply, Submodule.liftQ_apply] using hv

/-- Every linear map of vector spaces has a generalized inverse. -/
private theorem exists_generalized_inverse
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) :
    ∃ j : W →ₗ[K] V, (f.comp j).comp f = f := by
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective
    f.range_rangeRestrict
  obtain ⟨j, hj⟩ := s.exists_extend
  refine ⟨j, LinearMap.ext fun v => ?_⟩
  have hjv := congrArg (fun r : f.range →ₗ[K] V => r ⟨f v, ⟨v, rfl⟩⟩) hj
  have hsv := congrArg
    (fun r : f.range →ₗ[K] f.range => (r ⟨f v, ⟨v, rfl⟩⟩ : W)) hs
  change f (j (f v)) = f v
  change j (f v) = s ⟨f v, ⟨v, rfl⟩⟩ at hjv
  rw [hjv]
  exact hsv

variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype I] in
/-- A matrix killing another matrix's kernel is a left multiple of it. -/
theorem exists_matrix_factor_of_kernel
    {K : Type*} [Field K] (A : Matrix J J K) (U : Matrix I J K)
    (h : ∀ w, A *ᵥ w = 0 → U *ᵥ w = 0) :
    ∃ W : Matrix I J K, U = W * A := by
  classical
  obtain ⟨w, hw⟩ := exists_factor_of_ker_le (Matrix.toLin' A) (Matrix.toLin' U) h
  refine ⟨LinearMap.toMatrix' w, ?_⟩
  have ht := congrArg LinearMap.toMatrix' hw
  simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] using ht.symm

/-- Every square matrix over a field admits a generalized inverse. -/
theorem exists_matrix_generalized_inverse
    {K : Type*} [Field K] (A : Matrix I I K) :
    ∃ J : Matrix I I K, A * J * A = A := by
  classical
  obtain ⟨j, hj⟩ := exists_generalized_inverse (Matrix.toLin' A)
  refine ⟨LinearMap.toMatrix' j, ?_⟩
  have ht := congrArg LinearMap.toMatrix' hj
  simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] using ht

/-- The two physical matrices form a cycle in the separable bicycle complex. -/
def IsCycle (A : Matrix I I (ZMod 2)) (B : Matrix J J (ZMod 2))
    (U V : Matrix I J (ZMod 2)) : Prop := A * U + V * Bᵀ = 0

/-- A boundary has the standard two-block product form. -/
def IsBoundary (A : Matrix I I (ZMod 2)) (B : Matrix J J (ZMod 2))
    (U V : Matrix I J (ZMod 2)) : Prop :=
  ∃ S : Matrix I J (ZMod 2), U = S * Bᵀ ∧ V = A * S

/-- Factorizations of both blocks and the cycle equation give a boundary. -/
theorem isBoundary_of_factorizations
    (A : Matrix I I (ZMod 2)) (B : Matrix J J (ZMod 2))
    (U V W T : Matrix I J (ZMod 2))
    (hc : IsCycle A B U V) (hu : U = W * Bᵀ) (hv : V = A * T) :
    IsBoundary A B U V := by
  classical
  obtain ⟨jInv, hJ⟩ := exists_matrix_generalized_inverse A
  refine ⟨jInv * V + (1 - jInv * A) * W, ?_, ?_⟩
  · have he : A * U = V * Bᵀ := by
      ext i j
      have h := congrFun (congrFun hc i) j
      exact (by decide : ∀ a b : ZMod 2, a + b = 0 → a = b) _ _ h
    rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← hu,
      Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, he]
    abel
  · have hJV : A * jInv * V = V := by rw [hv, ← Matrix.mul_assoc, hJ]
    rw [Matrix.mul_add, ← Matrix.mul_assoc, hJV, ← Matrix.mul_assoc,
      Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hJ, sub_self,
      Matrix.zero_mul, add_zero]

/-- The two classical-kernel contractions jointly detect every cycle class. -/
theorem isBoundary_iff_contractions_vanish
    (A : Matrix I I (ZMod 2)) (B : Matrix J J (ZMod 2))
    (U V : Matrix I J (ZMod 2)) (hc : IsCycle A B U V) :
    IsBoundary A B U V ↔
      (∀ w, Bᵀ *ᵥ w = 0 → U *ᵥ w = 0) ∧
      (∀ a, Aᵀ *ᵥ a = 0 → Vᵀ *ᵥ a = 0) := by
  constructor
  · rintro ⟨S, rfl, rfl⟩
    constructor
    · intro w hw
      rw [← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]
    · intro a ha
      rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_zero]
  · rintro ⟨hu, hv⟩
    obtain ⟨W, hW⟩ := exists_matrix_factor_of_kernel Bᵀ U hu
    obtain ⟨T, hT⟩ := exists_matrix_factor_of_kernel Aᵀ Vᵀ hv
    have hT' : V = A * Tᵀ := by
      have h := congrArg Matrix.transpose hT
      simpa only [Matrix.transpose_transpose, Matrix.transpose_mul] using h
    exact isBoundary_of_factorizations A B U V W Tᵀ hc hW hT'

/-- The physical Hamming weight of a matrix of binary sites. -/
noncomputable def matrixWeight (M : Matrix I J (ZMod 2)) : ℕ :=
  hammingNorm (Function.uncurry M)

/-- Matrix-vector contraction cannot increase the physical Hamming weight. -/
theorem hammingNorm_mulVec_le_matrixWeight
    (M : Matrix I J (ZMod 2)) (w : J → ZMod 2) :
    hammingNorm (M *ᵥ w) ≤ matrixWeight M := by
  classical
  let s := Finset.univ.filter fun i => (M *ᵥ w) i ≠ 0
  let t := Finset.univ.filter fun p : I × J => M p.1 p.2 ≠ 0
  have hex : ∀ i : s, ∃ j, M i.1 j ≠ 0 := by
    intro i
    by_contra h
    push Not at h
    have hi := (Finset.mem_filter.mp i.2).2
    apply hi
    simp only [Matrix.mulVec, dotProduct, h, zero_mul, Finset.sum_const_zero]
  choose col hcol using hex
  let f : s → t := fun i => ⟨(i.1, col i), Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hcol i⟩⟩
  exact Finset.card_le_card_of_injective (f := f) fun a b hab =>
    Subtype.ext (congrArg (fun p : t => p.1.1) hab)

/-- Transposition preserves the physical matrix weight. -/
theorem matrixWeight_transpose (M : Matrix I J (ZMod 2)) :
    matrixWeight Mᵀ = matrixWeight M := by
  classical
  unfold matrixWeight hammingNorm
  apply Finset.card_equiv (Equiv.prodComm J I)
  intro p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

/-- The first contraction of a separable cycle is in the first kernel. -/
theorem mulVec_mem_kernel_of_cycle
    (A : Matrix I I (ZMod 2)) (B : Matrix J J (ZMod 2))
    (U V : Matrix I J (ZMod 2)) (hc : IsCycle A B U V)
    (w : J → ZMod 2) (hw : Bᵀ *ᵥ w = 0) :
    A *ᵥ (U *ᵥ w) = 0 := by
  have h := congrArg (fun M : Matrix I J (ZMod 2) => M *ᵥ w) hc
  simpa only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hw,
    Matrix.mulVec_zero, add_zero, Matrix.zero_mulVec] using h

/-- The second contraction of a separable cycle is in the second kernel. -/
theorem transpose_mulVec_mem_kernel_of_cycle
    (A : Matrix I I (ZMod 2)) (B : Matrix J J (ZMod 2))
    (U V : Matrix I J (ZMod 2)) (hc : IsCycle A B U V)
    (a : I → ZMod 2) (ha : Aᵀ *ᵥ a = 0) :
    B *ᵥ (Vᵀ *ᵥ a) = 0 := by
  have h := congrArg (fun M : Matrix I J (ZMod 2) => Mᵀ *ᵥ a) hc
  simpa only [Matrix.transpose_add, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
    ha, Matrix.mulVec_zero, zero_add, Matrix.transpose_zero, Matrix.zero_mulVec] using h

/-- Classical kernel distances give the chain distance of a separable complex.

This statement applies to every cycle, with no choice of representative and no
metric assumption on algebraic boundary elimination.
-/
theorem weight_ge_min_of_nonboundary_cycle
    (A : Matrix I I (ZMod 2)) (B : Matrix J J (ZMod 2))
    (dA dB : ℕ)
    (hA : ∀ u, A *ᵥ u = 0 → u ≠ 0 → dA ≤ hammingNorm u)
    (hB : ∀ v, B *ᵥ v = 0 → v ≠ 0 → dB ≤ hammingNorm v)
    (U V : Matrix I J (ZMod 2)) (hc : IsCycle A B U V)
    (hnb : ¬ IsBoundary A B U V) :
    min dA dB ≤ matrixWeight U + matrixWeight V := by
  by_contra hd
  apply hnb
  apply (isBoundary_iff_contractions_vanish A B U V hc).mpr
  constructor
  · intro w hw
    by_contra hn
    have hlow := hA _ (mulVec_mem_kernel_of_cycle A B U V hc w hw) hn
    have hweight := hammingNorm_mulVec_le_matrixWeight U w
    omega
  · intro a ha
    by_contra hn
    have hlow := hB _ (transpose_mulVec_mem_kernel_of_cycle A B U V hc a ha) hn
    have hweight := hammingNorm_mulVec_le_matrixWeight Vᵀ a
    rw [matrixWeight_transpose] at hweight
    omega

/-- A single occupied column carrying a classical word. -/
noncomputable def columnMatrix (u : I → ZMod 2) (j : J) : Matrix I J (ZMod 2) := by
  classical
  exact Matrix.vecMulVec u (Pi.single j 1)

/-- The zero matrix has zero physical weight. -/
@[simp] theorem matrixWeight_zero : matrixWeight (0 : Matrix I J (ZMod 2)) = 0 :=
  hammingNorm_zero

/-- Embedding a word in one column preserves its Hamming weight. -/
theorem matrixWeight_columnMatrix (u : I → ZMod 2) (j : J) :
    matrixWeight (columnMatrix u j) = hammingNorm u := by
  classical
  have hs : Finset.univ.filter
      (fun p : I × J => columnMatrix u j p.1 p.2 ≠ 0) =
      (Finset.univ.filter fun i => u i ≠ 0) ×ˢ {j} := by
    ext ⟨i, j'⟩
    by_cases hp : j' = j
    · simp [columnMatrix, Matrix.vecMulVec, Pi.single_apply, hp]
    · simp [columnMatrix, Matrix.vecMulVec, Pi.single_apply, hp, Ne.symm hp]
  unfold matrixWeight hammingNorm
  change (Finset.univ.filter (fun p : I × J => columnMatrix u j p.1 p.2 ≠ 0)).card = _
  rw [hs, Finset.card_product, Finset.card_singleton, mul_one]

/-- Swapping the two blocks and transposing preserves the cycle equation. -/
theorem isCycle_transpose_swap
    (A : Matrix I I (ZMod 2)) (B : Matrix J J (ZMod 2))
    (U V : Matrix I J (ZMod 2)) (hc : IsCycle A B U V) :
    IsCycle B A Vᵀ Uᵀ := by
  have h := congrArg Matrix.transpose hc
  simpa only [IsCycle, Matrix.transpose_add, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_zero, add_comm] using h

/-- Swapping blocks and transposing preserves the boundary condition. -/
theorem isBoundary_transpose_swap_iff
    (A : Matrix I I (ZMod 2)) (B : Matrix J J (ZMod 2))
    (U V : Matrix I J (ZMod 2)) :
    IsBoundary B A Vᵀ Uᵀ ↔ IsBoundary A B U V := by
  constructor
  · rintro ⟨S, hv, hu⟩
    refine ⟨Sᵀ, ?_, ?_⟩
    · simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using
        congrArg Matrix.transpose hu
    · simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using
        congrArg Matrix.transpose hv
  · rintro ⟨S, hu, hv⟩
    refine ⟨Sᵀ, ?_, ?_⟩
    · simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using
        congrArg Matrix.transpose hv
    · simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using
        congrArg Matrix.transpose hu

/-- A nonzero first-kernel word gives a nonboundary cycle of the same weight
whenever the second transpose kernel is nonzero. -/
theorem exists_cycle_of_kernel_word
    (A : Matrix I I (ZMod 2)) (B : Matrix J J (ZMod 2))
    (u : I → ZMod 2) (hu : A *ᵥ u = 0) (hu0 : u ≠ 0)
    (w : J → ZMod 2) (hw : Bᵀ *ᵥ w = 0) (hw0 : w ≠ 0) :
    ∃ U V : Matrix I J (ZMod 2), IsCycle A B U V ∧ ¬ IsBoundary A B U V ∧
      matrixWeight U + matrixWeight V = hammingNorm u := by
  classical
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw0
  have hj1 : w j = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hj
  have hc : IsCycle A B (columnMatrix u j) 0 := by
    simp only [IsCycle, columnMatrix, Matrix.mul_vecMulVec, hu,
      Matrix.zero_vecMulVec, Matrix.zero_mul, add_zero]
  refine ⟨columnMatrix u j, 0, hc, ?_, ?_⟩
  · intro hb
    have h := ((isBoundary_iff_contractions_vanish A B _ _ hc).mp hb).1 w hw
    apply hu0
    simpa only [columnMatrix, Matrix.vecMulVec_mulVec, single_dotProduct,
      one_mul, hj1, MulOpposite.op_one, one_smul] using h
  · rw [matrixWeight_columnMatrix, matrixWeight_zero, add_zero]

/-- A nonzero second-kernel word gives a nonboundary cycle of the same weight
whenever the first transpose kernel is nonzero. -/
theorem exists_cycle_of_second_kernel_word
    (A : Matrix I I (ZMod 2)) (B : Matrix J J (ZMod 2))
    (v : J → ZMod 2) (hv : B *ᵥ v = 0) (hv0 : v ≠ 0)
    (a : I → ZMod 2) (ha : Aᵀ *ᵥ a = 0) (ha0 : a ≠ 0) :
    ∃ U V : Matrix I J (ZMod 2), IsCycle A B U V ∧ ¬ IsBoundary A B U V ∧
      matrixWeight U + matrixWeight V = hammingNorm v := by
  obtain ⟨U, V, hc, hnb, hw⟩ := exists_cycle_of_kernel_word B A v hv hv0 a ha ha0
  refine ⟨Vᵀ, Uᵀ, isCycle_transpose_swap B A U V hc, ?_, ?_⟩
  · exact fun hb => hnb ((isBoundary_transpose_swap_iff B A U V).mp hb)
  · simpa only [matrixWeight_transpose, add_comm] using hw

/-- A singular square matrix also has a nonzero transpose-kernel word. -/
theorem exists_transpose_kernel_word
    {K : Type*} [Field K] (A : Matrix I I K)
    (u : I → K) (hu : A *ᵥ u = 0) (hu0 : u ≠ 0) :
    ∃ a : I → K, a ≠ 0 ∧ Aᵀ *ᵥ a = 0 := by
  classical
  apply Matrix.exists_mulVec_eq_zero_iff.mpr
  rw [Matrix.det_transpose]
  exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨u, hu0, hu⟩

/-- Exact classical kernel distances give the exact separable chain distance.
The transpose-kernel witnesses needed by the attainers follow from singularity
of the square parity-check matrices.
-/
theorem chain_distance_eq_min
    (A : Matrix I I (ZMod 2)) (B : Matrix J J (ZMod 2))
    (dA dB : ℕ)
    (hA : ∀ u, A *ᵥ u = 0 → u ≠ 0 → dA ≤ hammingNorm u)
    (hB : ∀ v, B *ᵥ v = 0 → v ≠ 0 → dB ≤ hammingNorm v)
    (u : I → ZMod 2) (hu : A *ᵥ u = 0) (hu0 : u ≠ 0) (huw : hammingNorm u = dA)
    (v : J → ZMod 2) (hv : B *ᵥ v = 0) (hv0 : v ≠ 0) (hvw : hammingNorm v = dB)
    : IsLeast {w : ℕ | ∃ U V : Matrix I J (ZMod 2),
      IsCycle A B U V ∧ ¬ IsBoundary A B U V ∧
      matrixWeight U + matrixWeight V = w} (min dA dB) := by
  obtain ⟨a, ha0, ha⟩ := exists_transpose_kernel_word A u hu hu0
  obtain ⟨b, hb0, hb⟩ := exists_transpose_kernel_word B v hv hv0
  constructor
  · rcases le_total dA dB with hle | hle
    · rw [min_eq_left hle, ← huw]
      exact exists_cycle_of_kernel_word A B u hu hu0 b hb hb0
    · rw [min_eq_right hle, ← hvw]
      exact exists_cycle_of_second_kernel_word A B v hv hv0 a ha ha0
  · rintro w ⟨U, V, hc, hnb, rfl⟩
    exact weight_ge_min_of_nonboundary_cycle A B dA dB hA hB U V hc hnb

end Quantum.Stabilizer.Homological.SeparableBB
