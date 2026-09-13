import QEC.Stabilizer.Framework.Homological.SeparableBB
import QEC.Stabilizer.Framework.Homological.BBDuality
import Mathlib.LinearAlgebra.Matrix.Circulant

/-!
# Separable BB convolution and matrix distance

Horizontal and vertical polynomial checks act by left and right circulant
matrix multiplication. The existing BB convention puts the matrix block `U`
in the right half and `V` in the left half. This is a physical relabeling and
preserves the sum of the two block weights.
-/

namespace Quantum.Stabilizer.Homological.SeparableBB

open Matrix HomologicalCode BB
open scoped BigOperators

variable {I J : Type} [Fintype I] [Fintype J] [AddCommGroup I] [AddCommGroup J]

/-- A one-variable check supported on the horizontal axis. -/
noncomputable def horizontal (f : I → ZMod 2) (p : I × J) : ZMod 2 := by
  classical
  exact if p.2 = 0 then f p.1 else 0

/-- A one-variable check supported on the vertical axis. -/
noncomputable def vertical (g : J → ZMod 2) (p : I × J) : ZMod 2 := by
  classical
  exact if p.1 = 0 then g p.2 else 0

/-- The BB chain complex with separated horizontal and vertical checks. -/
noncomputable def complex (f : I → ZMod 2) (g : J → ZMod 2) : HomologicalCode := by
  classical
  exact bbChainComplex (horizontal f) (vertical g)

/-- The right physical block is the matrix block acted on by the first check. -/
def firstMatrix (c : (I × J) × Fin 2 → ZMod 2) : Matrix I J (ZMod 2) :=
  fun i j => c ((i, j), 1)

/-- The left physical block is the matrix block acted on by the second check. -/
def secondMatrix (c : (I × J) × Fin 2 → ZMod 2) : Matrix I J (ZMod 2) :=
  fun i j => c ((i, j), 0)

/-- A physical BB chain from its two matrix blocks. -/
def chainOfMatrices (U V : Matrix I J (ZMod 2)) : (I × J) × Fin 2 → ZMod 2 :=
  fun p => if p.2 = 0 then V p.1.1 p.1.2 else U p.1.1 p.1.2

/-- Horizontal convolution is left circulant multiplication. -/
theorem conv_horizontal_eq (f : I → ZMod 2) (s : I × J → ZMod 2) (i : I) (j : J) :
    conv (horizontal f) s (i, j) =
      (Matrix.circulant f * Matrix.of (Function.curry s)) i j := by
  classical
  simp only [conv, horizontal, Fintype.sum_prod_type, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hs : ∀ a : I, (i, j) - (a, 0) = (i - a, j) :=
    fun a => Prod.ext rfl (sub_zero j)
  simp only [hs]
  change (∑ a : I, f a * s (i - a, j)) = _
  rw [Matrix.mul_apply]
  refine Fintype.sum_equiv (Equiv.subLeft i) _ _ ?_
  intro a
  simp only [Equiv.subLeft_apply, Matrix.circulant_apply, sub_sub_cancel,
    Matrix.of_apply, Function.curry_apply]

/-- Vertical convolution is right multiplication by the transpose circulant. -/
theorem conv_vertical_eq (g : J → ZMod 2) (s : I × J → ZMod 2) (i : I) (j : J) :
    conv (vertical g) s (i, j) =
      (Matrix.of (Function.curry s) * (Matrix.circulant g)ᵀ) i j := by
  classical
  simp only [conv, vertical, Fintype.sum_prod_type, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hs : ∀ b : J, (i, j) - (0, b) = (i, j - b) :=
    fun b => Prod.ext (sub_zero i) rfl
  simp only [hs]
  change (∑ b : J, g b * s (i, j - b)) = _
  rw [Matrix.mul_apply]
  refine Fintype.sum_equiv (Equiv.subLeft j) _ _ ?_
  intro b
  simp only [Equiv.subLeft_apply, Matrix.transpose_apply, Matrix.circulant_apply,
    sub_sub_cancel, Matrix.of_apply, Function.curry_apply, mul_comm]

/-- The BB cycle equation is the separable matrix cycle equation. -/
theorem mem_cycles_iff (f : I → ZMod 2) (g : J → ZMod 2)
    (c : (I × J) × Fin 2 → ZMod 2) :
    c ∈ (complex f g).cycles ↔
      IsCycle (Matrix.circulant f) (Matrix.circulant g) (firstMatrix c) (secondMatrix c) := by
  change bbBoundary1Fn (horizontal f) (vertical g) c = 0 ↔ _
  constructor
  · intro hc
    ext i j
    have h := congrFun hc (i, j)
    change conv (vertical g) (leftHalf c) (i, j) +
      conv (horizontal f) (rightHalf c) (i, j) = 0 at h
    rw [conv_horizontal_eq, conv_vertical_eq] at h
    exact (add_comm _ _).trans h
  · intro hc
    funext ⟨i, j⟩
    have h := congrFun (congrFun hc i) j
    change conv (vertical g) (leftHalf c) (i, j) +
      conv (horizontal f) (rightHalf c) (i, j) = 0
    rw [conv_horizontal_eq, conv_vertical_eq]
    exact (add_comm _ _).trans h

/-- The BB boundaries are exactly the separable matrix boundaries. -/
theorem mem_boundaries_iff (f : I → ZMod 2) (g : J → ZMod 2)
    (c : (I × J) × Fin 2 → ZMod 2) :
    c ∈ (complex f g).boundaries ↔
      IsBoundary (Matrix.circulant f) (Matrix.circulant g) (firstMatrix c) (secondMatrix c) := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨Matrix.of (Function.curry s), ?_, ?_⟩
    · ext i j
      have h := congrFun hs ((i, j), 1)
      change conv (vertical g) s (i, j) = c ((i, j), 1) at h
      simpa only [conv_vertical_eq] using h.symm
    · ext i j
      have h := congrFun hs ((i, j), 0)
      change conv (horizontal f) s (i, j) = c ((i, j), 0) at h
      simpa only [conv_horizontal_eq] using h.symm
  · rintro ⟨S, hU, hV⟩
    refine ⟨Function.uncurry S, ?_⟩
    funext ⟨⟨i, j⟩, b⟩
    fin_cases b
    · change conv (horizontal f) (Function.uncurry S) (i, j) = c ((i, j), 0)
      rw [conv_horizontal_eq]
      exact (congrFun (congrFun hV i) j).symm
    · change conv (vertical g) (Function.uncurry S) (i, j) = c ((i, j), 1)
      rw [conv_vertical_eq]
      exact (congrFun (congrFun hU i) j).symm

/-- The two matrix blocks partition the physical support. -/
theorem chainWeight_eq (f : I → ZMod 2) (g : J → ZMod 2)
    (c : (I × J) × Fin 2 → ZMod 2) :
    (complex f g).chainWeight c = matrixWeight (firstMatrix c) + matrixWeight (secondMatrix c) := by
  classical
  simp only [HomologicalCode.chainWeight, HomologicalCode.chainSupport,
    matrixWeight, hammingNorm, Finset.card_eq_sum_ones, Finset.sum_filter]
  change (∑ p : (I × J) × Fin 2, if c p ≠ 0 then 1 else 0) = _
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Finset.sum_add_distrib]
  exact add_comm _ _

/-- Classical convolution kernel bounds imply the physical BB chain bound. -/
theorem chainWeight_ge_of_kernel_bounds
    (f : I → ZMod 2) (g : J → ZMod 2) (dA dB : ℕ)
    (hA : ∀ u, Matrix.circulant f *ᵥ u = 0 → u ≠ 0 → dA ≤ hammingNorm u)
    (hB : ∀ v, Matrix.circulant g *ᵥ v = 0 → v ≠ 0 → dB ≤ hammingNorm v)
    (c : (I × J) × Fin 2 → ZMod 2)
    (hc : c ∈ (complex f g).cycles) (hnb : c ∉ (complex f g).boundaries) :
    min dA dB ≤ (complex f g).chainWeight c := by
  rw [chainWeight_eq]
  exact weight_ge_min_of_nonboundary_cycle (Matrix.circulant f) (Matrix.circulant g)
    dA dB hA hB (firstMatrix c) (secondMatrix c)
    ((mem_cycles_iff f g c).mp hc) (fun h => hnb ((mem_boundaries_iff f g c).mpr h))

omit [Fintype I] [Fintype J] [AddCommGroup I] [AddCommGroup J] in
/-- Reading the first block of a constructed chain recovers its matrix. -/
@[simp] theorem firstMatrix_chainOfMatrices (U V : Matrix I J (ZMod 2)) :
    firstMatrix (chainOfMatrices U V) = U := rfl

omit [Fintype I] [Fintype J] [AddCommGroup I] [AddCommGroup J] in
/-- Reading the second block of a constructed chain recovers its matrix. -/
@[simp] theorem secondMatrix_chainOfMatrices (U V : Matrix I J (ZMod 2)) :
    secondMatrix (chainOfMatrices U V) = V := rfl

/-- Exact classical circulant distances give the exact BB chain distance. -/
theorem bb_chain_distance_eq_min
    (f : I → ZMod 2) (g : J → ZMod 2) (dA dB : ℕ)
    (hA : ∀ u, Matrix.circulant f *ᵥ u = 0 → u ≠ 0 → dA ≤ hammingNorm u)
    (hB : ∀ v, Matrix.circulant g *ᵥ v = 0 → v ≠ 0 → dB ≤ hammingNorm v)
    (u : I → ZMod 2) (hu : Matrix.circulant f *ᵥ u = 0)
    (hu0 : u ≠ 0) (huw : hammingNorm u = dA)
    (v : J → ZMod 2) (hv : Matrix.circulant g *ᵥ v = 0)
    (hv0 : v ≠ 0) (hvw : hammingNorm v = dB) :
    IsLeast {w : ℕ | ∃ c : (I × J) × Fin 2 → ZMod 2,
      c ∈ (complex f g).cycles ∧ c ∉ (complex f g).boundaries ∧
      (complex f g).chainWeight c = w} (min dA dB) := by
  have hdist := chain_distance_eq_min (Matrix.circulant f) (Matrix.circulant g)
    dA dB hA hB u hu hu0 huw v hv hv0 hvw
  constructor
  · obtain ⟨U, V, hc, hnb, hw⟩ := hdist.1
    refine ⟨chainOfMatrices U V, ?_, ?_, ?_⟩
    · exact (mem_cycles_iff f g _).mpr hc
    · exact fun hb => hnb ((mem_boundaries_iff f g _).mp hb)
    · rw [chainWeight_eq, firstMatrix_chainOfMatrices, secondMatrix_chainOfMatrices]
      exact hw
  · rintro w ⟨c, hc, hnb, rfl⟩
    exact chainWeight_ge_of_kernel_bounds f g dA dB hA hB c hc hnb

/-- Classical circulant kernel bounds control every nontrivial Pauli logical. -/
theorem logical_weight_ge_of_kernel_bounds
    (f : I → ZMod 2) (g : J → ZMod 2) (dA dB : ℕ)
    (hA : ∀ u, Matrix.circulant f *ᵥ u = 0 → u ≠ 0 → dA ≤ hammingNorm u)
    (hB : ∀ v, Matrix.circulant g *ᵥ v = 0 → v ≠ 0 → dB ≤ hammingNorm v)
    (p : NQubitPauliGroupElement (complex f g).numQubits)
    (hp : Quantum.StabilizerGroup.IsNontrivialLogicalOperator p
      (complex f g).homologicalStabilizerGroup) :
    min dA dB ≤ NQubitPauliGroupElement.weight p := by
  classical
  have hX : ∀ c ∈ (complex f g).cycles, c ∉ (complex f g).boundaries →
      min dA dB ≤ (complex f g).chainWeight c :=
    fun c hc hnb => chainWeight_ge_of_kernel_bounds f g dA dB hA hB c hc hnb
  have hZ := (BB.bb_cycle_bound_iff_dual_bound (horizontal f) (vertical g)
    (min dA dB)).mp hX
  exact HomologicalCode.chainWeight_lower_bound_transfers (complex f g)
    (min dA dB) hX hZ p hp

/-- Exact classical circulant distances give the exact Pauli distance of the
separable BB homological stabilizer group. -/
theorem bb_pauli_distance_eq_min
    (f : I → ZMod 2) (g : J → ZMod 2) (dA dB : ℕ)
    (hA : ∀ u, Matrix.circulant f *ᵥ u = 0 → u ≠ 0 → dA ≤ hammingNorm u)
    (hB : ∀ v, Matrix.circulant g *ᵥ v = 0 → v ≠ 0 → dB ≤ hammingNorm v)
    (u : I → ZMod 2) (hu : Matrix.circulant f *ᵥ u = 0)
    (hu0 : u ≠ 0) (huw : hammingNorm u = dA)
    (v : J → ZMod 2) (hv : Matrix.circulant g *ᵥ v = 0)
    (hv0 : v ≠ 0) (hvw : hammingNorm v = dB) :
    IsLeast {w : ℕ | ∃ p : NQubitPauliGroupElement (complex f g).numQubits,
      Quantum.StabilizerGroup.IsNontrivialLogicalOperator p
        (complex f g).homologicalStabilizerGroup ∧
      NQubitPauliGroupElement.weight p = w} (min dA dB) := by
  constructor
  · obtain ⟨c, hc, hnb, hw⟩ :=
      (bb_chain_distance_eq_min f g dA dB hA hB u hu hu0 huw v hv hv0 hvw).1
    refine ⟨(complex f g).chainXOperator c, ?_, ?_⟩
    · exact (HomologicalCode.chainXOperator_isNontrivialLogical_iff
        (X := complex f g) c).mpr ⟨hc, hnb⟩
    · simpa only [HomologicalCode.weight_chainXOperator (X := complex f g)] using hw
  · rintro w ⟨p, hp, rfl⟩
    exact logical_weight_ge_of_kernel_bounds f g dA dB hA hB p hp

end Quantum.Stabilizer.Homological.SeparableBB
