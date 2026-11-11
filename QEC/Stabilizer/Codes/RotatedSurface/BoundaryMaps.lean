import QEC.Stabilizer.Codes.RotatedSurface.CellComplex

/-!
# Boundary maps of the rotated surface code

The chain complex of the rotated surface code has the X-checks as 2-cells, the
qubits as 1-cells and the Z-checks as 0-cells, with chains taking values in
`ZMod 2`:

* `rscBoundary2 L` (`∂₂ L`) sends a combination of X-checks to the sum of
  their supports;
* `rscBoundary1 L` (`∂₁ L`) sends a set of qubits to its syndrome, the
  Z-checks meeting it in an odd number of qubits;
* `rscZCutMap L` (`δ⁰ L`), the transpose of `∂₁`, sends a combination of
  Z-checks to the sum of their supports.

The chain-complex law `∂₁ ∘ ∂₂ = 0` (`rscBoundary_comp_zero`) holds because a
Z-check and an X-check share an even number of qubits
(`even_card_zFaceSupport_inter_xFaceSupport`). In the same way, a combination
of X-checks has an even number of qubits in every row
(`sum_row_rscBoundary2`), and a combination of Z-checks in every column
(`sum_col_rscZCutMap`).
-/

namespace Quantum
namespace Stabilizer
namespace Lattice
namespace RotatedSurface

/-! ## The maps -/

/-- `∂₂ : C₂ → C₁`: a combination of X-checks is sent to the sum of their
supports. -/
def rscBoundary2 (L : ℕ) :
    (XFaceIdx L → ZMod 2) →ₗ[ZMod 2] (VtxIdx L → ZMod 2) where
  toFun c v := ∑ xf : XFaceIdx L, c xf * (if v ∈ xFaceSupport xf then 1 else 0)
  map_add' c d := by
    funext v
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    funext v
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      mul_assoc]

/-- `∂₁ : C₁ → C₀`: a chain of qubits is sent to its sum over the support of
each Z-check. -/
def rscBoundary1 (L : ℕ) :
    (VtxIdx L → ZMod 2) →ₗ[ZMod 2] (ZFaceIdx L → ZMod 2) where
  toFun c zf := ∑ v ∈ zFaceSupport zf, c v
  map_add' c d := by
    funext zf
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' a c := by
    funext zf
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

/-- The cut map `C₀ → C₁`, the transpose of `∂₁`: a combination of Z-checks is
sent to the sum of their supports. -/
def rscZCutMap (L : ℕ) :
    (ZFaceIdx L → ZMod 2) →ₗ[ZMod 2] (VtxIdx L → ZMod 2) where
  toFun s v := ∑ zf : ZFaceIdx L, s zf * (if v ∈ zFaceSupport zf then 1 else 0)
  map_add' s t := by
    funext v
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a s := by
    funext v
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      mul_assoc]

/-!
## Notation

The scoped `RotatedSurfaceChain` notation writes the three maps as `∂₂ L c`,
`∂₁ L c` and `δ⁰ L s`, mirroring the toric `ToricChain` scope. The lattice size
stays an explicit argument, and the notation is purely a display form:
`rscBoundary1` is still the name to use in `simp [rscBoundary1]`, `unfold` and
lemma names. Enable it with `open scoped RotatedSurfaceChain`.
-/

/-- `∂₂` is the rotated-surface face-boundary map `rscBoundary2 L`. Scoped:
`open scoped RotatedSurfaceChain`. -/
scoped[RotatedSurfaceChain] notation "∂₂" =>
  Quantum.Stabilizer.Lattice.RotatedSurface.rscBoundary2

/-- `∂₁` is the rotated-surface edge-boundary map `rscBoundary1 L`. Scoped:
`open scoped RotatedSurfaceChain`. -/
scoped[RotatedSurfaceChain] notation "∂₁" =>
  Quantum.Stabilizer.Lattice.RotatedSurface.rscBoundary1

/-- `δ⁰` is the rotated-surface Z-side cut map `rscZCutMap L`, the transpose
of `∂₁`. Scoped: `open scoped RotatedSurfaceChain`. -/
scoped[RotatedSurfaceChain] notation "δ⁰" =>
  Quantum.Stabilizer.Lattice.RotatedSurface.rscZCutMap

open scoped RotatedSurfaceChain

@[simp] lemma rscBoundary2_apply (L : ℕ) (c : XFaceIdx L → ZMod 2) (v : VtxIdx L) :
    ∂₂ L c v = ∑ xf : XFaceIdx L, c xf * (if v ∈ xFaceSupport xf then 1 else 0) := rfl

@[simp] lemma rscBoundary1_apply (L : ℕ) (c : VtxIdx L → ZMod 2) (zf : ZFaceIdx L) :
    ∂₁ L c zf = ∑ v ∈ zFaceSupport zf, c v := rfl

@[simp] lemma rscZCutMap_apply (L : ℕ) (s : ZFaceIdx L → ZMod 2) (v : VtxIdx L) :
    δ⁰ L s v = ∑ zf : ZFaceIdx L, s zf * (if v ∈ zFaceSupport zf then 1 else 0) := rfl

/-- The boundary of a single X-check is the indicator of its support. -/
lemma rscBoundary2_single (L : ℕ) (xf : XFaceIdx L) (v : VtxIdx L) :
    ∂₂ L (Pi.single xf 1) v = if v ∈ xFaceSupport xf then 1 else 0 := by
  rw [rscBoundary2_apply, Fintype.sum_eq_single xf fun xf' h => by
    rw [Pi.single_eq_of_ne h, zero_mul], Pi.single_eq_same, one_mul]

/-- The syndrome of a single qubit is the indicator of the Z-checks acting on
it. -/
lemma rscBoundary1_single (L : ℕ) (v : VtxIdx L) (zf : ZFaceIdx L) :
    ∂₁ L (Pi.single v 1) zf = if v ∈ zFaceSupport zf then 1 else 0 := by
  simp [Pi.single_apply]

/-- The cut of a single Z-check is the indicator of its support. -/
lemma rscZCutMap_single (L : ℕ) (zf : ZFaceIdx L) (v : VtxIdx L) :
    δ⁰ L (Pi.single zf 1) v = if v ∈ zFaceSupport zf then 1 else 0 := by
  rw [rscZCutMap_apply, Fintype.sum_eq_single zf fun zf' h => by
    rw [Pi.single_eq_of_ne h, zero_mul], Pi.single_eq_same, one_mul]

/-! ## The chain-complex law -/

/-- A combination of the indicator functions of sets `S i` sums to zero over a
set `T` that meets every `S i` in an even number of points. -/
lemma sum_sum_mul_indicator_eq_zero {ι V : Type*} [Fintype ι] [DecidableEq V]
    (T : Finset V) (S : ι → Finset V) (hS : ∀ i, Even (T ∩ S i).card) (c : ι → ZMod 2) :
    ∑ v ∈ T, ∑ i, c i * (if v ∈ S i then 1 else 0) = 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← Finset.mul_sum, Finset.sum_boole, Finset.filter_mem_eq_inter,
    (ZMod.natCast_eq_zero_iff_even).2 (hS i), mul_zero]

/-- Chain-complex law `∂₁ ∘ ∂₂ = 0`: the support of an X-check has zero
syndrome, since it meets every Z-check in an even number of qubits. -/
theorem rscBoundary_comp_zero (L : ℕ) [Fact (Odd L)] :
    (∂₁ L).comp (∂₂ L) = 0 :=
  LinearMap.ext fun c => funext fun zf =>
    sum_sum_mul_indicator_eq_zero _ _ (even_card_zFaceSupport_inter_xFaceSupport zf) c

/-- Pointwise form of `rscBoundary_comp_zero`. -/
theorem rscBoundary_comp_zero_apply (L : ℕ) [Fact (Odd L)]
    (c : XFaceIdx L → ZMod 2) :
    ∂₁ L (∂₂ L c) = 0 :=
  LinearMap.congr_fun (rscBoundary_comp_zero L) c

/-! ## Rows and columns -/

/-- A combination of X-checks has an even number of qubits in every row. -/
theorem sum_row_rscBoundary2 (L : ℕ) (c : XFaceIdx L → ZMod 2) (y : Fin L) :
    ∑ v : VtxIdx L with v.2 = y, ∂₂ L c v = 0 :=
  sum_sum_mul_indicator_eq_zero _ _ (fun xf => even_card_row_inter_xFaceSupport xf y) c

/-- A combination of Z-checks has an even number of qubits in every column. -/
theorem sum_col_rscZCutMap (L : ℕ) (s : ZFaceIdx L → ZMod 2) (x : Fin L) :
    ∑ v : VtxIdx L with v.1 = x, δ⁰ L s v = 0 :=
  sum_sum_mul_indicator_eq_zero _ _ (fun zf => even_card_col_inter_zFaceSupport zf x) s

end RotatedSurface
end Lattice
end Stabilizer
end Quantum
