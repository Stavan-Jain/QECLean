import QEC.Stabilizer.Codes.RotatedSurface.ChainComplex
import QEC.Stabilizer.Geometry.GridIndexing

/-!
# The rotated surface code has one logical qubit

For odd `L`, the checks of the rotated surface code are independent: the
X-check combination map `∂₂` and the Z-check combination map `δ⁰` are
injective (`rscBoundary2_injective`, `rscZCutMap_injective`). As there are
`L * L - 1` checks on `L * L` qubits, the first homology has dimension one
(`rsc_finrank_H1_eq_one`).

Independence is a triangularity argument
(`eq_zero_of_sum_indicator_eq_zero`). Number the qubits row by row and call
the first qubit of a check its anchor. Two checks of the same type have
different anchors, so in a nonzero combination of checks of one type, the
anchor of the check with the smallest anchor lies in no other check of the
combination, and the combination does not vanish there. In terms of the block
`(a, b)` of a check (`zFaceCorner`, `xFaceCorner`), the anchor is the qubit
`(a - 1, b - 1)`, with number `blockKey L (a, b)`.

The ranks follow: `rsc_rank_boundary2`, `rsc_rank_zCutMap`,
`rsc_rank_boundary1`, `rsc_finrank_cycles`, `rsc_finrank_boundaries` and
`rsc_finrank_cycles_eq_boundaries_add_one`.
-/

namespace Quantum
namespace Stabilizer
namespace Lattice
namespace RotatedSurface

open scoped Homology
open scoped RotatedSurfaceChain

/-! ## Triangularity -/

/-- **Triangularity criterion.** Let `S i` be finite sets of points numbered
by `idx`, such that `S i` has a point of number `key i` and no point of
smaller number, with `key` injective. Then the indicator functions of the
`S i` are linearly independent over `ZMod 2`: a combination `c` of them that
vanishes at every point is zero. -/
lemma eq_zero_of_sum_indicator_eq_zero {ι V : Type*} [Fintype ι] [DecidableEq V]
    {S : ι → Finset V} {idx : V → ℕ} {key : ι → ℕ} (hkey : Function.Injective key)
    (hmem : ∀ i, ∃ v ∈ S i, idx v = key i) (hle : ∀ i, ∀ v ∈ S i, key i ≤ idx v)
    {c : ι → ZMod 2} (hc : ∀ v, ∑ i, c i * (if v ∈ S i then 1 else 0) = 0) :
    c = 0 := by
  by_contra hne
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hne
  obtain ⟨m, hm, hmin⟩ := (Finset.univ.filter fun i => c i ≠ 0).exists_min_image key
    ⟨i₀, by simpa using hi₀⟩
  obtain ⟨v, hv, hvm⟩ := hmem m
  refine (Finset.mem_filter.mp hm).2 ?_
  rw [← hc v, Fintype.sum_eq_single m, if_pos hv, mul_one]
  intro j hjm
  by_cases hj : c j = 0
  · rw [hj, zero_mul]
  · rw [if_neg, mul_zero]
    exact fun hvj => hjm (hkey (le_antisymm (hvm ▸ hle j v hvj) (hmin j (by simpa using hj))))

/-! ## Anchors of blocks -/

variable {L : ℕ}

/-- The number `(b - 1) * L + (a - 1)` of the first qubit `(a - 1, b - 1)` of
the block `p = (a, b)`. The subtractions are truncated, so this is also the
first qubit of a block that sticks out of the grid at the left or at the
top. -/
def blockKey (L : ℕ) (p : ℕ × ℕ) : ℕ := (p.2 - 1) * L + (p.1 - 1)

/-- A block within one step of the grid contains its first qubit. -/
private lemma exists_mem_block_number_eq (hL : 0 < L) {p : ℕ × ℕ} (h1 : p.1 ≤ L)
    (h2 : p.2 ≤ L) : ∃ v ∈ block L p, v.2.val * L + v.1.val = blockKey L p :=
  ⟨(⟨p.1 - 1, by omega⟩, ⟨p.2 - 1, by omega⟩), by simp only [mem_block]; omega, rfl⟩

/-- No qubit of a block comes before its first qubit. -/
private lemma blockKey_le {p : ℕ × ℕ} {v : VtxIdx L} (hv : v ∈ block L p) :
    blockKey L p ≤ v.2.val * L + v.1.val := by
  rw [mem_block] at hv
  exact Nat.add_le_add (Nat.mul_le_mul_right L (by omega)) (by omega)

/-- Blocks within one step of the grid with the same first qubit have the same
corner, up to the truncation at the left and at the top. -/
private lemma pred_eq_of_blockKey_eq (hL : 0 < L) {p q : ℕ × ℕ}
    (hp : p.1 ≤ L ∧ p.2 ≤ L) (hq : q.1 ≤ L ∧ q.2 ≤ L) (h : blockKey L p = blockKey L q) :
    p.1 - 1 = q.1 - 1 ∧ p.2 - 1 = q.2 - 1 := by
  haveI : Fact (0 < L) := ⟨hL⟩
  simpa [Prod.ext_iff, Fin.ext_iff] using
    rowMajor_injective L (a₁ := (⟨p.1 - 1, by omega⟩, ⟨p.2 - 1, by omega⟩))
      (a₂ := (⟨q.1 - 1, by omega⟩, ⟨q.2 - 1, by omega⟩)) h

/-- The indicator functions of a family of blocks within one step of the grid
and with distinct first qubits are linearly independent. -/
private lemma eq_zero_of_sum_block_indicator_eq_zero {ι : Type*} [Fintype ι] (hL : 0 < L)
    {corner : ι → ℕ × ℕ} (hkey : Function.Injective fun i => blockKey L (corner i))
    (hle : ∀ i, (corner i).1 ≤ L ∧ (corner i).2 ≤ L) {c : ι → ZMod 2}
    (hc : ∀ v : VtxIdx L, ∑ i, c i * (if v ∈ block L (corner i) then 1 else 0) = 0) :
    c = 0 :=
  eq_zero_of_sum_indicator_eq_zero (idx := fun v : VtxIdx L => v.2.val * L + v.1.val) hkey
    (fun i => exists_mem_block_number_eq hL (hle i).1 (hle i).2) (fun _ _ hv => blockKey_le hv) hc

variable [Fact (Odd L)]

/-- Distinct X-checks have distinct anchors. -/
lemma blockKey_xFaceCorner_injective :
    Function.Injective fun xf : XFaceIdx L => blockKey L (xFaceCorner xf) := by
  intro xf xf' h
  have hb := xFaceCorner_bounds xf
  have hb' := xFaceCorner_bounds xf'
  have hp := xFaceCorner_parity xf
  have hp' := xFaceCorner_parity xf'
  obtain ⟨h1, h2⟩ := pred_eq_of_blockKey_eq (by omega) ⟨hb.2.1.le, hb.2.2⟩
    ⟨hb'.2.1.le, hb'.2.2⟩ h
  exact xFaceCorner_injective (Prod.ext (by omega) (by omega))

/-- Distinct Z-checks have distinct anchors. -/
lemma blockKey_zFaceCorner_injective :
    Function.Injective fun zf : ZFaceIdx L => blockKey L (zFaceCorner zf) := by
  intro zf zf' h
  have hb := zFaceCorner_bounds zf
  have hb' := zFaceCorner_bounds zf'
  have hp := zFaceCorner_parity zf
  have hp' := zFaceCorner_parity zf'
  obtain ⟨h1, h2⟩ := pred_eq_of_blockKey_eq (by omega) ⟨hb.1, hb.2.2.le⟩
    ⟨hb'.1, hb'.2.2.le⟩ h
  exact zFaceCorner_injective (Prod.ext (by omega) (by omega))

/-! ## Independence of the checks -/

/-- The X-checks are independent: `∂₂` is injective. -/
theorem rscBoundary2_injective : Function.Injective (∂₂ L) := by
  refine (injective_iff_map_eq_zero _).2 fun c hc => ?_
  refine eq_zero_of_sum_block_indicator_eq_zero (Fact.out : Odd L).pos
    blockKey_xFaceCorner_injective
    (fun xf => ⟨(xFaceCorner_bounds xf).2.1.le, (xFaceCorner_bounds xf).2.2⟩) fun v => ?_
  simpa only [rscBoundary2_apply, xFaceSupport_eq_block] using congrFun hc v

/-- The Z-checks are independent: `δ⁰` is injective. -/
theorem rscZCutMap_injective : Function.Injective (δ⁰ L) := by
  refine (injective_iff_map_eq_zero _).2 fun s hs => ?_
  refine eq_zero_of_sum_block_indicator_eq_zero (Fact.out : Odd L).pos
    blockKey_zFaceCorner_injective
    (fun zf => ⟨(zFaceCorner_bounds zf).1, (zFaceCorner_bounds zf).2.2.le⟩) fun v => ?_
  simpa only [rscZCutMap_apply, zFaceSupport_eq_block] using congrFun hs v

/-! ## Ranks and the dimension of `H₁` -/

/-- `rank ∂₂` is the number of X-checks. -/
theorem rsc_rank_boundary2 :
    dim₂ (LinearMap.range (∂₂ L)) = Fintype.card (XFaceIdx L) := by
  rw [LinearMap.finrank_range_of_inj rscBoundary2_injective,
    Module.finrank_fintype_fun_eq_card]

/-- `rank δ⁰` is the number of Z-checks. -/
theorem rsc_rank_zCutMap :
    dim₂ (LinearMap.range (δ⁰ L)) = Fintype.card (ZFaceIdx L) := by
  rw [LinearMap.finrank_range_of_inj rscZCutMap_injective,
    Module.finrank_fintype_fun_eq_card]

/-- `dim B₁` is the number of X-checks. -/
theorem rsc_finrank_boundaries : dim₂ (B₁ L) = Fintype.card (XFaceIdx L) :=
  rsc_rank_boundary2

variable [Fact (3 ≤ L)]

/-- `rank ∂₁` is the number of Z-checks: `∂₁` is the transpose of `δ⁰`. -/
theorem rsc_rank_boundary1 :
    dim₂ (LinearMap.range (∂₁ L)) = Fintype.card (ZFaceIdx L) := by
  rw [← rsc_rank_zCutMap, ← rotatedSurfaceHomologicalCode_cutMap_eq]
  exact (rotatedSurfaceHomologicalCode L).finrank_range_cutMap.symm

/-- `dim Z₁ = L * L - |ZFaceIdx L|`, by rank-nullity for `∂₁`. -/
theorem rsc_finrank_cycles :
    dim₂ (Z₁ L) = L * L - Fintype.card (ZFaceIdx L) := by
  have h : dim₂ (VtxIdx L → ZMod 2) = dim₂ (Z₁ L) + dim₂ (LinearMap.range (∂₁ L)) :=
    (rotatedSurfaceHomologicalCode L).rank_nullity_boundary1
  rw [rsc_rank_boundary1, Module.finrank_fintype_fun_eq_card, Fintype.card_prod,
    Fintype.card_fin] at h
  omega

/-- The boundaries have codimension one in the cycles: there are `L * L`
qubits and `L * L - 1` independent checks. -/
theorem rsc_finrank_cycles_eq_boundaries_add_one : dim₂ (Z₁ L) = dim₂ (B₁ L) + 1 := by
  have hcard := card_ZFaceIdx_add_card_XFaceIdx (L := L)
  have hL : 0 < L * L := Nat.mul_pos (Fact.out : Odd L).pos (Fact.out : Odd L).pos
  rw [rsc_finrank_cycles, rsc_finrank_boundaries]
  omega

/-- The rotated surface code has one logical qubit: `dim H₁ = 1`. -/
theorem rsc_finrank_H1_eq_one : dim₂ (H₁ L) = 1 := by
  have h : dim₂ (H₁ L) = dim₂ (Z₁ L) - dim₂ (B₁ L) :=
    (rotatedSurfaceHomologicalCode L).finrank_H1_eq_cycles_sub_boundaries
  rw [h, rsc_finrank_cycles_eq_boundaries_add_one, Nat.add_sub_cancel_left]

end RotatedSurface
end Lattice
end Stabilizer
end Quantum
