import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.TopFiberBoundary
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Packaging
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Fibers
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Join
import QEC.Stabilizer.Framework.Homological.Certificate.MaskSpan
import QEC.Stabilizer.Framework.Homological.Certificate.SearchInitial

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open F2Mask FiberData
set_option maxRecDepth 200000

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Each packed column of the full top boundary matrix is a physical stabilizer boundary. -/
theorem boundaryColumns_mem : ∀ p ∈ boundaryColumns,
    chainOfMask qubitEnum p.2 ∈ complex.boundaries := by
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  rw [← faceRow_certificate]
  exact ⟨Pi.single (faceEnum.symm i) 1, boundary2_single_eq_faceRow _⟩

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- An arbitrary packed face combination witnesses physical boundary membership. -/
theorem boundary_of_recon_witness (v : Group × Fin 2 → ZMod 2) (coeff : Nat)
    (h : reconX boundaryColumns coeff = maskOf qubitEnum v) :
    v ∈ complex.boundaries := by
  have hb := chainOfMask_reconX_mem qubitEnum complex.boundaries
    boundaryColumns boundaryColumns_mem coeff
  rwa [h, chainOfMask_maskOf] at hb

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- A certified affine fiber statement applies to the actual first sheet and shadow
of every physical cycle in that fiber. -/
theorem topFiberBoundary_apply {beta : Nat} (hbeta : TopFiberBoundary beta)
    {v : Group × Fin 2 → ZMod 2} (hv : v ∈ complex.cycles)
    (hw : complex.chainWeight v ≤ 22)
    (hshadow : maskOf middleQubitEnum (topCover.push1 v) = beta) :
    v ∈ complex.boundaries := by
  obtain ⟨coeff, hc⟩ := hbeta (maskOf middleQubitEnum (topCover.sheet0 v))
    (maskOf_lt _ _) (by rw [top_fiber_equation hv, hshadow]) (by
      rw [outsideMask_eq_and_complement (maskOf_lt _ _)]
      have h := topCover.mask_overflow_le middleQubitEnum v hw
      rwa [hshadow] at h)
  apply boundary_of_recon_witness v coeff
  rw [maskOf_top_eq_join, hshadow]
  exact hc

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- An empty packed fiber excludes physical cycles with the matching overflow budget. -/
theorem topFiberEmpty_apply {beta cap : Nat}
    (hempty : ∀ word : Nat, word < 2 ^ 180 →
      reconX topEColumns word = reconX topRColumns beta →
      bitCount 180 (outsideMask word beta) ≤ cap → False)
    (hcap : (22 - bitCount 180 beta) / 2 ≤ cap)
    {v : Group × Fin 2 → ZMod 2} (hv : v ∈ complex.cycles)
    (hw : complex.chainWeight v ≤ 22)
    (hshadow : maskOf middleQubitEnum (topCover.push1 v) = beta) : False := by
  apply hempty (maskOf middleQubitEnum (topCover.sheet0 v)) (maskOf_lt _ _)
  · rw [top_fiber_equation hv, hshadow]
  · rw [outsideMask_eq_and_complement (maskOf_lt _ _)]
    have h := topCover.mask_overflow_le middleQubitEnum v hw
    rw [hshadow] at h
    exact h.trans hcap

end Quantum.Stabilizer.Homological.BB.Bravyi360
