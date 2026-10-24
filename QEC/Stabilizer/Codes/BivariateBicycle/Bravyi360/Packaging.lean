import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.Sparse
import QEC.Stabilizer.Codes.BivariateBicycle.Bravyi360.RankData
import QEC.Stabilizer.Framework.Homological.Certificate.MaskLinear
import QEC.Stabilizer.Framework.Homological.Certificate.TrimChecks
import QEC.Stabilizer.Framework.Homological.BBDuality
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance

noncomputable section

namespace Quantum.Stabilizer.Homological.BB.Bravyi360
open HomologicalCode F2Mask
open scoped BigOperators

set_option maxRecDepth 200000
set_option exponentiation.threshold 400

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/--
The 174 independent checks omit six dependent checks near the end of the
enumeration.
-/
noncomputable def keptIndex (i : Fin 174) : Fin 180 :=
  ⟨if i.val < 172 then i.val else i.val + 2, by split <;> omega⟩

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Group coordinates of the retained checks. -/
noncomputable def keptCheck (i : Fin 174) : Group := faceEnum.symm (keptIndex i)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/--
The retained face and vertex checks define a complex on the same 360 physical
qubits.
-/
noncomputable def trimmedComplex : HomologicalCode := complex.trimChecks keptCheck keptCheck

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- A packed X-check allRows entry fits within its specified bit width. -/
theorem allRowsXAt_lt (i : Nat) : RankData.allRowsXAt i < 2^360 :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- A packed X-check basis entry fits within its specified bit width. -/
theorem basisXAt_lt (i : Nat) : RankData.basisXAt i < 2^360 :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- A packed X-check coeff entry fits within its specified bit width. -/
theorem coeffXAt_lt (i : Nat) : RankData.coeffXAt i < 2^174 :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- A packed Z-check allRows entry fits within its specified bit width. -/
theorem allRowsZAt_lt (i : Nat) : RankData.allRowsZAt i < 2^360 :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- A packed Z-check basis entry fits within its specified bit width. -/
theorem basisZAt_lt (i : Nat) : RankData.basisZAt i < 2^360 :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- A packed Z-check coeff entry fits within its specified bit width. -/
theorem coeffZAt_lt (i : Nat) : RankData.coeffZAt i < 2^174 :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every full face row agrees with the packed finite rank certificate. -/
theorem faceRow_certificate : ∀ i : Fin 180,
    faceRow (faceEnum.symm i) = chainOfMask qubitEnum (RankData.allRowsXAt i) := by
  intro i
  apply maskOf_injective qubitEnum
  rw [maskOf_faceRow, maskOf_chainOfMask qubitEnum (allRowsXAt_lt i)]
  have h : ∀ i : Fin 180, faceMask (faceEnum.symm i) = RankData.allRowsXAt i := by decide +kernel
  exact h i

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every full vertex row agrees with the packed finite rank certificate. -/
theorem vertexRow_certificate : ∀ i : Fin 180,
    vertexRow (faceEnum.symm i) = chainOfMask qubitEnum (RankData.allRowsZAt i) := by
  intro i
  apply maskOf_injective qubitEnum
  rw [maskOf_vertexRow, maskOf_chainOfMask qubitEnum (allRowsZAt_lt i)]
  have h : ∀ i : Fin 180, vertexMask (faceEnum.symm i) = RankData.allRowsZAt i := by decide +kernel
  exact h i

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/--
Reconstruction of a single selected face coefficient reads its certified row.
-/
theorem basisX_single : ∀ i : Fin 174,
    reconX RankData.basisXList (2 ^ i.val) = RankData.basisXAt i := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/--
Reconstruction of a single selected vertex coefficient reads its certified
row.
-/
theorem basisZ_single : ∀ i : Fin 174,
    reconX RankData.basisZList (2 ^ i.val) = RankData.basisZAt i := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The selected face row indices agree with the basis table. -/
theorem basisX_selected : ∀ i : Fin 174,
    RankData.allRowsXAt (keptIndex i) = RankData.basisXAt i := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The selected vertex row indices agree with the basis table. -/
theorem basisZ_selected : ∀ i : Fin 174,
    RankData.allRowsZAt (keptIndex i) = RankData.basisZAt i := by decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The face decoder is a left inverse on every retained face row. -/
theorem decoderX_certificate : ∀ i : Fin 174,
    reconX RankData.decoderXList (RankData.basisXAt i) = 2 ^ i.val := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The vertex decoder is a left inverse on every retained vertex row. -/
theorem decoderZ_certificate : ∀ i : Fin 174,
    reconX RankData.decoderZList (RankData.basisZAt i) = 2 ^ i.val := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- All original face rows are generated by retained face rows. -/
theorem spanningX_certificate : ∀ i : Fin 180,
    reconX RankData.basisXList (RankData.coeffXAt i) = RankData.allRowsXAt i := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- All original vertex rows are generated by retained vertex rows. -/
theorem spanningZ_certificate : ∀ i : Fin 180,
    reconX RankData.basisZList (RankData.coeffZAt i) = RankData.allRowsZAt i := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Boundary reconstruction from the certified selected face rows. -/
theorem trimmed_boundary2_eq : trimmedComplex.boundary2 =
    reconLinear (Equiv.refl (Fin 174)) qubitEnum RankData.basisXList := by
  apply linearMap_eq_of_single
  intro i
  change (complex.trimChecks keptCheck keptCheck).boundary2 (Pi.single i 1) = _
  rw [trimChecks_boundary2_single, boundary2_single_eq_faceRow]
  rw [keptCheck, faceRow_certificate, basisX_selected]
  change _ = chainOfMask qubitEnum
    (reconX RankData.basisXList (maskOf (Equiv.refl (Fin 174)) (Pi.single i 1)))
  rw [maskOf_single, basisX_single]
  rfl

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Cut reconstruction from the certified selected vertex rows. -/
theorem trimmed_cutMap_eq : trimmedComplex.cutMap =
    reconLinear (Equiv.refl (Fin 174)) qubitEnum RankData.basisZList := by
  apply linearMap_eq_of_single
  intro i
  change (complex.trimChecks keptCheck keptCheck).cutMap (Pi.single i 1) = _
  rw [trimChecks_cutMap_single, cutMap_single_eq_vertexRow]
  rw [keptCheck, vertexRow_certificate, basisZ_selected]
  change _ = chainOfMask qubitEnum
    (reconX RankData.basisZList (maskOf (Equiv.refl (Fin 174)) (Pi.single i 1)))
  rw [maskOf_single, basisZ_single]
  rfl

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- All 180 face columns, indexed by their reflected certificate coordinate. -/
noncomputable def boundaryColumns : List (Nat × Nat) :=
  List.ofFn fun i : Fin 180 => (i.val, RankData.allRowsXAt i)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Reconstruction of a full face point mass selects its certified row. -/
theorem boundaryColumns_single : ∀ i : Fin 180,
    reconX boundaryColumns (2^i.val) = RankData.allRowsXAt i := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/--
The full face boundary is the linear reconstruction map of the packed columns.
-/
theorem boundary2_eq_reconLinear : complex.boundary2 =
    reconLinear faceEnum qubitEnum boundaryColumns := by
  apply linearMap_eq_of_single
  intro g
  rw [boundary2_single_eq_faceRow]
  change faceRow g = chainOfMask qubitEnum
    (reconX boundaryColumns (maskOf faceEnum (Pi.single g 1)))
  rw [maskOf_single, boundaryColumns_single]
  simpa using faceRow_certificate (faceEnum g)

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/--
A packed face coefficient witness proves that a chain is a stabilizer
boundary.
-/
theorem mem_boundary_of_mask_witness (v : Group × Fin 2 → ZMod 2) (coeff : Nat)
    (hcoeff : coeff < 2^180)
    (h : reconX boundaryColumns coeff = maskOf qubitEnum v) :
    v ∈ complex.boundaries := by
  refine ⟨chainOfMask faceEnum coeff, ?_⟩
  rw [boundary2_eq_reconLinear]
  change chainOfMask qubitEnum
    (reconX boundaryColumns (maskOf faceEnum (chainOfMask faceEnum coeff))) = v
  rw [maskOf_chainOfMask faceEnum hcoeff, h, chainOfMask_maskOf]

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 174 retained face checks are independent. -/
theorem trimmed_boundary2_injective : Function.Injective trimmedComplex.boundary2 := by
  apply injective_of_decoder_single trimmedComplex.boundary2
    (reconLinear qubitEnum (Equiv.refl (Fin 174)) RankData.decoderXList)
  intro i
  rw [trimmed_boundary2_eq]
  change chainOfMask (Equiv.refl (Fin 174))
    (reconX RankData.decoderXList (maskOf qubitEnum
      (chainOfMask qubitEnum (reconX RankData.basisXList
        (maskOf (Equiv.refl (Fin 174)) (Pi.single i 1)))))) = _
  rw [maskOf_single, basisX_single]
  simp only [Equiv.refl_apply]
  rw [maskOf_chainOfMask qubitEnum (basisXAt_lt (i : Fin 174).val), decoderX_certificate]
  exact chainOfMask_two_pow (Equiv.refl (Fin 174)) i

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The 174 retained vertex checks are independent. -/
theorem trimmed_cutMap_injective : Function.Injective trimmedComplex.cutMap := by
  apply injective_of_decoder_single trimmedComplex.cutMap
    (reconLinear qubitEnum (Equiv.refl (Fin 174)) RankData.decoderZList)
  intro i
  rw [trimmed_cutMap_eq]
  change chainOfMask (Equiv.refl (Fin 174))
    (reconX RankData.decoderZList (maskOf qubitEnum
      (chainOfMask qubitEnum (reconX RankData.basisZList
        (maskOf (Equiv.refl (Fin 174)) (Pi.single i 1)))))) = _
  rw [maskOf_single, basisZ_single]
  simp only [Equiv.refl_apply]
  rw [maskOf_chainOfMask qubitEnum (basisZAt_lt (i : Fin 174).val), decoderZ_certificate]
  exact chainOfMask_two_pow (Equiv.refl (Fin 174)) i

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every original face boundary is a boundary in the trimmed complex. -/
theorem original_face_mem_trimmed (g : Group) :
    complex.boundary2 (Pi.single g 1) ∈ trimmedComplex.boundaries := by
  refine ⟨chainOfMask (Equiv.refl (Fin 174)) (RankData.coeffXAt (faceEnum g)), ?_⟩
  rw [trimmed_boundary2_eq, boundary2_single_eq_faceRow]
  change chainOfMask qubitEnum (reconX RankData.basisXList
    (maskOf (Equiv.refl (Fin 174)) (chainOfMask (Equiv.refl (Fin 174))
      (RankData.coeffXAt (faceEnum g))))) = _
  rw [maskOf_chainOfMask _ (coeffXAt_lt (faceEnum g)), spanningX_certificate]
  simpa using (faceRow_certificate (faceEnum g)).symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- Every original vertex cut is a cut in the trimmed complex. -/
theorem original_vertex_mem_trimmed (g : Group) :
    complex.cutMap (Pi.single g 1) ∈ LinearMap.range trimmedComplex.cutMap := by
  refine ⟨chainOfMask (Equiv.refl (Fin 174)) (RankData.coeffZAt (faceEnum g)), ?_⟩
  rw [trimmed_cutMap_eq, cutMap_single_eq_vertexRow]
  change chainOfMask qubitEnum (reconX RankData.basisZList
    (maskOf (Equiv.refl (Fin 174)) (chainOfMask (Equiv.refl (Fin 174))
      (RankData.coeffZAt (faceEnum g))))) = _
  rw [maskOf_chainOfMask _ (coeffZAt_lt (faceEnum g)), spanningZ_certificate]
  simpa using (vertexRow_certificate (faceEnum g)).symm

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/--
The trimmed presentation generates exactly the original BB stabilizer
subgroup.
-/
theorem trimmed_stabilizer_eq : trimmedComplex.homologicalStabilizerGroup.toSubgroup =
    complex.homologicalStabilizerGroup.toSubgroup :=
  trimChecks_stabilizer_eq complex keptCheck keptCheck
    original_vertex_mem_trimmed original_face_mem_trimmed

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/--
A canonical 348-generator presentation of the 360-qubit,12-logical-qubit code.
-/
noncomputable def codePresentation : Quantum.StabilizerGroup.StabilizerCode.Presentation 360 12 :=
  trimmedComplex.presentation 12 (by decide) (by decide)
    trimmed_cutMap_injective trimmed_boundary2_injective

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/--
The canonical stabilizer code is derived from its independent generator list.
-/
noncomputable def stabilizerCode : Quantum.StabilizerGroup.StabilizerCode 360 12 :=
  codePresentation.toCode

set_option maxHeartbeats 0 in
-- Elaborating this packed certificate can exceed the default heartbeat budget.
/-- The packaged stabilizer code is the BB homological stabilizer code. -/
theorem stabilizerCode_subgroup : stabilizerCode.toStabilizerGroup.toSubgroup =
    complex.homologicalStabilizerGroup.toSubgroup := by
  exact (trimmedComplex.presentation_toCode_subgroup 12 (by decide) (by decide)
    trimmed_cutMap_injective trimmed_boundary2_injective).trans trimmed_stabilizer_eq

end Quantum.Stabilizer.Homological.BB.Bravyi360

#print axioms Quantum.Stabilizer.Homological.BB.Bravyi360.trimmed_boundary2_injective
#print axioms Quantum.Stabilizer.Homological.BB.Bravyi360.stabilizerCode_subgroup
