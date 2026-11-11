import QEC.Stabilizer.Framework.Homological.StabGroup
import QEC.Stabilizer.Framework.Symplectic.Presentation

/-!
# Presentations of homological CSS codes with independent checks

`generatorsList X` enumerates the checks of a `HomologicalCode X`: the Z-check
of every 0-cell and the X-check of every 2-cell (`cellGenerator`). When the
vertex cut map `cutMap` and the face boundary map `∂₂` are injective, these
checks are independent (`linearIndependent_cellGenerator`,
`rowsLinearIndependent_generatorsList`), and the list is a
`StabilizerCode.Presentation` (`presentation`) whose code has the stabilizer
subgroup of `homologicalStabilizerGroup X` (`presentation_toCode_subgroup`).

The symplectic vector of a chain operator is computed coordinate by coordinate
in `toSymplectic_chainXOperator_X`, `toSymplectic_chainXOperator_Z`,
`toSymplectic_chainZOperator_X` and `toSymplectic_chainZOperator_Z`.
-/

namespace Quantum.Stabilizer.Homological.HomologicalCode

open scoped BigOperators
open NQubitPauliGroupElement NQubitPauliOperator

variable (X : HomologicalCode)

/-- The check of a cell: the Z-check of a 0-cell or the X-check of a
2-cell. -/
noncomputable def cellGenerator : X.C0 ⊕ X.C2 → NQubitPauliGroupElement X.numQubits :=
  Sum.elim X.vertexStabOf X.faceStabOf

/-- The canonical list of homological CSS checks. -/
noncomputable def generatorsList : List (NQubitPauliGroupElement X.numQubits) :=
  List.ofFn (fun i => X.cellGenerator ((Fintype.equivFin (X.C0 ⊕ X.C2)).symm i))

/-- There is one generator for every 0-cell and every 2-cell. -/
theorem generatorsList_length :
    X.generatorsList.length = Fintype.card X.C0 + Fintype.card X.C2 := by
  simp [generatorsList]

/-- The canonical list enumerates precisely the homological generators. -/
theorem listToSet_generatorsList :
    listToSet X.generatorsList = X.homologicalGenerators := by
  rw [generatorsList, listToSet_ofFn]
  exact ((Fintype.equivFin _).symm.surjective.range_comp X.cellGenerator).trans
    (Set.Sum.elim_range _ _)

/-- Every canonical homological generator has phase zero. -/
theorem generatorsList_phaseZero : AllPhaseZero X.generatorsList := by
  apply AllPhaseZero_ofFn
  intro i
  cases (Fintype.equivFin (X.C0 ⊕ X.C2)).symm i <;> rfl

/-- The canonical homological generators pairwise commute. -/
theorem generatorsList_commute :
    ∀ g ∈ X.generatorsList, ∀ h ∈ X.generatorsList, g * h = h * g := by
  change ∀ g ∈ listToSet X.generatorsList, ∀ h ∈ listToSet X.generatorsList, g * h = h * g
  rw [X.listToSet_generatorsList]
  exact homologicalGenerators_commute

/-! ## Symplectic coordinates of chain operators -/

/-- The X-coordinate of an encoded X-chain is its coefficient. -/
theorem toSymplectic_chainXOperator_X (c : X.C1 → ZMod 2) (e : X.C1) :
    toSymplectic (X.chainXOperator c).operators
      (Fin.castAdd X.numQubits (X.edgeEquiv e)) = c e := by
  rw [toSymplectic_X_part, chainXOperator_operators_edgeEquiv]
  obtain h | h := zmod2_eq_zero_or_eq_one (c e) <;> simp [h]

/-- The Z-coordinate of an encoded Z-chain is its coefficient. -/
theorem toSymplectic_chainZOperator_Z (c : X.C1 → ZMod 2) (e : X.C1) :
    toSymplectic (X.chainZOperator c).operators
      (Fin.natAdd X.numQubits (X.edgeEquiv e)) = c e := by
  rw [toSymplectic_Z_part, chainZOperator_operators_edgeEquiv]
  obtain h | h := zmod2_eq_zero_or_eq_one (c e) <;> simp [h]

/-- An encoded Z-chain has zero X-coordinates. -/
theorem toSymplectic_chainZOperator_X (c : X.C1 → ZMod 2) (q : Fin X.numQubits) :
    toSymplectic (X.chainZOperator c).operators (Fin.castAdd X.numQubits q) = 0 := by
  rcases (chainZOperator_isZType c).2 q with h | h <;> rw [toSymplectic_X_part, h] <;> rfl

/-- An encoded X-chain has zero Z-coordinates. -/
theorem toSymplectic_chainXOperator_Z (c : X.C1 → ZMod 2) (q : Fin X.numQubits) :
    toSymplectic (X.chainXOperator c).operators (Fin.natAdd X.numQubits q) = 0 := by
  rcases (chainXOperator_isXType c).2 q with h | h <;> rw [toSymplectic_Z_part, h] <;> rfl

/-! ## Independence of the checks -/

/-- If `cutMap` and `∂₂` are injective, the symplectic vectors of the checks
are linearly independent: a vanishing combination of them vanishes on the Z
block, where it is the cut of its vertex coefficients, and on the X block,
where it is the boundary of its face coefficients. -/
theorem linearIndependent_cellGenerator
    (hcut : Function.Injective X.cutMap) (hboundary : Function.Injective X.boundary2) :
    LinearIndependent (ZMod 2) (fun i => toSymplectic (X.cellGenerator i).operators) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hsum i
  have hZ : X.cutMap (fun v => c (.inl v)) = 0 := by
    ext e
    have hcol := congr_fun hsum (Fin.natAdd X.numQubits (X.edgeEquiv e))
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Fintype.sum_sum_type, cellGenerator, Sum.elim_inl, Sum.elim_inr,
      vertexStabOf, faceStabOf, toSymplectic_chainZOperator_Z,
      toSymplectic_chainXOperator_Z, mul_zero, Finset.sum_const_zero, add_zero] at hcol
    rw [linearMap_apply_eq_sum_single]
    simpa only [singleVtx] using hcol
  have hX : X.boundary2 (fun f => c (.inr f)) = 0 := by
    ext e
    have hcol := congr_fun hsum (Fin.castAdd X.numQubits (X.edgeEquiv e))
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Fintype.sum_sum_type, cellGenerator, Sum.elim_inl, Sum.elim_inr,
      vertexStabOf, faceStabOf, toSymplectic_chainZOperator_X,
      toSymplectic_chainXOperator_X, mul_zero, Finset.sum_const_zero, zero_add] at hcol
    rw [linearMap_apply_eq_sum_single]
    simpa only [singleFace] using hcol
  cases i with
  | inl v => exact congr_fun (hcut (hZ.trans (map_zero X.cutMap).symm)) v
  | inr f => exact congr_fun (hboundary (hX.trans (map_zero X.boundary2).symm)) f

/-- If `cutMap` and `∂₂` are injective, the check matrix of the canonical list
has independent rows. -/
theorem rowsLinearIndependent_generatorsList
    (hcut : Function.Injective X.cutMap) (hboundary : Function.Injective X.boundary2) :
    rowsLinearIndependent X.generatorsList := by
  rw [generatorsList, List.ofFn_eq_map]
  exact rowsLinearIndependent_map_of_nodup
    ((X.linearIndependent_cellGenerator hcut hboundary).comp _
      (Fintype.equivFin (X.C0 ⊕ X.C2)).symm.injective) (List.nodup_finRange _)

/-- The presentation of a homological CSS code by its canonical checks, given
that they are independent (`cutMap` and `∂₂` injective) and that their number
is `numQubits - k`. -/
noncomputable def presentation (k : ℕ) (hk : k ≤ X.numQubits)
    (hcard : Fintype.card X.C0 + Fintype.card X.C2 = X.numQubits - k)
    (hcut : Function.Injective X.cutMap) (hboundary : Function.Injective X.boundary2) :
    StabilizerGroup.StabilizerCode.Presentation X.numQubits k where
  hk := hk
  generatorsList := X.generatorsList
  generators_length := X.generatorsList_length.trans hcard
  generators_phaseZero := X.generatorsList_phaseZero
  generators_independent := X.rowsLinearIndependent_generatorsList hcut hboundary
  generators_commute := X.generatorsList_commute

/-- The presented code has the same subgroup as the homological CSS code. -/
theorem presentation_toCode_subgroup (k : ℕ) (hk : k ≤ X.numQubits)
    (hcard : Fintype.card X.C0 + Fintype.card X.C2 = X.numQubits - k)
    (hcut : Function.Injective X.cutMap) (hboundary : Function.Injective X.boundary2) :
    (X.presentation k hk hcard hcut hboundary).toCode.toStabilizerGroup.toSubgroup =
      X.homologicalStabilizerGroup.toSubgroup :=
  congrArg Subgroup.closure X.listToSet_generatorsList

end Quantum.Stabilizer.Homological.HomologicalCode
