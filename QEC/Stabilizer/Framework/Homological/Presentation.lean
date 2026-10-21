import QEC.Stabilizer.Framework.Homological.StabGroup
import QEC.Stabilizer.Framework.Symplectic.Presentation

/-!
# Presentations of homological CSS codes

If the face-boundary map and the vertex cut map are injective, all the
canonical CSS checks are independent. Enumerating those checks therefore
gives a stabilizer-code presentation with one generator per 0-cell and per
2-cell. The resulting code uses `mkStabilizerFromGenerators`, and its
stabilizer subgroup agrees with the abstract homological construction.
-/

namespace Quantum.Stabilizer.Homological.HomologicalCode

open scoped BigOperators
open NQubitPauliGroupElement NQubitPauliOperator

variable (X : HomologicalCode)

/-- The Z-check or X-check associated to a 0-cell or 2-cell. -/
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
  classical
  ext g
  simp only [listToSet, generatorsList, List.mem_ofFn, Set.mem_setOf_eq,
    homologicalGenerators, ZGenerators, XGenerators, Set.mem_union, Set.mem_range]
  constructor
  · rintro ⟨i, hi⟩
    cases h : (Fintype.equivFin (X.C0 ⊕ X.C2)).symm i with
    | inl v => exact Or.inl ⟨v, by simpa [cellGenerator, h] using hi⟩
    | inr f => exact Or.inr ⟨f, by simpa [cellGenerator, h] using hi⟩
  · rintro (⟨v, rfl⟩ | ⟨f, rfl⟩)
    · exact ⟨Fintype.equivFin (X.C0 ⊕ X.C2) (.inl v), by simp [cellGenerator]⟩
    · exact ⟨Fintype.equivFin (X.C0 ⊕ X.C2) (.inr f), by simp [cellGenerator]⟩

/-- Every canonical homological generator has phase zero. -/
theorem generatorsList_phaseZero : AllPhaseZero X.generatorsList := by
  apply AllPhaseZero_ofFn
  intro i
  cases (Fintype.equivFin (X.C0 ⊕ X.C2)).symm i <;> rfl

/-- The canonical homological generators pairwise commute. -/
theorem generatorsList_commute :
    ∀ g ∈ X.generatorsList, ∀ h ∈ X.generatorsList, g * h = h * g := by
  intro g hg h hh
  apply homologicalGenerators_commute
  · rw [← X.listToSet_generatorsList]
    exact hg
  · rw [← X.listToSet_generatorsList]
    exact hh

/-- The X-coordinate of an encoded X-chain is its coefficient. -/
theorem toSymplectic_chainXOperator_X (c : X.C1 → ZMod 2) (e : X.C1) :
    toSymplectic (X.chainXOperator c).operators
      (Fin.castAdd X.numQubits (X.edgeEquiv e)) = c e := by
  rw [toSymplectic_X_part]
  have h : (∃ e', X.edgeEquiv e' = X.edgeEquiv e ∧ c e' = 1) ↔ c e = 1 := by
    constructor
    · rintro ⟨e', he, hc⟩
      exact X.edgeEquiv.injective he ▸ hc
    · intro hc
      exact ⟨e, rfl, hc⟩
  change (if ∃ e', X.edgeEquiv e' = X.edgeEquiv e ∧ c e' = 1
    then PauliOperator.X else PauliOperator.I).toSymplecticSingle.1 = c e
  simp only [h]
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (c e) with h0 | h1
  · simp [h0, PauliOperator.toSymplecticSingle]
  · simp [h1, PauliOperator.toSymplecticSingle]

/-- The Z-coordinate of an encoded Z-chain is its coefficient. -/
theorem toSymplectic_chainZOperator_Z (c : X.C1 → ZMod 2) (e : X.C1) :
    toSymplectic (X.chainZOperator c).operators
      (Fin.natAdd X.numQubits (X.edgeEquiv e)) = c e := by
  rw [toSymplectic_Z_part]
  have h : (∃ e', X.edgeEquiv e' = X.edgeEquiv e ∧ c e' = 1) ↔ c e = 1 := by
    constructor
    · rintro ⟨e', he, hc⟩
      exact X.edgeEquiv.injective he ▸ hc
    · intro hc
      exact ⟨e, rfl, hc⟩
  change (if ∃ e', X.edgeEquiv e' = X.edgeEquiv e ∧ c e' = 1
    then PauliOperator.Z else PauliOperator.I).toSymplecticSingle.2 = c e
  simp only [h]
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (c e) with h0 | h1
  · simp [h0, PauliOperator.toSymplecticSingle]
  · simp [h1, PauliOperator.toSymplecticSingle]

/-- An encoded Z-chain has zero X-coordinate. -/
theorem toSymplectic_chainZOperator_X (c : X.C1 → ZMod 2) (q : Fin X.numQubits) :
    toSymplectic (X.chainZOperator c).operators (Fin.castAdd X.numQubits q) = 0 := by
  rcases (chainZOperator_isZType c).2 q with hI | hZ
  · rw [toSymplectic_X_part, hI]
    rfl
  · rw [toSymplectic_X_part, hZ]
    rfl

/-- An encoded X-chain has zero Z-coordinate. -/
theorem toSymplectic_chainXOperator_Z (c : X.C1 → ZMod 2) (q : Fin X.numQubits) :
    toSymplectic (X.chainXOperator c).operators (Fin.natAdd X.numQubits q) = 0 := by
  rcases (chainXOperator_isXType c).2 q with hI | hX
  · rw [toSymplectic_Z_part, hI]
    rfl
  · rw [toSymplectic_Z_part, hX]
    rfl

/-- Expand a linear map on a finite coordinate space in its standard basis. -/
private theorem linearMap_apply_eq_sum {A B : Type} [Fintype A] [DecidableEq A]
    (T : (A → ZMod 2) →ₗ[ZMod 2] (B → ZMod 2)) (c : A → ZMod 2) (b : B) :
    T c b = ∑ a, c a * T (Pi.single a 1) b := by
  have hc : c = ∑ a, c a • (Pi.single a (1 : ZMod 2)) := by
    ext a
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hc]
  simp [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- Injective boundary and cut maps make all canonical check vectors
independent. -/
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
    rw [linearMap_apply_eq_sum]
    simpa only [singleVtx] using hcol
  have hX : X.boundary2 (fun f => c (.inr f)) = 0 := by
    ext e
    have hcol := congr_fun hsum (Fin.castAdd X.numQubits (X.edgeEquiv e))
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Fintype.sum_sum_type, cellGenerator, Sum.elim_inl, Sum.elim_inr,
      vertexStabOf, faceStabOf, toSymplectic_chainZOperator_X,
      toSymplectic_chainXOperator_X, mul_zero, Finset.sum_const_zero, zero_add] at hcol
    rw [linearMap_apply_eq_sum]
    simpa only [singleFace] using hcol
  cases i with
  | inl v => exact congr_fun (hcut (hZ.trans (map_zero X.cutMap).symm)) v
  | inr f => exact congr_fun (hboundary (hX.trans (map_zero X.boundary2).symm)) f

/-- The canonical list has independent check-matrix rows when both check maps
are injective. -/
theorem rowsLinearIndependent_generatorsList
    (hcut : Function.Injective X.cutMap) (hboundary : Function.Injective X.boundary2) :
    rowsLinearIndependent X.generatorsList := by
  classical
  let e : Fin X.generatorsList.length ≃ X.C0 ⊕ X.C2 :=
    (finCongr (List.length_ofFn)).trans (Fintype.equivFin (X.C0 ⊕ X.C2)).symm
  have h := (X.linearIndependent_cellGenerator hcut hboundary).comp e e.injective
  unfold rowsLinearIndependent checkMatrix
  convert h using 1
  funext i col
  simp only [generatorsList, List.get_ofFn]
  rfl

/-- A homological CSS presentation from independent checks and their count. -/
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
      X.homologicalStabilizerGroup.toSubgroup := by
  change Subgroup.closure (listToSet X.generatorsList) =
    Subgroup.closure X.homologicalGenerators
  rw [X.listToSet_generatorsList]

end Quantum.Stabilizer.Homological.HomologicalCode
