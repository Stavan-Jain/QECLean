import QEC.Stabilizer.Framework.Homological.Presentation
import QEC.Stabilizer.Framework.Homological.LogicalCorrespondence

namespace Quantum.Stabilizer.Homological.HomologicalCode
open scoped BigOperators

/--
Extend a list of selected check coefficients by taking their point-mass sum.
-/
def checkExtension {ι κ : Type} [Fintype ι] [DecidableEq κ] (e : ι → κ) :
    (ι → ZMod 2) →ₗ[ZMod 2] (κ → ZMod 2) where
  toFun c := ∑ i, c i • Pi.single (e i) 1
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum, smul_smul]

/--
Extending a point mass through an injective selection gives its original point
mass.
-/
theorem checkExtension_single {ι κ : Type} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (e : ι → κ) (i : ι) : checkExtension e (Pi.single i 1) = Pi.single (e i) 1 := by
  simp [checkExtension, Pi.single_apply]

/--
Retain a selection of vertex and face checks, keeping the physical qubits
unchanged.
-/
noncomputable def trimChecks (X : HomologicalCode)
    {V F : Type} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
    (v : V → X.C0) (f : F → X.C2) : HomologicalCode where
  C0 := V
  C1 := X.C1
  C2 := F
  decEq0 := inferInstance
  decEq1 := inferInstance
  decEq2 := inferInstance
  fin0 := inferInstance
  fin1 := inferInstance
  fin2 := inferInstance
  boundary1 := (LinearMap.funLeft (ZMod 2) (ZMod 2) v).comp X.boundary1
  boundary2 := X.boundary2.comp (checkExtension f)
  boundary_comp := by
    apply LinearMap.ext
    intro c
    funext q
    change X.boundary1 (X.boundary2 (checkExtension f c)) (v q) = 0
    rw [X.boundary_comp_apply]
    rfl
  numQubits := X.numQubits
  numQubits_eq := X.numQubits_eq
  edgeEquiv := X.edgeEquiv

variable (X : HomologicalCode)
variable {V F : Type} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
variable (v : V → X.C0) (f : F → X.C2)

/-- The selected face boundary is its original boundary. -/
theorem trimChecks_boundary2_single (i : F) :
    (X.trimChecks v f).boundary2 (Pi.single i 1) = X.boundary2 (Pi.single (f i) 1) := by
  change X.boundary2 (checkExtension f (Pi.single i 1)) = _
  rw [checkExtension_single]

/--
The cut map of the trimmed complex extends coefficients through the selected
vertices.
-/
theorem trimChecks_cutMap (s : V → ZMod 2) :
    (X.trimChecks v f).cutMap s = X.cutMap (checkExtension v s) := by
  ext q
  change (∑ i : V, s i * X.boundary1 (Pi.single q 1) (v i)) = _
  simp only [checkExtension, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [X.cutMap_apply]
  simp [Pi.single_apply]

/-- The selected vertex cut is its original cut. -/
theorem trimChecks_cutMap_single (i : V) :
    (X.trimChecks v f).cutMap (Pi.single i 1) = X.cutMap (Pi.single (v i) 1) := by
  rw [trimChecks_cutMap]
  exact congrArg X.cutMap (checkExtension_single v i)

/--
Trimming checks preserves boundaries when every original face boundary is
generated.
-/
theorem trimChecks_boundaries_eq
    (h : ∀ i : X.C2, X.boundary2 (Pi.single i 1) ∈ (X.trimChecks v f).boundaries) :
    (X.trimChecks v f).boundaries = X.boundaries := by
  apply le_antisymm
  · rintro c ⟨s, rfl⟩
    exact ⟨checkExtension f s, rfl⟩
  · rintro c ⟨s, rfl⟩
    have hs : s = ∑ i, s i • (Pi.single i (1 : ZMod 2)) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hs, map_sum]
    apply Submodule.sum_mem
    intro i hi
    rw [map_smul]
    exact Submodule.smul_mem _ _ (h i)

/--
Trimming vertex checks preserves cycles when every original cut is generated.
-/
theorem trimChecks_cycles_eq
    (h : ∀ i : X.C0, X.cutMap (Pi.single i 1) ∈
      LinearMap.range (X.trimChecks v f).cutMap) :
    (X.trimChecks v f).cycles = X.cycles := by
  ext c
  constructor
  · intro hc
    change X.boundary1 c = 0
    ext i
    obtain ⟨s, hs⟩ := h i
    have hp := (X.trimChecks v f).boundary1_cutMap_transpose c s
    have hz : (X.trimChecks v f).boundary1 c = 0 := hc
    rw [hz, hs] at hp
    have hx := X.boundary1_cutMap_transpose c (Pi.single i 1)
    simp at hp hx
    simpa [Pi.single_apply] using hx.trans hp.symm
  · intro hc
    change (fun i => X.boundary1 c (v i)) = 0
    change X.boundary1 c = 0 at hc
    rw [hc]
    rfl

/--
Retaining spanning vertex and face checks preserves the stabilizer subgroup.
-/
theorem trimChecks_stabilizer_eq
    (hV : ∀ i : X.C0, X.cutMap (Pi.single i 1) ∈
      LinearMap.range (X.trimChecks v f).cutMap)
    (hF : ∀ i : X.C2, X.boundary2 (Pi.single i 1) ∈
      (X.trimChecks v f).boundaries) :
    (X.trimChecks v f).homologicalStabilizerGroup.toSubgroup =
      X.homologicalStabilizerGroup.toSubgroup := by
  change Subgroup.closure (X.trimChecks v f).homologicalGenerators =
    Subgroup.closure X.homologicalGenerators
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro g (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · change (X.trimChecks v f).chainZOperator
        ((X.trimChecks v f).cutMap (Pi.single i 1)) ∈ _
      rw [trimChecks_cutMap_single]
      exact Subgroup.subset_closure (Or.inl ⟨v i, rfl⟩)
    · change (X.trimChecks v f).chainXOperator
        ((X.trimChecks v f).boundary2 (Pi.single i 1)) ∈ _
      rw [trimChecks_boundary2_single]
      exact Subgroup.subset_closure (Or.inr ⟨f i, rfl⟩)
  · apply (Subgroup.closure_le _).mpr
    rintro g (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · have h := ((X.trimChecks v f).chainZOperator_mem_ZClosure_iff_mem_dualBoundaries
        (X.cutMap (Pi.single i 1))).mpr (hV i)
      exact Subgroup.closure_mono (X.trimChecks v f).ZGenerators_subset_homologicalGenerators h
    · have h := ((X.trimChecks v f).chainXOperator_mem_XClosure_iff_mem_boundaries
        (X.boundary2 (Pi.single i 1))).mpr (hF i)
      exact Subgroup.closure_mono (X.trimChecks v f).XGenerators_subset_homologicalGenerators h

end Quantum.Stabilizer.Homological.HomologicalCode
