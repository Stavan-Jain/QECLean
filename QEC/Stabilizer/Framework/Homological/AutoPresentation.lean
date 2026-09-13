import QEC.Stabilizer.Framework.Homological.StabilizerCode
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Automatic independent presentations of homological CSS codes

Choose bases of the boundary and coboundary spaces. Their pure X- and Z-chain
operators form an independent CSS generator list. Rank-nullity identifies the
number of encoded qubits with the dimension of first homology.
-/

namespace Quantum.Stabilizer.Homological.HomologicalCode

open NQubitPauliGroupElement NQubitPauliOperator
open scoped BigOperators Matrix

variable (X : HomologicalCode)

/-- Read a symplectic vector into its two physical chain coordinates. -/
def readSymplectic : (Fin (X.numQubits + X.numQubits) → ZMod 2) →ₗ[ZMod 2]
    ((X.C1 → ZMod 2) × (X.C1 → ZMod 2)) where
  toFun v := (fun e => v (Fin.castAdd X.numQubits (X.edgeEquiv e)),
    fun e => v (Fin.natAdd X.numQubits (X.edgeEquiv e)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The symplectic coordinates of a pure X-chain are `(c, 0)`. -/
theorem readSymplectic_chainXOperator (c : X.C1 → ZMod 2) :
    X.readSymplectic (toSymplectic (X.chainXOperator c).operators) = (c, 0) := by
  apply Prod.ext
  · funext e
    change toSymplectic _ (Fin.castAdd _ (X.edgeEquiv e)) = c e
    rw [toSymplectic_X_part, chainXOperator_op_at]
    simp only [Equiv.apply_eq_iff_eq, exists_eq_left]
    by_cases hc : c e = 1
    · simp only [hc, if_true, PauliOperator.toSymplecticSingle_X]
    · have hz : c e = 0 := (by decide : ∀ a : ZMod 2, a ≠ 1 → a = 0) _ hc
      simp [hz]
  · funext e
    change toSymplectic _ (Fin.natAdd _ (X.edgeEquiv e)) = 0
    rw [toSymplectic_Z_part, chainXOperator_op_at]
    split_ifs <;> rfl

/-- The symplectic coordinates of a pure Z-chain are `(0, c)`. -/
theorem readSymplectic_chainZOperator (c : X.C1 → ZMod 2) :
    X.readSymplectic (toSymplectic (X.chainZOperator c).operators) = (0, c) := by
  apply Prod.ext
  · funext e
    change toSymplectic _ (Fin.castAdd _ (X.edgeEquiv e)) = 0
    rw [toSymplectic_X_part, chainZOperator_op_at]
    split_ifs <;> rfl
  · funext e
    change toSymplectic _ (Fin.natAdd _ (X.edgeEquiv e)) = c e
    rw [toSymplectic_Z_part, chainZOperator_op_at]
    simp only [Equiv.apply_eq_iff_eq, exists_eq_left]
    by_cases hc : c e = 1
    · simp only [hc, if_true, PauliOperator.toSymplecticSingle_Z]
    · have hz : c e = 0 := (by decide : ∀ a : ZMod 2, a ≠ 1 → a = 0) _ hc
      simp [hz]

/-- Independent X- and Z-chain families give independent CSS check rows. -/
theorem rowsLinearIndependent_chainGeneratorsList {a b : ℕ}
    (x : Fin a → X.C1 → ZMod 2) (z : Fin b → X.C1 → ZMod 2)
    (hx : LinearIndependent (ZMod 2) x) (hz : LinearIndependent (ZMod 2) z) :
    rowsLinearIndependent (X.chainGeneratorsList (List.ofFn x) (List.ofFn z)) := by
  classical
  rw [chainGeneratorsList, List.map_ofFn, List.map_ofFn, ← List.ofFn_fin_append]
  have hi : LinearIndependent (ZMod 2) (fun i : Fin (a + b) =>
      toSymplectic ((Fin.append (X.chainXOperator ∘ x) (X.chainZOperator ∘ z)) i).operators) := by
    apply LinearIndependent.of_comp X.readSymplectic
    apply (linearIndependent_equiv finSumFinEquiv).mp
    convert linearIndependent_inl_union_inr' hx hz using 1
    funext i
    rcases i with i | i
    · simp [Function.comp_def, finSumFinEquiv_apply_left,
        readSymplectic_chainXOperator]
    · simp [Function.comp_def, finSumFinEquiv_apply_right,
        readSymplectic_chainZOperator]
  unfold rowsLinearIndependent checkMatrix
  convert hi.comp (Fin.cast (List.length_ofFn)) (Fin.cast_injective _) using 1
  funext i j
  simp only [Function.comp_apply, List.get_eq_getElem, List.getElem_ofFn]
  rfl

/-- The cut map's matrix is the transpose of the first boundary matrix. -/
theorem toMatrix_cutMap :
    LinearMap.toMatrix' X.cutMap = (LinearMap.toMatrix' X.boundary1)ᵀ := by
  classical
  ext e v
  simp [LinearMap.toMatrix'_apply, cutMap_apply, Pi.single_apply]

/-- Boundary and coboundary ranks satisfy the expected transpose identity. -/
theorem finrank_dualBoundaries :
    Module.finrank (ZMod 2) X.dualBoundaries =
      Module.finrank (ZMod 2) (LinearMap.range X.boundary1) := by
  classical
  have h := Matrix.rank_transpose (LinearMap.toMatrix' X.boundary1)
  rw [← X.toMatrix_cutMap] at h
  have heq (f : (X.C0 → ZMod 2) →ₗ[ZMod 2] (X.C1 → ZMod 2)) :
      (LinearMap.toMatrix' f).rank = Module.finrank (ZMod 2) (LinearMap.range f) :=
    (LinearEquiv.ofEq _ _ (congrArg LinearMap.range (Matrix.toLin'_toMatrix' f))).finrank_eq
  have heq' (f : (X.C1 → ZMod 2) →ₗ[ZMod 2] (X.C0 → ZMod 2)) :
      (LinearMap.toMatrix' f).rank = Module.finrank (ZMod 2) (LinearMap.range f) :=
    (LinearEquiv.ofEq _ _ (congrArg LinearMap.range (Matrix.toLin'_toMatrix' f))).finrank_eq
  exact (heq X.cutMap).symm.trans (h.trans (heq' X.boundary1))

/-- Homology and the two stabilizer ranks partition the physical dimension. -/
theorem finrank_H1_add_stabilizer_ranks :
    Module.finrank (ZMod 2) X.H1 + Module.finrank (ZMod 2) X.boundaries +
      Module.finrank (ZMod 2) X.dualBoundaries = X.numQubits := by
  have hb := Submodule.finrank_mono X.boundaries_le_cycles
  have hh := X.finrank_H1_eq_cycles_sub_boundaries
  have hr := X.rank_nullity_boundary1
  rw [X.finrank_C1, X.numQubits_eq] at hr
  rw [X.finrank_dualBoundaries]
  omega

/-- The homological dimension cannot exceed the physical-qubit count. -/
theorem finrank_H1_le_numQubits : Module.finrank (ZMod 2) X.H1 ≤ X.numQubits := by
  have h := X.finrank_H1_add_stabilizer_ranks
  omega

/-- The ambient chain list underlying a chosen basis of a chain subspace. -/
noncomputable def basisChains (P : Submodule (ZMod 2) (X.C1 → ZMod 2)) :
    List (X.C1 → ZMod 2) :=
  List.ofFn (fun i => ((Module.finBasis (ZMod 2) P) i : X.C1 → ZMod 2))

/-- The selected ambient basis chains span their original subspace. -/
theorem span_basisChains (P : Submodule (ZMod 2) (X.C1 → ZMod 2)) :
    Submodule.span (ZMod 2) {c | c ∈ X.basisChains P} = P := by
  classical
  have hs : {c | c ∈ X.basisChains P} =
      Set.range (fun i => ((Module.finBasis (ZMod 2) P) i : X.C1 → ZMod 2)) := by
    ext c
    simp only [basisChains, List.mem_ofFn, Set.mem_setOf_eq, Set.mem_range]
  rw [hs]
  change Submodule.span (ZMod 2) (Set.range (P.subtype ∘ Module.finBasis (ZMod 2) P)) = P
  rw [Set.range_comp, ← Submodule.map_span, (Module.finBasis (ZMod 2) P).span_eq,
    Submodule.map_top, Submodule.range_subtype]

/-- Every homological CSS code has an independent generator presentation with
exactly its first-homology dimension as the number of logical qubits. -/
noncomputable def automaticPresentation :
    X.CSSGeneratorPresentation (Module.finrank (ZMod 2) X.H1) where
  xChains := X.basisChains X.boundaries
  zChains := X.basisChains X.dualBoundaries
  x_span := X.span_basisChains X.boundaries
  z_span := X.span_basisChains X.dualBoundaries
  independent := X.rowsLinearIndependent_chainGeneratorsList _ _
    ((Module.finBasis (ZMod 2) X.boundaries).linearIndependent.map'
      X.boundaries.subtype X.boundaries.ker_subtype)
    ((Module.finBasis (ZMod 2) X.dualBoundaries).linearIndependent.map'
      X.dualBoundaries.subtype X.dualBoundaries.ker_subtype)
  hk := X.finrank_H1_le_numQubits
  length_eq := by
    simp only [basisChains, List.length_ofFn]
    have h := X.finrank_H1_add_stabilizer_ranks
    omega

/-- The canonical homological CSS code packaged with its homology dimension. -/
noncomputable def toStabilizerCode :
    Quantum.StabilizerGroup.StabilizerCode X.numQubits (Module.finrank (ZMod 2) X.H1) :=
  X.automaticPresentation.toStabilizerCode

/-- Automatic basis selection preserves the canonical stabilizer subgroup. -/
theorem toStabilizerCode_toSubgroup_eq :
    X.toStabilizerCode.toStabilizerGroup.toSubgroup =
      X.homologicalStabilizerGroup.toSubgroup :=
  X.automaticPresentation.toStabilizerCode_toSubgroup_eq

end Quantum.Stabilizer.Homological.HomologicalCode
