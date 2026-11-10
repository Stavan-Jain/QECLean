import QEC.Stabilizer.Framework.FoldDouble.Basic
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode
import QEC.Stabilizer.Framework.Core.Stabilizer.Centralizer
import QEC.Stabilizer.Framework.Core.Logical.LogicalOperators
import QEC.Stabilizer.Framework.Symplectic.SymplecticSpan
import QEC.Stabilizer.Framework.Symplectic.SymplecticImage

/-!
# Phase-free images of stabilizer groups

The fold-and-double theory is a theory of phase-free Pauli operators: weights,
commutation and the nontriviality of a logical operator all depend only on the
operator part of a Pauli group element. This file provides the bridge between
the phased objects — `StabilizerGroup n`, `centralizer S`,
`IsNontrivialLogicalOperator g S` — and their phase-free shadows:

* `operatorImage H`, the subgroup of the phase-free Pauli group formed by the
  operator parts of the elements of a subgroup `H` of the Pauli group;
* membership in a centralizer, and nontriviality of a logical operator, read
  off the operator part alone (`mem_centralizer_iff_symplecticInner`,
  `isNontrivialLogicalOperator_iff_operators`);
* `exists_stabilizerGroup_operatorImage_eq`: every subgroup of the phase-free
  Pauli group on which the symplectic form vanishes is the operator image of a
  stabilizer group. The signs are chosen on an `𝔽₂`-basis of the symplectic
  image, through `negIdentity_not_mem_of_indep_phase_zero_commute`.
-/

namespace Quantum
namespace Stabilizer
namespace FoldDouble

open NQubitPauliOperator NQubitPauliGroupElement StabilizerGroup

variable {n : ℕ}

/-! ## The operator image of a subgroup -/

/-- The operator image of a subgroup of the Pauli group: the subgroup of the
phase-free Pauli group formed by the operator parts of its elements. -/
noncomputable def operatorImage (H : Subgroup (NQubitPauliGroupElement n)) :
    Subgroup (NQubitPauliOperator n) :=
  H.map operatorsHom

lemma mem_operatorImage {H : Subgroup (NQubitPauliGroupElement n)} {u : NQubitPauliOperator n} :
    u ∈ operatorImage H ↔ ∃ g ∈ H, g.operators = u :=
  Subgroup.mem_map

lemma operators_mem_operatorImage {H : Subgroup (NQubitPauliGroupElement n)}
    {g : NQubitPauliGroupElement n} (hg : g ∈ H) : g.operators ∈ operatorImage H :=
  ⟨g, hg, rfl⟩

lemma operatorImage_mono {H K : Subgroup (NQubitPauliGroupElement n)} (h : H ≤ K) :
    operatorImage H ≤ operatorImage K :=
  Subgroup.map_mono h

/-- The operator image of a stabilizer group is isotropic for the symplectic
form: its elements pairwise commute. -/
lemma symplecticInner_eq_zero_of_mem_operatorImage (S : StabilizerGroup n)
    {u v : NQubitPauliOperator n} (hu : u ∈ operatorImage S.toSubgroup)
    (hv : v ∈ operatorImage S.toSubgroup) : symplecticInner u v = 0 := by
  obtain ⟨g, hg, rfl⟩ := hu
  obtain ⟨h, hh, rfl⟩ := hv
  exact (commutes_iff_symplectic_inner_zero g h).mp (S.commutes hg hh)

/-! ## Centralizers and nontrivial logicals through the operator part -/

/-- Membership in the centralizer, read on operator parts: `g` commutes with
every stabilizer iff its operator part is symplectically orthogonal to every
stabilizer. -/
lemma mem_centralizer_iff_symplecticInner (S : StabilizerGroup n)
    (g : NQubitPauliGroupElement n) :
    g ∈ centralizer S ↔ ∀ s ∈ S.toSubgroup, symplecticInner s.operators g.operators = 0 :=
  (mem_centralizer_iff g S).trans
    (forall₂_congr fun s _ => commutes_iff_symplectic_inner_zero s g)

/-- Membership in the centralizer depends only on the operator part. -/
lemma mem_centralizer_iff_of_operators_eq (S : StabilizerGroup n)
    {g g' : NQubitPauliGroupElement n} (h : g.operators = g'.operators) :
    g ∈ centralizer S ↔ g' ∈ centralizer S := by
  rw [mem_centralizer_iff_symplecticInner, mem_centralizer_iff_symplecticInner, h]

/-- The phase-zero lift of `u` is in the centralizer iff `u` is orthogonal to
every stabilizer. -/
lemma ofOperator_mem_centralizer_iff (S : StabilizerGroup n) (u : NQubitPauliOperator n) :
    ofOperator u ∈ centralizer S ↔ ∀ s ∈ S.toSubgroup, symplecticInner s.operators u = 0 :=
  mem_centralizer_iff_symplecticInner S (ofOperator u)

/-- The operator image of the centralizer: the operators orthogonal to every
stabilizer. -/
lemma mem_operatorImage_centralizer_iff (S : StabilizerGroup n) (u : NQubitPauliOperator n) :
    u ∈ operatorImage (centralizer S) ↔
      ∀ s ∈ S.toSubgroup, symplecticInner s.operators u = 0 := by
  refine ⟨?_, fun h => ⟨ofOperator u, (ofOperator_mem_centralizer_iff S u).mpr h, rfl⟩⟩
  rintro ⟨g, hg, rfl⟩
  exact (mem_centralizer_iff_symplecticInner S g).mp hg

/-- An element is in the centralizer iff its operator part is in the operator
image of the centralizer. -/
lemma mem_centralizer_iff_operators_mem (S : StabilizerGroup n) (g : NQubitPauliGroupElement n) :
    g ∈ centralizer S ↔ g.operators ∈ operatorImage (centralizer S) := by
  rw [mem_operatorImage_centralizer_iff, mem_centralizer_iff_symplecticInner]

/-- The operator image of the stabilizer group sits inside that of its
centralizer. -/
lemma operatorImage_le_operatorImage_centralizer (S : StabilizerGroup n) :
    operatorImage S.toSubgroup ≤ operatorImage (centralizer S) :=
  operatorImage_mono (stabilizer_le_centralizer S)

/-- A nontrivial logical operator, read on operator parts: an element of the
centralizer whose operator part is not that of a stabilizer. -/
lemma isNontrivialLogicalOperator_iff_operators (S : StabilizerGroup n)
    (g : NQubitPauliGroupElement n) :
    IsNontrivialLogicalOperator g S ↔
      g ∈ centralizer S ∧ g.operators ∉ operatorImage S.toSubgroup := by
  rw [IsNontrivialLogicalOperator_iff, mem_operatorImage]
  simp only [not_exists, not_and, ne_eq]

/-- Nontriviality of a logical operator depends only on the operator part. -/
lemma isNontrivialLogicalOperator_iff_of_operators_eq (S : StabilizerGroup n)
    {g g' : NQubitPauliGroupElement n} (h : g.operators = g'.operators) :
    IsNontrivialLogicalOperator g S ↔ IsNontrivialLogicalOperator g' S := by
  rw [isNontrivialLogicalOperator_iff_operators, isNontrivialLogicalOperator_iff_operators,
    mem_centralizer_iff_of_operators_eq S h, h]

/-- The phase-zero lift of `u` is a nontrivial logical operator iff `u` lies in
the operator image of the centralizer but not in that of the stabilizer. -/
lemma isNontrivialLogicalOperator_ofOperator_iff (S : StabilizerGroup n)
    (u : NQubitPauliOperator n) :
    IsNontrivialLogicalOperator (ofOperator u) S ↔
      u ∈ operatorImage (centralizer S) ∧ u ∉ operatorImage S.toSubgroup := by
  rw [isNontrivialLogicalOperator_iff_operators, mem_centralizer_iff_operators_mem,
    ofOperator_operators]

/-! ## Choosing signs

A subgroup `J` of the phase-free Pauli group whose elements pairwise commute is
the operator image of a stabilizer group. Pick an `𝔽₂`-basis of the symplectic
image of `J`, lift its vectors to phase-zero Pauli group elements, and generate:
the generators commute, have phase zero and linearly independent check-matrix
rows, so their closure avoids `−I`
(`negIdentity_not_mem_of_indep_phase_zero_commute`), and its operator image is
all of `J` because the basis spans the symplectic image of `J`. -/

/-- A subgroup of the phase-free Pauli group on which the symplectic form
vanishes is the operator image of a stabilizer group: there is a choice of
signs making it an abelian subgroup of the Pauli group not containing `−I`. -/
theorem exists_stabilizerGroup_operatorImage_eq (J : Subgroup (NQubitPauliOperator n))
    (hJ : ∀ u ∈ J, ∀ v ∈ J, symplecticInner u v = 0) :
    ∃ F : StabilizerGroup n, operatorImage F.toSubgroup = J := by
  classical
  -- an `𝔽₂`-basis `B` of the symplectic image of `J`
  obtain ⟨B, hBJ, hspan, hli⟩ :=
    exists_linearIndependent (ZMod 2) (toSymplectic '' (J : Set (NQubitPauliOperator n)))
  have hJ_of : ∀ u, toSymplectic u ∈ B → u ∈ J := fun u hu => by
    obtain ⟨u', hu', h⟩ := hBJ hu
    exact toSymplectic_injective h ▸ hu'
  -- the generator list: the phase-zero lifts of the operators with symplectic vector in `B`
  have hfin : (toSymplectic ⁻¹' B : Set (NQubitPauliOperator n)).Finite :=
    B.toFinite.preimage toSymplectic_injective.injOn
  set L : List (NQubitPauliGroupElement n) := hfin.toFinset.toList.map ofOperator with hL
  have hmemL : ∀ g, g ∈ L ↔ ∃ u, toSymplectic u ∈ B ∧ ofOperator u = g := fun g => by
    simp only [hL, List.mem_map, Finset.mem_toList, Set.Finite.mem_toFinset, Set.mem_preimage]
  have hL_of : ∀ g ∈ L, g = ofOperator g.operators ∧ toSymplectic g.operators ∈ B := by
    intro g hg
    obtain ⟨u, hu, rfl⟩ := (hmemL g).mp hg
    exact ⟨rfl, hu⟩
  have hL_phase : AllPhaseZero L := fun g hg => congrArg phasePower (hL_of g hg).1
  have hL_mem : ∀ g ∈ listToSet L, g.operators ∈ J := fun g hg => hJ_of _ (hL_of g hg).2
  have hL_comm : ∀ g ∈ listToSet L, ∀ h ∈ listToSet L, g * h = h * g := fun g hg h hh =>
    (commutes_iff_symplectic_inner_zero g h).mpr (hJ _ (hL_mem g hg) _ (hL_mem h hh))
  -- the check-matrix rows of `L` are the vectors of `B`, without repetition
  have hL_indep : rowsLinearIndependent L := by
    refine hli.comp (fun i => ⟨checkMatrix L i, (hL_of _ (L.get_mem i)).2⟩) fun i j hij => ?_
    have h : (L.get i).operators = (L.get j).operators :=
      toSymplectic_injective (congrArg Subtype.val hij)
    refine List.nodup_iff_injective_get.mp
      ((Finset.nodup_toList _).map ofOperator_injective) ?_
    rw [(hL_of _ (L.get_mem i)).1, (hL_of _ (L.get_mem j)).1, h]
  have hset : (fun g : NQubitPauliGroupElement n => toSymplectic g.operators) '' listToSet L =
      B := by
    refine Set.Subset.antisymm ?_ fun v hv => ?_
    · rintro _ ⟨g, hg, rfl⟩
      exact (hL_of g hg).2
    · obtain ⟨u, -, rfl⟩ := hBJ hv
      exact ⟨ofOperator u, (hmemL _).mpr ⟨u, hv, rfl⟩, rfl⟩
  refine ⟨mkStabilizerFromGenerators n L hL_comm
    (negIdentity_not_mem_of_indep_phase_zero_commute L hL_phase hL_indep hL_comm),
    le_antisymm ?_ fun u hu => ?_⟩
  · exact Subgroup.map_le_iff_le_comap.mpr ((Subgroup.closure_le _).mpr hL_mem)
  · refine mem_operatorImage.mpr (exists_mem_closure_of_symp_in_span L u ?_)
    rw [sympSpan_eq_span_listToSet, hset, hspan]
    exact Submodule.subset_span ⟨u, hu, rfl⟩

end FoldDouble
end Stabilizer
end Quantum
