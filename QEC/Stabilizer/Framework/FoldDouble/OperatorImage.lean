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
the library's phased objects — `StabilizerGroup n`, `centralizer S`,
`IsNontrivialLogicalOperator g S` — and their phase-free shadows:

* `operatorImage H`, the subgroup of the phase-free Pauli group formed by the
  operator parts of the elements of a subgroup `H` of the Pauli group;
* membership in a centralizer, and nontriviality of a logical operator, read
  off the operator part alone (`mem_centralizer_iff_symplecticInner`,
  `isNontrivialLogicalOperator_iff_operators`);
* **Lemma 1.8**: every subgroup of the phase-free Pauli group on which the
  symplectic form vanishes is the operator image of a genuine stabilizer group
  (`exists_stabilizerGroup_operatorImage_eq`). The signs are chosen on an
  `𝔽₂`-basis of the symplectic image, through the library's
  `negIdentity_not_mem_of_indep_phase_zero_commute`.
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
    u ∈ operatorImage H ↔ ∃ g ∈ H, g.operators = u := by
  simp only [operatorImage, Subgroup.mem_map, operatorsHom_apply]

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
  obtain ⟨g, hg, rfl⟩ := mem_operatorImage.mp hu
  obtain ⟨h, hh, rfl⟩ := mem_operatorImage.mp hv
  exact (commutes_iff_symplectic_inner_zero g h).mp (S.commutes hg hh)

/-! ## Centralizers and nontrivial logicals through the operator part -/

/-- Membership in the centralizer, read on operator parts: `g` commutes with
every stabilizer iff its operator part is symplectically orthogonal to every
stabilizer. -/
lemma mem_centralizer_iff_symplecticInner (S : StabilizerGroup n)
    (g : NQubitPauliGroupElement n) :
    g ∈ centralizer S ↔ ∀ s ∈ S.toSubgroup, symplecticInner s.operators g.operators = 0 := by
  rw [mem_centralizer_iff]
  exact forall₂_congr fun s _ => commutes_iff_symplectic_inner_zero s g

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
  rw [mem_operatorImage]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (mem_centralizer_iff_symplecticInner S g).mp hg
  · intro h
    exact ⟨ofOperator u, (ofOperator_mem_centralizer_iff S u).mpr h, rfl⟩

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

/-! ## Lemma 1.8: choosing signs

A subgroup `J` of the phase-free Pauli group whose elements pairwise commute is
the operator image of a stabilizer group. Pick an `𝔽₂`-basis of the symplectic
image of `J`, lift its vectors to phase-zero Pauli group elements, and generate:
the generators commute, have phase zero and linearly independent check-matrix
rows, so their closure avoids `−I`
(`negIdentity_not_mem_of_indep_phase_zero_commute`), and its operator image is
all of `J` because the basis spans the symplectic image of `J`. -/

/-- The symplectic image of a subgroup of the phase-free Pauli group is already
closed under spans: a vector in the span is the symplectic vector of an element
of the subgroup. -/
lemma exists_mem_of_toSymplectic_mem_span (J : Subgroup (NQubitPauliOperator n))
    {v : Fin (n + n) → ZMod 2}
    (hv : v ∈ Submodule.span (ZMod 2) (toSymplectic '' (J : Set (NQubitPauliOperator n)))) :
    ∃ u ∈ J, toSymplectic u = v := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    exact ⟨u, hu, rfl⟩
  | zero => exact ⟨1, J.one_mem, toSymplectic_one_operators⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hy
    exact ⟨u * w, J.mul_mem hu hw, funext (toSymplectic_add u w)⟩
  | smul a x _ hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) a with rfl | rfl
    · exact ⟨1, J.one_mem, by rw [zero_smul]; exact toSymplectic_one_operators⟩
    · exact ⟨u, hu, (one_smul _ _).symm⟩

/-- `ofOperator` is injective. -/
lemma ofOperator_injective : Function.Injective (ofOperator : NQubitPauliOperator n → _) :=
  fun _ _ h => congrArg operators h

/-- **Lemma 1.8.** A subgroup of the phase-free Pauli group on which the
symplectic form vanishes is the operator image of a stabilizer group: there is
a choice of signs making it a genuine abelian subgroup of the Pauli group not
containing `−I`. -/
theorem exists_stabilizerGroup_operatorImage_eq (J : Subgroup (NQubitPauliOperator n))
    (hJ : ∀ u ∈ J, ∀ v ∈ J, symplecticInner u v = 0) :
    ∃ F : StabilizerGroup n, operatorImage F.toSubgroup = J := by
  classical
  -- an `𝔽₂`-basis `B` of the symplectic image of `J`
  obtain ⟨B, hBV, hspan, hli⟩ :=
    exists_linearIndependent (ZMod 2) (toSymplectic '' (J : Set (NQubitPauliOperator n)))
  -- the operators whose symplectic vectors lie in `B`
  set B' : Set (NQubitPauliOperator n) := toSymplectic ⁻¹' B with hB'
  have hB'J : B' ⊆ (J : Set (NQubitPauliOperator n)) := by
    intro u hu
    obtain ⟨u', hu'J, hu'⟩ := hBV hu
    rwa [toSymplectic_injective hu'] at hu'J
  have himg : toSymplectic '' B' = B :=
    Set.image_preimage_eq_of_subset (hBV.trans (Set.image_subset_range _ _))
  have hBfin : B.Finite := (Set.toFinite _).subset hBV
  have hB'fin : B'.Finite := hBfin.preimage toSymplectic_injective.injOn
  -- the generator list: phase-zero lifts of `B'`
  set L : List (NQubitPauliGroupElement n) := hB'fin.toFinset.toList.map ofOperator with hL
  have hmemL : ∀ g, g ∈ L ↔ ∃ u ∈ B', ofOperator u = g := by
    intro g
    rw [hL, List.mem_map]
    simp only [Finset.mem_toList, Set.Finite.mem_toFinset]
  have hL_phase : AllPhaseZero L := by
    intro g hg
    obtain ⟨u, _, rfl⟩ := (hmemL g).mp hg
    rfl
  have hL_mem : ∀ g ∈ listToSet L, g.operators ∈ J := by
    intro g hg
    obtain ⟨u, hu, rfl⟩ := (hmemL g).mp hg
    exact hB'J hu
  have hL_comm : ∀ g ∈ listToSet L, ∀ h ∈ listToSet L, g * h = h * g := by
    intro g hg h hh
    rw [commutes_iff_symplectic_inner_zero]
    exact hJ _ (hL_mem g hg) _ (hL_mem h hh)
  have hL_nodup : L.Nodup := (Finset.nodup_toList _).map ofOperator_injective
  -- the check-matrix rows of `L` are exactly `B`
  have hset : (fun g : NQubitPauliGroupElement n => toSymplectic g.operators) '' listToSet L
      = B := by
    rw [← himg]
    ext v
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨u, hu, rfl⟩ := (hmemL g).mp hg
      exact ⟨u, hu, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨ofOperator u, (hmemL _).mpr ⟨u, hu, rfl⟩, rfl⟩
  have hrow : ∀ i : Fin L.length, checkMatrix L i = toSymplectic (L.get i).operators :=
    fun i => rfl
  have hrow_mem : ∀ i : Fin L.length, checkMatrix L i ∈ B := by
    intro i
    rw [← hset, hrow]
    exact ⟨L.get i, List.get_mem L i, rfl⟩
  have hL_indep : rowsLinearIndependent L := by
    let f : Fin L.length → B := fun i => ⟨checkMatrix L i, hrow_mem i⟩
    have hf : Function.Injective f := by
      intro i j hij
      have h1 : toSymplectic (L.get i).operators = toSymplectic (L.get j).operators :=
        congrArg Subtype.val hij
      have h2 : (L.get i).operators = (L.get j).operators := toSymplectic_injective h1
      have h3 : L.get i = L.get j :=
        NQubitPauliGroupElement.ext _ _
          ((hL_phase _ (List.get_mem L i)).trans (hL_phase _ (List.get_mem L j)).symm) h2
      exact (List.nodup_iff_injective_get.mp hL_nodup) h3
    exact hli.comp f hf
  have hN := negIdentity_not_mem_of_indep_phase_zero_commute L hL_phase hL_indep hL_comm
  have hspanL : sympSpan L =
      Submodule.span (ZMod 2) (toSymplectic '' (J : Set (NQubitPauliOperator n))) := by
    rw [sympSpan_eq_span_listToSet, hset, hspan]
  refine ⟨mkStabilizerFromGenerators n L hL_comm hN, ?_⟩
  ext u
  rw [mem_operatorImage]
  constructor
  · rintro ⟨g, hg, rfl⟩
    have h1 := mem_closure_implies_symp_in_span L g hg
    rw [hspanL] at h1
    obtain ⟨u, hu, huv⟩ := exists_mem_of_toSymplectic_mem_span J h1
    rwa [toSymplectic_injective huv] at hu
  · intro hu
    have h1 : toSymplectic u ∈ sympSpan L := by
      rw [hspanL]
      exact Submodule.subset_span ⟨u, hu, rfl⟩
    exact exists_mem_closure_of_symp_in_span L u h1

end FoldDouble
end Stabilizer
end Quantum
