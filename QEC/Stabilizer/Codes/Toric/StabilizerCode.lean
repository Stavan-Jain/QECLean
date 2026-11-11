import QEC.Stabilizer.Codes.Toric.DistanceZ
import QEC.Stabilizer.Framework.Homological.ToCode
import QEC.Stabilizer.Framework.Symplectic.Presentation

/-!
# The toric code as a `[[2 * L * L, 2]]` stabilizer code

The `2 * L * L` checks of the toric code are not independent: the product of
all vertex checks is the identity, and so is the product of all face checks.
Dropping the vertex check and the face check at the site `(0, 0)` leaves an
independent list of checks, which presents the code.

* `generatorsListPackaged L` is the trimmed list of `2 * L * L - 2` checks.
* `vertexStab_zero_mul_prod_generatorsListZTrimmed` and
  `faceStab_zero_mul_prod_generatorsListXTrimmed`: each dropped check is the
  inverse of the product of the kept checks of its type. Hence the trimmed list
  generates the whole stabilizer group (`closure_packaged_eq_full`).
* `rowsLinearIndependent_generatorsListPackaged`: the trimmed checks are
  independent. They generate a group whose symplectic image has dimension
  `2 * L * L - dim H₁ = 2 * L * L - 2`, the length of the list
  (`rowsLinearIndependent_of_length_eq_finrank_sympImage`).
* `toricPresentation L` is the resulting presentation, and
  `toricStabilizerCode L` the `[[2 * L * L, 2]]` code it presents. Its
  stabilizer group is `stabilizerGroup L` (`toricStabilizerCode_subgroup_eq`),
  so it is also the stabilizer group of the code
  `(toricHomologicalCode L).toStabilizerCode` that the general theory builds
  from the chain complex (`toricHomologicalCode_toStabilizerCode_subgroup_eq`).
* `logicalOps L` are the logical operators of the two logical qubits: the
  horizontal X-loop with the Z-operator of the dual loop crossing it, and the
  vertical X-loop with the Z-operator of the dual loop crossing it. A loop and
  a dual loop anticommute exactly when they cross in one edge
  (`loopXOperator_commutes_dualLoopZOperator_iff`).
  `toricStabilizerCodeWithLogicals L` bundles the code with these operators.
-/

namespace Quantum

/-! ## A rank criterion for independent rows -/

/-- A list of Pauli group elements that generates a stabilizer group whose
symplectic image has dimension the length of the list has linearly independent
check-matrix rows: the rows span a space of that dimension. -/
theorem NQubitPauliGroupElement.rowsLinearIndependent_of_length_eq_finrank_sympImage {n : ℕ}
    (S : StabilizerGroup n) (l : List (NQubitPauliGroupElement n))
    (hS : S.toSubgroup = Subgroup.closure (listToSet l))
    (hl : l.length = Module.finrank (ZMod 2) S.sympImage) : rowsLinearIndependent l := by
  rw [StabilizerGroup.sympImage_eq_span_of_toSubgroup_eq_closure S _ hS,
    ← sympSpan_eq_span_listToSet] at hl
  exact linearIndependent_iff_card_eq_finrank_span.2 ((Fintype.card_fin _).trans hl)

namespace StabilizerGroup
namespace ToricCodeN

open NQubitPauliGroupElement Stabilizer.Lattice Stabilizer.Homological
open scoped ToricChain

/-! ## The trimmed list of checks -/

section Trimmed

variable (L : ℕ) [Fact (0 < L)]

/-- The sites other than `(0, 0)`: the list `coords L` with `(0, 0)` erased. -/
def coordsTrimmed : List (Fin L × Fin L) :=
  (coords L).erase (zeroCoord L, zeroCoord L)

/-- The vertex checks at the sites other than `(0, 0)`. -/
def generatorsListZTrimmed : List (NQubitPauliGroupElement (numQubits L)) :=
  (coordsTrimmed L).map fun p => vertexStab L p.1 p.2

/-- The face checks at the sites other than `(0, 0)`. -/
def generatorsListXTrimmed : List (NQubitPauliGroupElement (numQubits L)) :=
  (coordsTrimmed L).map fun p => faceStab L p.1 p.2

/-- The trimmed list of checks: all vertex checks and all face checks except
the two at `(0, 0)`. -/
def generatorsListPackaged : List (NQubitPauliGroupElement (numQubits L)) :=
  generatorsListZTrimmed L ++ generatorsListXTrimmed L

omit [Fact (0 < L)] in
private lemma nodup_coords : (coords L).Nodup :=
  (List.nodup_finRange L).product (List.nodup_finRange L)

omit [Fact (0 < L)] in
private lemma mem_coords (p : Fin L × Fin L) : p ∈ coords L :=
  GeneratorListLemmas.mem_finRange_product L p

/-- `coords L` is `(0, 0)` followed by `coordsTrimmed L`, up to order. -/
private lemma coords_perm :
    (coords L).Perm ((zeroCoord L, zeroCoord L) :: coordsTrimmed L) :=
  List.perm_cons_erase (mem_coords L _)

/-- `coordsTrimmed L` contains every site except `(0, 0)`. -/
lemma mem_coordsTrimmed {p : Fin L × Fin L} :
    p ∈ coordsTrimmed L ↔ p ≠ (zeroCoord L, zeroCoord L) :=
  (nodup_coords L).mem_erase_iff.trans (and_iff_left (mem_coords L p))

/-- The trimmed list has `2 * L * L - 2` checks. -/
lemma generatorsListPackaged_length :
    (generatorsListPackaged L).length = numQubits L - 2 := by
  have h : (coordsTrimmed L).length = L * L - 1 := by
    rw [coordsTrimmed, List.length_erase_of_mem (mem_coords L _),
      show (coords L).length = L * L from
        (List.length_product _ _).trans (by rw [List.length_finRange])]
  rw [generatorsListPackaged, List.length_append, generatorsListZTrimmed, generatorsListXTrimmed,
    List.length_map, List.length_map, h, numQubits, Nat.mul_assoc]
  omega

/-- Every check of the trimmed list has phase `+1`. -/
lemma allPhaseZero_generatorsListPackaged : AllPhaseZero (generatorsListPackaged L) := by
  intro g hg
  rcases List.mem_append.1 hg with h | h <;> obtain ⟨p, -, rfl⟩ := List.mem_map.1 h <;> rfl

/-- The checks of the trimmed list are checks of the toric code. -/
lemma listToSet_packaged_subset_full :
    listToSet (generatorsListPackaged L) ⊆ generators L := by
  intro g hg
  rcases List.mem_append.1 hg with h | h <;> obtain ⟨p, -, rfl⟩ := List.mem_map.1 h
  exacts [Or.inl ⟨p, rfl⟩, Or.inr ⟨p, rfl⟩]

/-- If `φ` turns sums into products and the `c p` sum to `0` over all sites
`p`, then `φ (c (0, 0))` times the product of the `φ (c p)` over the other
sites is `1`. -/
private lemma mul_prod_map_coordsTrimmed {M G : Type*} [AddCommMonoid M] [Monoid G]
    (φ : M → G) (h0 : φ 0 = 1) (hadd : ∀ a b, φ (a + b) = φ a * φ b)
    (c : Fin L × Fin L → M) (hc : ∑ p, c p = 0) :
    φ (c (zeroCoord L, zeroCoord L)) * ((coordsTrimmed L).map fun p => φ (c p)).prod = 1 := by
  have h : ∀ l : List (Fin L × Fin L), (l.map fun p => φ (c p)).prod = φ (l.map c).sum := by
    intro l
    induction l with
    | nil => exact h0.symm
    | cons a l ih => rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.sum_cons, hadd]
  rw [← List.prod_cons, ← List.map_cons (f := fun p => φ (c p)), h,
    ← ((coords_perm L).map c).sum_eq, ← List.sum_toFinset c (nodup_coords L),
    Finset.eq_univ_iff_forall.2 fun p => List.mem_toFinset.2 (mem_coords L p), hc, h0]

end Trimmed

variable (L : ℕ) [Fact (2 ≤ L)]

/-! ## The dropped checks -/

/-- The product of all vertex checks is the identity: every edge has two
endpoints. -/
theorem vertexStab_zero_mul_prod_generatorsListZTrimmed :
    vertexStab L (zeroCoord L) (zeroCoord L) * (generatorsListZTrimmed L).prod = 1 := by
  have h : (fun p : Fin L × Fin L => vertexStab L p.1 p.2) =
      fun p => toricZOperatorOfChain L (δ⁰ L (singleVtx p)) :=
    funext fun p => vertexStab_eq_toricZOperatorOfChain L p.1 p.2
  rw [generatorsListZTrimmed, h, vertexStab_eq_toricZOperatorOfChain]
  refine mul_prod_map_coordsTrimmed L _ (toricZOperatorOfChain_zero L)
    (toricZOperatorOfChain_add L) (fun p => δ⁰ L (singleVtx p)) ?_
  rw [← map_sum]
  exact (mem_ker_cutMap_iff L _).2 ⟨1, funext fun q => by simp [singleVtx]⟩

/-- The product of all face checks is the identity: every edge borders two
faces. -/
theorem faceStab_zero_mul_prod_generatorsListXTrimmed :
    faceStab L (zeroCoord L) (zeroCoord L) * (generatorsListXTrimmed L).prod = 1 := by
  have h : (fun p : Fin L × Fin L => faceStab L p.1 p.2) =
      fun p => toricXOperatorOfChain L (∂₂ L (singleFace p)) :=
    funext fun p => faceStab_eq_toricXOperatorOfChain L p.1 p.2
  rw [generatorsListXTrimmed, h, faceStab_eq_toricXOperatorOfChain]
  refine mul_prod_map_coordsTrimmed L _ (toricXOperatorOfChain_zero L)
    (toricXOperatorOfChain_add L) (fun p => ∂₂ L (singleFace p)) ?_
  rw [← map_sum]
  exact (mem_ker_boundary2_iff L _).2 ⟨1, funext fun q => by simp [singleFace]⟩

/-- The trimmed list generates the whole stabilizer group: each of the two
dropped checks is the product of the other checks of its type. -/
theorem closure_packaged_eq_full :
    Subgroup.closure (listToSet (generatorsListPackaged L)) = (stabilizerGroup L).toSubgroup := by
  rw [stabilizerGroup_toSubgroup_eq]
  refine le_antisymm (Subgroup.closure_mono (listToSet_packaged_subset_full L))
    ((Subgroup.closure_le _).2 ?_)
  have hZ : ∀ x y, vertexStab L x y ∈
      Subgroup.closure (listToSet (generatorsListPackaged L)) := fun x y => by
    by_cases hp : (x, y) = (zeroCoord L, zeroCoord L)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
      rw [eq_inv_of_mul_eq_one_left (vertexStab_zero_mul_prod_generatorsListZTrimmed L)]
      exact Subgroup.inv_mem _ (Subgroup.list_prod_mem _ fun g hg =>
        Subgroup.subset_closure (List.mem_append_left _ hg))
    · exact Subgroup.subset_closure (List.mem_append_left _
        (List.mem_map.2 ⟨(x, y), (mem_coordsTrimmed L).2 hp, rfl⟩))
  have hX : ∀ x y, faceStab L x y ∈
      Subgroup.closure (listToSet (generatorsListPackaged L)) := fun x y => by
    by_cases hp : (x, y) = (zeroCoord L, zeroCoord L)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
      rw [eq_inv_of_mul_eq_one_left (faceStab_zero_mul_prod_generatorsListXTrimmed L)]
      exact Subgroup.inv_mem _ (Subgroup.list_prod_mem _ fun g hg =>
        Subgroup.subset_closure (List.mem_append_right _ hg))
    · exact Subgroup.subset_closure (List.mem_append_right _
        (List.mem_map.2 ⟨(x, y), (mem_coordsTrimmed L).2 hp, rfl⟩))
  rintro _ (⟨p, rfl⟩ | ⟨p, rfl⟩)
  exacts [hZ p.1 p.2, hX p.1 p.2]

/-- The checks of the trimmed list pairwise commute. -/
lemma generators_commute_packaged :
    ∀ g ∈ listToSet (generatorsListPackaged L), ∀ h ∈ listToSet (generatorsListPackaged L),
      g * h = h * g :=
  fun g hg h hh => generators_commute L g (listToSet_packaged_subset_full L hg) h
    (listToSet_packaged_subset_full L hh)

/-- `-I` is not in the subgroup generated by the trimmed list. -/
lemma negIdentity_not_mem_packaged :
    StabilizerGroup.negIdentity (numQubits L) ∉
      Subgroup.closure (listToSet (generatorsListPackaged L)) := by
  rw [closure_packaged_eq_full, stabilizerGroup_toSubgroup_eq]
  exact negIdentity_not_mem L

/-- The checks of the trimmed list are independent: they generate the
stabilizer group, whose symplectic image has dimension
`2 * L * L - dim H₁ = 2 * L * L - 2`, the length of the list. -/
theorem rowsLinearIndependent_generatorsListPackaged :
    rowsLinearIndependent (generatorsListPackaged L) := by
  have h := (toricHomologicalCode L).finrank_sympImage_eq_numQubits_sub_finrank_H1
  have h2 : Module.finrank (ZMod 2) (toricHomologicalCode L).H1 = 2 := toric_finrank_H1_eq_two L
  rw [h2] at h
  exact rowsLinearIndependent_of_length_eq_finrank_sympImage
    (toricHomologicalCode L).homologicalStabilizerGroup _
    ((stabilizerGroup_toSubgroup_eq_homologicalStabilizerGroup L).symm.trans
      (closure_packaged_eq_full L).symm)
    ((generatorsListPackaged_length L).trans h.symm)

/-! ## The stabilizer code -/

/-- The trimmed list of `2 * L * L - 2` checks as a presentation of a
`[[2 * L * L, 2]]` code. -/
def toricPresentation : StabilizerCode.Presentation (2 * L * L) 2 where
  hk := by have : 2 ≤ L := Fact.out; nlinarith
  generatorsList := generatorsListPackaged L
  generators_length := generatorsListPackaged_length L
  generators_phaseZero := allPhaseZero_generatorsListPackaged L
  generators_independent := rowsLinearIndependent_generatorsListPackaged L
  generators_commute := generators_commute_packaged L
  closure_no_neg_identity := negIdentity_not_mem_packaged L

/-- The toric code as a `[[2 * L * L, 2]]` stabilizer code. -/
noncomputable def toricStabilizerCode : StabilizerCode (2 * L * L) 2 :=
  (toricPresentation L).toCode

/-- The stabilizer group of `toricStabilizerCode L` is `stabilizerGroup L`. -/
theorem toricStabilizerCode_subgroup_eq :
    (toricStabilizerCode L).toStabilizerGroup.toSubgroup = (stabilizerGroup L).toSubgroup :=
  closure_packaged_eq_full L

/-- The stabilizer group of `toricStabilizerCode L` is the homological
stabilizer group of `toricHomologicalCode L`. -/
theorem toricStabilizerCode_toSubgroup_eq_homologicalStabilizerGroup :
    (toricStabilizerCode L).toStabilizerGroup.toSubgroup =
      (toricHomologicalCode L).homologicalStabilizerGroup.toSubgroup :=
  (toricStabilizerCode_subgroup_eq L).trans
    (stabilizerGroup_toSubgroup_eq_homologicalStabilizerGroup L)

/-- The code `(toricHomologicalCode L).toStabilizerCode`, which the general
theory builds from the chain complex without choosing independent checks, has
the same stabilizer group as `toricStabilizerCode L`. -/
theorem toricHomologicalCode_toStabilizerCode_subgroup_eq :
    (toricHomologicalCode L).toStabilizerCode.toStabilizerGroup.toSubgroup =
      (toricStabilizerCode L).toStabilizerGroup.toSubgroup :=
  (toricStabilizerCode_toSubgroup_eq_homologicalStabilizerGroup L).symm

/-! ## Logical operators -/

/-- The X-chain operator of a cycle commutes with the stabilizer group of
`toricStabilizerCode L`. -/
lemma mem_centralizer_of_mem_toricCycles {c : C1 L} (hc : c ∈ Z₁ L) :
    toricXOperatorOfChain L c ∈ centralizer (toricStabilizerCode L).toStabilizerGroup := by
  rw [centralizer_eq_of_toSubgroup_eq _ _ (toricStabilizerCode_subgroup_eq L)]
  exact (toricXOperatorOfChain_mem_centralizer_iff_mem_toricCycles L c).2 hc

/-- The Z-chain operator of a dual cycle commutes with the stabilizer group of
`toricStabilizerCode L`. -/
lemma mem_centralizer_of_mem_toricDualCycles {c : C1 L} (hc : c ∈ Z¹ L) :
    toricZOperatorOfChain L c ∈ centralizer (toricStabilizerCode L).toStabilizerGroup := by
  rw [centralizer_eq_of_toSubgroup_eq _ _ (toricStabilizerCode_subgroup_eq L)]
  exact (toricZOperatorOfChain_mem_centralizer_iff_mem_toricDualCycles L c).2 hc

/-- The X-operator of the loop `loopChain L a b` commutes with the Z-operator
of the dual loop `dualLoopChain L a' b'` iff `a * a' + b * b' = 0`: the two
loops share one horizontal edge if `a = a' = 1`, and one vertical edge if
`b = b' = 1`. -/
theorem loopXOperator_commutes_dualLoopZOperator_iff (a b a' b' : ZMod 2) :
    toricXOperatorOfChain L (loopChain L a b) *
          toricZOperatorOfChain L (dualLoopChain L a' b') =
        toricZOperatorOfChain L (dualLoopChain L a' b') *
          toricXOperatorOfChain L (loopChain L a b) ↔
      a * a' + b * b' = 0 := by
  have h : ∑ e : EdgeIdx L, loopChain L a b e * dualLoopChain L a' b' e = a * a' + b * b' := by
    rw [← (edgeIdxEquivSum L).symm.sum_comp, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Fintype.sum_prod_type]
    simp [edgeIdxEquivSum, loopChain, dualLoopChain]
  rw [← h]
  exact HomologicalCode.chainXOperator_commutes_chainZOperator_iff (X := toricHomologicalCode L) _ _

/-- The horizontal X-loop anticommutes with `horizontalHRowZOperator L`: they
share one horizontal edge. -/
theorem horizontalLoopXOperator_anticommutes_horizontalHRowZOperator :
    Anticommute (horizontalLoopXOperator L) (horizontalHRowZOperator L) :=
  (commute_or_anticommute _ _).resolve_left fun h =>
    absurd ((loopXOperator_commutes_dualLoopZOperator_iff L 1 0 1 0).1 h) (by decide)

/-- The vertical X-loop anticommutes with `verticalVRowZOperator L`: they share
one vertical edge. -/
theorem verticalLoopXOperator_anticommutes_verticalVRowZOperator :
    Anticommute (verticalLoopXOperator L) (verticalVRowZOperator L) :=
  (commute_or_anticommute _ _).resolve_left fun h =>
    absurd ((loopXOperator_commutes_dualLoopZOperator_iff L 0 1 0 1).1 h) (by decide)

/-- The logical operators of the two logical qubits: the horizontal X-loop
with `horizontalHRowZOperator L`, and the vertical X-loop with
`verticalVRowZOperator L`. -/
noncomputable def logicalOps :
    Fin 2 → LogicalQubitOps (numQubits L) (toricStabilizerCode L).toStabilizerGroup
  | 0 =>
    { xOp := horizontalLoopXOperator L
      zOp := horizontalHRowZOperator L
      x_mem_centralizer := mem_centralizer_of_mem_toricCycles L (loopChain_mem_toricCycles L 1 0)
      z_mem_centralizer :=
        mem_centralizer_of_mem_toricDualCycles L (dualLoopChain_mem_toricDualCycles L 1 0)
      anticommute := horizontalLoopXOperator_anticommutes_horizontalHRowZOperator L }
  | 1 =>
    { xOp := verticalLoopXOperator L
      zOp := verticalVRowZOperator L
      x_mem_centralizer := mem_centralizer_of_mem_toricCycles L (loopChain_mem_toricCycles L 0 1)
      z_mem_centralizer :=
        mem_centralizer_of_mem_toricDualCycles L (dualLoopChain_mem_toricDualCycles L 0 1)
      anticommute := verticalLoopXOperator_anticommutes_verticalVRowZOperator L }

/-- The logical operators of the two logical qubits commute with each other. -/
theorem logicalOps_commute_cross : ∀ ℓ ℓ', ℓ ≠ ℓ' →
    ((logicalOps L ℓ).xOp * (logicalOps L ℓ').xOp =
        (logicalOps L ℓ').xOp * (logicalOps L ℓ).xOp ∧
      (logicalOps L ℓ).xOp * (logicalOps L ℓ').zOp =
        (logicalOps L ℓ').zOp * (logicalOps L ℓ).xOp ∧
      (logicalOps L ℓ).zOp * (logicalOps L ℓ').xOp =
        (logicalOps L ℓ').xOp * (logicalOps L ℓ).zOp ∧
      (logicalOps L ℓ).zOp * (logicalOps L ℓ').zOp =
        (logicalOps L ℓ').zOp * (logicalOps L ℓ).zOp) := by
  have hXX := (horizontalLoopXOperator_isXType L).commute (verticalLoopXOperator_isXType L)
  have hZZ := (horizontalHRowZOperator_isZType L).commute (verticalVRowZOperator_isZType L)
  have hXZ : horizontalLoopXOperator L * verticalVRowZOperator L =
      verticalVRowZOperator L * horizontalLoopXOperator L :=
    (loopXOperator_commutes_dualLoopZOperator_iff L 1 0 0 1).2 (by decide)
  have hZX : horizontalHRowZOperator L * verticalLoopXOperator L =
      verticalLoopXOperator L * horizontalHRowZOperator L :=
    ((loopXOperator_commutes_dualLoopZOperator_iff L 0 1 1 0).2 (by decide)).symm
  rw [Fin.forall_fin_two]
  constructor <;> rw [Fin.forall_fin_two]
  · exact ⟨fun h => absurd rfl h, fun _ => ⟨hXX, hXZ, hZX, hZZ⟩⟩
  · exact ⟨fun _ => ⟨hXX.symm, hZX.symm, hXZ.symm, hZZ.symm⟩, fun h => absurd rfl h⟩

/-- The toric code with its two pairs of logical operators `logicalOps L`. -/
noncomputable def toricStabilizerCodeWithLogicals : StabilizerCodeWithLogicals (2 * L * L) 2 where
  toStabilizerCode := toricStabilizerCode L
  logicalOps := logicalOps L
  logical_commute_cross := logicalOps_commute_cross L

end ToricCodeN
end StabilizerGroup
end Quantum
