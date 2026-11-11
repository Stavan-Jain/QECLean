import QEC.Stabilizer.Codes.RotatedSurface.N
import QEC.Stabilizer.Codes.RotatedSurface.H1Dimension
import QEC.Stabilizer.Framework.Homological.Presentation

/-!
# The rotated surface code as a `StabilizerCode`

The rotated surface code of odd size `L ≥ 3` encodes one logical qubit in
`numQubits L = L * L` physical qubits.

* `rowsLinearIndependent_generatorsList`: the `L * L - 1` checks of
  `generatorsList L` are independent, because the Z-check combination map `δ⁰`
  and the X-check combination map `∂₂` are injective (`rscZCutMap_injective`,
  `rscBoundary2_injective`). It is derived from
  `HomologicalCode.linearIndependent_cellGenerator` through
  `NQubitPauliGroupElement.rowsLinearIndependent_map_append_map`, a general
  statement on the check matrix of a list that enumerates a linearly
  independent family.
* `rotatedSurfacePresentation L` and `rotatedSurfaceStabilizerCode L`: the
  presentation by `generatorsList L`, in which no check is redundant, and the
  `[[L * L, 1]]` code it presents. Its stabilizer subgroup is that of
  `stabilizerGroup L` (`rotatedSurfaceStabilizerCode_subgroup_eq`) and of the
  homological stabilizer group of `rotatedSurfaceHomologicalCode L`
  (`rotatedSurfaceStabilizerCode_toSubgroup_eq_homologicalStabilizerGroup`).
* `middleColChain L` and `middleRowChain L`: the middle column and the middle
  row of the grid. The column is a cycle (`middleColChain_mem_cycles`) and the
  row a dual cycle (`middleRowChain_mem_dualCycles`), since a Z-check meets
  every column, and an X-check every row, in an even number of qubits.
* `logicalX L` and `logicalZ L`: the X-string on the middle column and the
  Z-string on the middle row. They commute with the stabilizer group
  (`logicalX_mem_centralizer`, `logicalZ_mem_centralizer`) and anticommute
  with each other (`logicalX_anticommutes_logicalZ`), since the column and the
  row meet in the single qubit at the centre of the grid.
* `rotatedSurfaceStabilizerCodeWithLogicals L`: the code together with this
  pair of logical operators.
-/

namespace Quantum
namespace NQubitPauliGroupElement

open NQubitPauliOperator

/-! ## Row independence of mapped lists -/

/-- If the symplectic vectors of the elements `g i` are linearly independent,
then the check matrix of `l.map g` has linearly independent rows for every
list `l` without repetitions. -/
lemma rowsLinearIndependent_map_of_nodup {ι : Type*} {n : ℕ}
    {g : ι → NQubitPauliGroupElement n}
    (hg : LinearIndependent (ZMod 2) fun i => toSymplectic (g i).operators)
    {l : List ι} (hl : l.Nodup) : rowsLinearIndependent (l.map g) := by
  have key : (fun k => checkMatrix (l.map g) k) =
      (fun i => toSymplectic (g i).operators) ∘ fun k => l.get (k.cast (List.length_map g)) := by
    funext k col
    simp [checkMatrix]
  rw [rowsLinearIndependent, key]
  exact hg.comp _ fun _ _ h => Fin.cast_injective _ (List.nodup_iff_injective_get.mp hl h)

/-- `rowsLinearIndependent_map_of_nodup` for two families `f` and `g` listed
one after the other. -/
lemma rowsLinearIndependent_map_append_map {ι κ : Type*} {n : ℕ}
    {f : ι → NQubitPauliGroupElement n} {g : κ → NQubitPauliGroupElement n}
    (h : LinearIndependent (ZMod 2) fun i => toSymplectic (Sum.elim f g i).operators)
    {l : List ι} {m : List κ} (hl : l.Nodup) (hm : m.Nodup) :
    rowsLinearIndependent (l.map f ++ m.map g) := by
  have hnd : (l.map Sum.inl ++ m.map Sum.inr : List (ι ⊕ κ)).Nodup :=
    (hl.map Sum.inl_injective).append (hm.map Sum.inr_injective) (by simp [List.Disjoint])
  simpa using rowsLinearIndependent_map_of_nodup h hnd

end NQubitPauliGroupElement

namespace StabilizerGroup
namespace RotatedSurfaceCodeN

open scoped RotatedSurfaceChain
open NQubitPauliGroupElement Stabilizer.Homological Stabilizer.Lattice.RotatedSurface

variable (L : ℕ) [Fact (Odd L)] [Fact (3 ≤ L)]

/-! ## Independence of the checks -/

/-- The checks of the rotated surface code have linearly independent
check-matrix rows: the Z-check combination map `δ⁰` and the X-check
combination map `∂₂` are injective. -/
theorem rowsLinearIndependent_generatorsList : rowsLinearIndependent (generatorsList L) :=
  rowsLinearIndependent_map_append_map
    ((rotatedSurfaceHomologicalCode L).linearIndependent_cellGenerator
      (rotatedSurfaceHomologicalCode_cutMap_eq L ▸ rscZCutMap_injective) rscBoundary2_injective)
    (Finset.nodup_toList _) (Finset.nodup_toList _)

/-- No check of the rotated surface code is a product of the others. -/
theorem GeneratorsIndependent_generatorsList :
    GeneratorsIndependent (numQubits L) (generatorsList L) :=
  GeneratorsIndependent_of_rowsLinearIndependent (rowsLinearIndependent_generatorsList L)

/-! ## The stabilizer code -/

/-- The `L * L - 1` checks of `generatorsList L` as a presentation of an
`[[L * L, 1]]` code. -/
noncomputable def rotatedSurfacePresentation :
    StabilizerCode.Presentation (numQubits L) 1 where
  hk := Nat.mul_pos (Fact.out : Odd L).pos (Fact.out : Odd L).pos
  generatorsList := generatorsList L
  generators_length := generatorsList_length L
  generators_phaseZero := allPhaseZero_generatorsList L
  generators_independent := rowsLinearIndependent_generatorsList L
  generators_commute := by
    have h := generators_commute L
    rw [← listToSet_generatorsList] at h
    exact h
  closure_no_neg_identity := by rw [listToSet_generatorsList]; exact negIdentity_not_mem L

/-- The rotated surface code as an `[[L * L, 1]]` stabilizer code. -/
noncomputable def rotatedSurfaceStabilizerCode : StabilizerCode (numQubits L) 1 :=
  (rotatedSurfacePresentation L).toCode

/-- The stabilizer subgroup of `rotatedSurfaceStabilizerCode L` is that of
`stabilizerGroup L`. -/
theorem rotatedSurfaceStabilizerCode_subgroup_eq :
    (rotatedSurfaceStabilizerCode L).toStabilizerGroup.toSubgroup =
      (stabilizerGroup L).toSubgroup := rfl

/-- The stabilizer subgroup of `rotatedSurfaceStabilizerCode L` is that of the
homological stabilizer group of `rotatedSurfaceHomologicalCode L`. -/
theorem rotatedSurfaceStabilizerCode_toSubgroup_eq_homologicalStabilizerGroup :
    (rotatedSurfaceStabilizerCode L).toStabilizerGroup.toSubgroup =
      (rotatedSurfaceHomologicalCode L).homologicalStabilizerGroup.toSubgroup :=
  stabilizerGroup_toSubgroup_eq_homologicalStabilizerGroup L

/-! ## The middle column and the middle row -/

/-- The index `(L - 1) / 2` of the middle column and of the middle row. -/
def midIdx : Fin L :=
  ⟨(L - 1) / 2, by have h3 : 3 ≤ L := Fact.out; omega⟩

omit [Fact (Odd L)] in
@[simp] lemma midIdx_val : (midIdx L).val = (L - 1) / 2 := rfl

/-- The middle column as a 1-chain: `1` on the qubits `(x, y)` with
`x = (L - 1) / 2`. -/
def middleColChain : VtxIdx L → ZMod 2 :=
  fun v => if v.1.val = (L - 1) / 2 then 1 else 0

/-- The middle row as a 1-chain: `1` on the qubits `(x, y)` with
`y = (L - 1) / 2`. -/
def middleRowChain : VtxIdx L → ZMod 2 :=
  fun v => if v.2.val = (L - 1) / 2 then 1 else 0

omit [Fact (Odd L)] in
/-- The middle column is a cycle: it meets every Z-check in an even number of
qubits. -/
theorem middleColChain_mem_cycles : middleColChain L ∈ Z₁ L := by
  refine funext fun zf => ?_
  have h := even_card_col_inter_zFaceSupport zf (midIdx L)
  rw [Finset.filter_inter, Finset.univ_inter] at h
  simpa [middleColChain, Fin.ext_iff, Finset.sum_boole, ZMod.natCast_eq_zero_iff_even] using h

/-- The transpose of `∂₂` sends a chain to its sum over the support of each
X-check. -/
lemma dualBoundary_apply_eq_sum (c : VtxIdx L → ZMod 2) (xf : XFaceIdx L) :
    (rotatedSurfaceHomologicalCode L).dualBoundary c xf = ∑ v ∈ xFaceSupport xf, c v :=
  (Finset.sum_congr rfl fun v _ =>
    (congrArg (c v * ·) (rscBoundary2_single L xf v)).trans (mul_boole _ _)).trans
    (Fintype.sum_ite_mem _ _)

/-- The middle row is a dual cycle: it meets every X-check in an even number
of qubits. -/
theorem middleRowChain_mem_dualCycles :
    middleRowChain L ∈ (rotatedSurfaceHomologicalCode L).dualCycles := by
  refine funext fun xf => ?_
  have h := even_card_row_inter_xFaceSupport xf (midIdx L)
  rw [Finset.filter_inter, Finset.univ_inter] at h
  rw [dualBoundary_apply_eq_sum]
  simpa [middleRowChain, Fin.ext_iff, Finset.sum_boole, ZMod.natCast_eq_zero_iff_even] using h

/-- The middle column and the middle row pair to `1`: they meet in the single
qubit at the centre of the grid. -/
lemma chainInnerProduct_middleColChain_middleRowChain :
    (rotatedSurfaceHomologicalCode L).chainInnerProduct (middleColChain L)
      (middleRowChain L) = 1 := by
  have h : ∀ v : VtxIdx L, middleColChain L v * middleRowChain L v =
      if v = (midIdx L, midIdx L) then 1 else 0 := by
    rintro ⟨a, b⟩
    simp [middleColChain, middleRowChain, Prod.ext_iff, Fin.ext_iff, ← ite_and, and_comm]
  exact (Fintype.sum_congr _ _ h).trans (by simp)

/-! ## Logical operators -/

/-- The logical X operator: `X` on the qubits of the middle column. -/
noncomputable def logicalX : NQubitPauliGroupElement (numQubits L) :=
  (rotatedSurfaceHomologicalCode L).chainXOperator (middleColChain L)

/-- The logical Z operator: `Z` on the qubits of the middle row. -/
noncomputable def logicalZ : NQubitPauliGroupElement (numQubits L) :=
  (rotatedSurfaceHomologicalCode L).chainZOperator (middleRowChain L)

/-- The logical X operator commutes with every stabilizer: the middle column
is a cycle. -/
lemma logicalX_mem_centralizer : logicalX L ∈ centralizer (stabilizerGroup L) := by
  rw [centralizer_eq_of_toSubgroup_eq _ _
    (stabilizerGroup_toSubgroup_eq_homologicalStabilizerGroup L)]
  exact (HomologicalCode.chainXOperator_mem_centralizer_iff_mem_cycles _).2
    (middleColChain_mem_cycles L)

/-- The logical Z operator commutes with every stabilizer: the middle row is a
dual cycle. -/
lemma logicalZ_mem_centralizer : logicalZ L ∈ centralizer (stabilizerGroup L) := by
  rw [centralizer_eq_of_toSubgroup_eq _ _
    (stabilizerGroup_toSubgroup_eq_homologicalStabilizerGroup L)]
  exact (HomologicalCode.chainZOperator_mem_centralizer_iff_mem_dualCycles _).2
    (middleRowChain_mem_dualCycles L)

/-- The logical X and Z operators anticommute, because the middle column and
the middle row pair to `1`. -/
theorem logicalX_anticommutes_logicalZ : Anticommute (logicalX L) (logicalZ L) :=
  (commute_or_anticommute _ _).resolve_left fun hc => one_ne_zero <|
    (chainInnerProduct_middleColChain_middleRowChain L).symm.trans <|
      (HomologicalCode.chainXOperator_commutes_chainZOperator_iff
        (X := rotatedSurfaceHomologicalCode L) _ _).1 hc

/-- The logical operators of the one logical qubit of the rotated surface
code. -/
noncomputable def logicalOps : Fin 1 → LogicalQubitOps (numQubits L) (stabilizerGroup L) :=
  fun _ => ⟨logicalX L, logicalZ L, logicalX_mem_centralizer L, logicalZ_mem_centralizer L,
    logicalX_anticommutes_logicalZ L⟩

/-- The rotated surface code together with its logical operators `logicalX L`
and `logicalZ L`. -/
noncomputable def rotatedSurfaceStabilizerCodeWithLogicals :
    StabilizerCodeWithLogicals (numQubits L) 1 where
  toStabilizerCode := rotatedSurfaceStabilizerCode L
  logicalOps := logicalOps L
  logical_commute_cross := fun ℓ ℓ' h => (h (Subsingleton.elim ℓ ℓ')).elim

end RotatedSurfaceCodeN
end StabilizerGroup
end Quantum
