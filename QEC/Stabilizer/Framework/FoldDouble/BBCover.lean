import QEC.Stabilizer.Framework.Homological.BBDeficitWall
import QEC.Stabilizer.Framework.Homological.Distance
import QEC.Stabilizer.Framework.FoldDouble.Distance

/-!
# Fold and double for a free double cover of a bivariate bicycle code

A free double cover `D : XDoubleCoverData G H` of bivariate bicycle codes pairs
the cover qubits `G × Fin 2` by the deck translation: each qubit `q` with its
partner `D.deckSigma1 q`, the pair being indexed by the base qubit
`Prod.map D.proj id q`, with the section `D.sec1` picking sheet `0`. This file
makes the cover code an instance of the fold-and-double framework and derives
the doubling theorem from the fold-and-double distance theorem.

It opens with two facts about the chain operators of any homological code:
every stabilizer is the Z-type chain operator of a dual boundary times the
X-type chain operator of a boundary
(`exists_eq_chainZOperator_mul_chainXOperator`), and every X-type operator is
the operator part of an X-type chain operator
(`exists_chainXOperator_operators_eq`).

## The dictionary

* `D.pairing : Fin n ≃ Fin m × Fin 2` is the pairing on the qubit indices of
  the cover code, with the base qubit indices as the pairs.
* On X-type and Z-type chain operators, the sheets are `D.sheet0` and
  `D.sheet1`, the fold is the pushforward `D.push1`, the double is the
  pullback `D.pull1`, and the sheet swap is the deck shift `D.deckShift1`
  (`fold_chainXOperator`, `double_chainXOperator`,
  `sheetSwap_chainXOperator` and their Z-type counterparts).
* The X-type chain operator of a base chain `c` lies in the doubling group iff
  `D.pull1 c` is a cover cycle, in the seam group iff `D.pull1 c` is a cover
  boundary, and in the stabilizer folds iff `c` is a base boundary
  (`chainXOperator_mem_doublingGroup_iff`, `chainXOperator_mem_seamGroup_iff`,
  `chainXOperator_mem_foldImage_iff`).

## The hypotheses of the fold-and-double theorem

The symmetric form `isLeast_logicalWeight_two_mul_of_symmetric` of the
fold-and-double theorem asks for a symmetric pairing and for conditions (R),
(F) and (S). For the cover code:

* the pairing is symmetric (`isSymmetric_pairing`), because boundaries and
  dual boundaries are invariant under the deck shift;
* `DeckTrivialOnH1` gives (R), `g * g^σ` is a stabilizer, for every logical
  operator `g` of any Pauli type (`condition_R_of_deckTrivialOnH1`); the Z side
  follows from the X side through the duality involution `bbDualFn`, which
  commutes with the deck shift;
* `SeamCosetFloor (2 * d)` gives (F), weight `≥ 2 * d`, for the X-type seam
  logicals (`condition_F_of_seamCosetFloor`), which are the chain operators of
  the elements of the seam cosets that are not base boundaries;
* `DangerousFloorNZ (2 * d)` gives (S), `wt b + 2 · residualWeight v ≥ 2 * d`,
  for the nontrivial logical operators `v` with X-type operator part that fold
  to a stabilizer fold `b ≠ 1` (`condition_S_of_dangerousFloorNZ`).

## The doubling theorem

Conditions (F) and (S) are available for X-type operators only, so the
fold-and-double theorem is applied in its sector form
`isLeast_logicalWeight_two_mul_of_floors_sector`, to the X-type operators. Its
first hypothesis is `isLeast_xType_doublingLogical`: the least weight of an
X-type doubling logical is the least weight `d` of a base cycle that is not a
boundary. The sector theorem bounds the X-type logical operators of the cover
code, the duality `bb_cycle_bound_iff_dual_bound` transfers the bound to the
Z-type ones, and `chainWeight_lower_bound_transfers` to every logical
operator. The result, `isLeast_logicalWeight_two_mul_of_foldDouble`, has
exactly the hypotheses and the conclusion of
`pauli_distance_eq_double_of_admissible`.
-/

namespace Quantum
namespace Stabilizer
namespace Homological

open NQubitPauliOperator NQubitPauliGroupElement StabilizerGroup FoldDouble

/-! ## Chain operators of a homological code -/

namespace HomologicalCode

variable {X : HomologicalCode}

/-- Two operators on the qubits of a homological code are equal once they agree
on the qubit of every edge. -/
lemma operators_ext_edgeEquiv {u w : NQubitPauliOperator X.numQubits}
    (h : ∀ e : X.C1, u (X.edgeEquiv e) = w (X.edgeEquiv e)) : u = w :=
  funext (X.edgeEquiv.surjective.forall.2 h)

/-- The operator part of a Pauli element is the product of the X-type chain
operator of its X-support and the Z-type chain operator of its Z-support. -/
lemma operators_eq_chainXOperator_mul_chainZOperator
    (g : NQubitPauliGroupElement X.numQubits) :
    g.operators =
      (X.chainXOperator (X.xChainOf g)).operators *
        (X.chainZOperator (X.zChainOf g)).operators := by
  ext i
  rw [NQubitPauliOperator.mul_apply, chainXOperator_xChainOf_op_at, chainZOperator_zChainOf_op_at]
  generalize g.operators i = a
  cases a <;> decide

/-- Every X-type operator is the operator part of an X-type chain operator. -/
lemma exists_chainXOperator_operators_eq {u : NQubitPauliOperator X.numQubits}
    (hu : IsXType u) : ∃ c : X.C1 → ZMod 2, (X.chainXOperator c).operators = u :=
  ⟨_, congrArg operators
    (chainXOperator_xChainOf (g := ofOperator u) ⟨rfl, hu⟩)⟩

/-- The X-type chain operator of a boundary is a stabilizer. -/
lemma chainXOperator_mem_of_mem_boundaries {c : X.C1 → ZMod 2} (hc : c ∈ X.boundaries) :
    X.chainXOperator c ∈ X.homologicalStabilizerGroup.toSubgroup :=
  X.closure_XGenerators_le ((chainXOperator_mem_XClosure_iff_mem_boundaries c).mpr hc)

/-- The Z-type chain operator of a dual boundary is a stabilizer. -/
lemma chainZOperator_mem_of_mem_dualBoundaries {c : X.C1 → ZMod 2}
    (hc : c ∈ X.dualBoundaries) :
    X.chainZOperator c ∈ X.homologicalStabilizerGroup.toSubgroup :=
  X.closure_ZGenerators_le ((chainZOperator_mem_ZClosure_iff_mem_dualBoundaries c).mpr hc)

/-- The X-type chain operator of `c` has the operator part of a stabilizer iff
`c` is a boundary. -/
lemma chainXOperator_operators_mem_operatorImage_iff (c : X.C1 → ZMod 2) :
    (X.chainXOperator c).operators ∈ operatorImage X.homologicalStabilizerGroup.toSubgroup ↔
      c ∈ X.boundaries :=
  ⟨fun ⟨s, hs, h⟩ => stabilizer_same_ops_implies_boundary c s hs h,
    fun h => operators_mem_operatorImage (chainXOperator_mem_of_mem_boundaries h)⟩

/-- The CSS decomposition of a stabilizer: the Z-type chain operator of a dual
boundary times the X-type chain operator of a boundary. -/
lemma exists_eq_chainZOperator_mul_chainXOperator {s : NQubitPauliGroupElement X.numQubits}
    (hs : s ∈ X.homologicalStabilizerGroup.toSubgroup) :
    ∃ cz ∈ X.dualBoundaries, ∃ cx ∈ X.boundaries,
      s = X.chainZOperator cz * X.chainXOperator cx := by
  obtain ⟨z, hz, x, hx, rfl⟩ :=
    Subgroup.mem_closure_union_exists_mul_of_commute_generators ZGenerators_commute_XGenerators s hs
  have hz' := chainZOperator_zChainOf
    (IsZTypeElement_of_mem_closure ZGenerators_isZType z hz)
  have hx' := chainXOperator_xChainOf
    (IsXTypeElement_of_mem_closure XGenerators_isXType x hx)
  exact ⟨X.zChainOf z, (chainZOperator_mem_ZClosure_iff_mem_dualBoundaries _).mp (by rwa [hz']),
    X.xChainOf x, (chainXOperator_mem_XClosure_iff_mem_boundaries _).mp (by rwa [hx']),
    by rw [hz', hx']⟩

end HomologicalCode

namespace BB

open HomologicalCode

variable {G H : Type}
  [Fintype G] [AddCommGroup G] [DecidableEq G]
  [Fintype H] [AddCommGroup H] [DecidableEq H]

/-- `bbDualFn c` is a boundary iff `c` is a dual boundary. -/
lemma bbDual_mem_boundaries_iff (A B : G → ZMod 2) (c : G × Fin 2 → ZMod 2) :
    bbDualFn c ∈ (bbChainComplex A B).boundaries ↔ c ∈ (bbChainComplex A B).dualBoundaries := by
  rw [← bbDual_mem_dualBoundaries_iff, bbDualFn_bbDualFn]

/-- `bbDualFn c` is a cycle iff `c` is a dual cycle. -/
lemma bbDual_mem_cycles_iff (A B : G → ZMod 2) (c : G × Fin 2 → ZMod 2) :
    bbDualFn c ∈ (bbChainComplex A B).cycles ↔ c ∈ (bbChainComplex A B).dualCycles := by
  rw [← bbDual_mem_dualCycles_iff, bbDualFn_bbDualFn]

namespace XDoubleCoverData

variable (D : XDoubleCoverData G H)

/-! ## The pairing by the deck translation -/

/-- The pairing of the cover qubits `G × Fin 2` by the deck translation: a
qubit is sent to its base qubit together with its sheet, sheet `0` being the
image of the section. -/
def coverPairing : (G × Fin 2) ≃ (H × Fin 2) × Fin 2 where
  toFun q := ((D.proj q.1, q.2), if q.1 = D.sec (D.proj q.1) then 0 else 1)
  invFun x := (if x.2 = 0 then D.sec x.1.1 else D.sec x.1.1 + D.deckS, x.1.2)
  left_inv := by
    rintro ⟨g, i⟩
    by_cases hg : g = D.sec (D.proj g)
    · simp [← hg]
    · simp [hg, ← (D.point_dichotomy g).resolve_left hg]
  right_inv := by
    rintro ⟨⟨p, i⟩, s⟩
    fin_cases s
    · simp [D.proj_sec]
    · simp [D.proj_add_deckS, D.proj_sec, D.deckS_ne_zero]

@[simp] lemma coverPairing_symm_zero (p : H × Fin 2) :
    D.coverPairing.symm (p, 0) = D.sec1 p := rfl

@[simp] lemma coverPairing_symm_one (p : H × Fin 2) :
    D.coverPairing.symm (p, 1) = D.deckSigma1 (D.sec1 p) := rfl

@[simp] lemma coverPairing_apply_fst (q : G × Fin 2) :
    (D.coverPairing q).1 = Prod.map D.proj id q := rfl

/-- Flipping the sheet of a cover qubit gives its deck partner. -/
lemma coverPairing_symm_rev (x : (H × Fin 2) × Fin 2) :
    D.coverPairing.symm (x.1, Fin.rev x.2) = D.deckSigma1 (D.coverPairing.symm x) := by
  obtain ⟨p, s⟩ := x
  fin_cases s
  · rfl
  · exact Prod.ext (by simp [coverPairing, add_assoc, D.deckS_add_deckS]) rfl

/-- The pairing of the cover code's qubit indices by the deck translation, with
the base code's qubit indices as the pairs. -/
noncomputable def pairing :
    Fin D.coverComplex.numQubits ≃ Fin D.baseComplex.numQubits × Fin 2 :=
  (D.coverComplex.edgeEquiv.symm.trans D.coverPairing).trans
    (D.baseComplex.edgeEquiv.prodCongr (Equiv.refl (Fin 2)))

lemma pairing_apply (q : G × Fin 2) :
    D.pairing (D.coverComplex.edgeEquiv q) =
      (D.baseComplex.edgeEquiv (D.coverPairing q).1, (D.coverPairing q).2) := by
  rw [pairing, Equiv.trans_apply, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

lemma pairing_symm_apply (p : H × Fin 2) (s : Fin 2) :
    D.pairing.symm (D.baseComplex.edgeEquiv p, s) =
      D.coverComplex.edgeEquiv (D.coverPairing.symm (p, s)) :=
  (Equiv.symm_apply_eq _).mpr (by rw [pairing_apply, Equiv.apply_symm_apply])

/-- The partner of a cover qubit under the pairing is its deck partner. -/
lemma partner_pairing (q : G × Fin 2) :
    partner D.pairing (D.coverComplex.edgeEquiv q) =
      D.coverComplex.edgeEquiv (D.deckSigma1 q) := by
  simp only [partner, pairing_apply, pairing_symm_apply,
    D.coverPairing_symm_rev (D.coverPairing q), Equiv.symm_apply_apply]

/-! ## The dictionary on X-type and Z-type chain operators -/

section Dictionary

variable (v : G × Fin 2 → ZMod 2) (u : H × Fin 2 → ZMod 2)

/-- Sheet `0` of an X-type chain operator is the X-type chain operator of sheet
`0` of the chain. -/
lemma sheet_zero_chainXOperator :
    sheet D.pairing 0 (D.coverComplex.chainXOperator v).operators =
      (D.baseComplex.chainXOperator (D.sheet0 v)).operators :=
  operators_ext_edgeEquiv fun p => by
    rw [sheet_apply, pairing_symm_apply, chainXOperator_operators_edgeEquiv,
      chainXOperator_operators_edgeEquiv]
    rfl

/-- Sheet `1` of an X-type chain operator is the X-type chain operator of sheet
`1` of the chain. -/
lemma sheet_one_chainXOperator :
    sheet D.pairing 1 (D.coverComplex.chainXOperator v).operators =
      (D.baseComplex.chainXOperator (D.sheet1 v)).operators :=
  operators_ext_edgeEquiv fun p => by
    rw [sheet_apply, pairing_symm_apply, chainXOperator_operators_edgeEquiv,
      chainXOperator_operators_edgeEquiv]
    rfl

/-- The fold of an X-type chain operator is the X-type chain operator of the
pushforward. -/
theorem fold_chainXOperator :
    fold D.pairing (D.coverComplex.chainXOperator v).operators =
      (D.baseComplex.chainXOperator (D.push1 v)).operators := by
  rw [fold, sheet_zero_chainXOperator, sheet_one_chainXOperator, ← mul_operators,
    ← chainXOperator_add]
  exact congrArg (fun c => (D.baseComplex.chainXOperator c).operators) (D.sheet0_add_sheet1 v)

/-- The double of an X-type chain operator is the X-type chain operator of the
pullback. -/
theorem double_chainXOperator :
    double D.pairing (D.baseComplex.chainXOperator u).operators =
      (D.coverComplex.chainXOperator (D.pull1 u)).operators :=
  operators_ext_edgeEquiv fun q => by
    rw [double_apply, pairing_apply, chainXOperator_operators_edgeEquiv,
      chainXOperator_operators_edgeEquiv]
    rfl

/-- The sheet swap of an X-type chain operator is the X-type chain operator of
the deck shift. -/
theorem sheetSwap_chainXOperator :
    sheetSwap D.pairing (D.coverComplex.chainXOperator v).operators =
      (D.coverComplex.chainXOperator (D.deckShift1 v)).operators :=
  operators_ext_edgeEquiv fun q => by
    rw [sheetSwap_apply, partner_pairing, chainXOperator_operators_edgeEquiv,
      chainXOperator_operators_edgeEquiv]
    rfl

/-- Sheet `0` of a Z-type chain operator is the Z-type chain operator of sheet
`0` of the chain. -/
lemma sheet_zero_chainZOperator :
    sheet D.pairing 0 (D.coverComplex.chainZOperator v).operators =
      (D.baseComplex.chainZOperator (D.sheet0 v)).operators :=
  operators_ext_edgeEquiv fun p => by
    rw [sheet_apply, pairing_symm_apply, chainZOperator_operators_edgeEquiv,
      chainZOperator_operators_edgeEquiv]
    rfl

/-- Sheet `1` of a Z-type chain operator is the Z-type chain operator of sheet
`1` of the chain. -/
lemma sheet_one_chainZOperator :
    sheet D.pairing 1 (D.coverComplex.chainZOperator v).operators =
      (D.baseComplex.chainZOperator (D.sheet1 v)).operators :=
  operators_ext_edgeEquiv fun p => by
    rw [sheet_apply, pairing_symm_apply, chainZOperator_operators_edgeEquiv,
      chainZOperator_operators_edgeEquiv]
    rfl

/-- The fold of a Z-type chain operator is the Z-type chain operator of the
pushforward. -/
theorem fold_chainZOperator :
    fold D.pairing (D.coverComplex.chainZOperator v).operators =
      (D.baseComplex.chainZOperator (D.push1 v)).operators := by
  rw [fold, sheet_zero_chainZOperator, sheet_one_chainZOperator, ← mul_operators,
    ← chainZOperator_add]
  exact congrArg (fun c => (D.baseComplex.chainZOperator c).operators) (D.sheet0_add_sheet1 v)

/-- The double of a Z-type chain operator is the Z-type chain operator of the
pullback. -/
theorem double_chainZOperator :
    double D.pairing (D.baseComplex.chainZOperator u).operators =
      (D.coverComplex.chainZOperator (D.pull1 u)).operators :=
  operators_ext_edgeEquiv fun q => by
    rw [double_apply, pairing_apply, chainZOperator_operators_edgeEquiv,
      chainZOperator_operators_edgeEquiv]
    rfl

/-- The sheet swap of a Z-type chain operator is the Z-type chain operator of
the deck shift. -/
theorem sheetSwap_chainZOperator :
    sheetSwap D.pairing (D.coverComplex.chainZOperator v).operators =
      (D.coverComplex.chainZOperator (D.deckShift1 v)).operators :=
  operators_ext_edgeEquiv fun q => by
    rw [sheetSwap_apply, partner_pairing, chainZOperator_operators_edgeEquiv,
      chainZOperator_operators_edgeEquiv]
    rfl

end Dictionary

/-! ## The deck shift on boundaries and dual boundaries -/

/-- Boundaries of the cover complex are invariant under the deck shift. -/
lemma deckShift1_mem_boundaries {c : G × Fin 2 → ZMod 2}
    (hc : c ∈ D.coverComplex.boundaries) : D.deckShift1 c ∈ D.coverComplex.boundaries := by
  obtain ⟨f, rfl⟩ := hc
  exact ⟨D.deckShift0 f, bbBoundary2Fn_translate D.Ac D.Bc D.deckS f⟩

/-- The duality involution commutes with the deck shift. -/
lemma bbDualFn_deckShift1 (c : G × Fin 2 → ZMod 2) :
    bbDualFn (D.deckShift1 c) = D.deckShift1 (bbDualFn c) := by
  funext ⟨g, j⟩
  fin_cases j <;> simp [bbDualFn, deckShift1, blockSwapNeg, D.neg_deckS, add_comm]

/-- Dual boundaries of the cover complex are invariant under the deck shift. -/
lemma deckShift1_mem_dualBoundaries {c : G × Fin 2 → ZMod 2}
    (hc : c ∈ D.coverComplex.dualBoundaries) :
    D.deckShift1 c ∈ D.coverComplex.dualBoundaries :=
  (bbDual_mem_boundaries_iff D.Ac D.Bc _).mp <| by
    rw [D.bbDualFn_deckShift1]
    exact D.deckShift1_mem_boundaries ((bbDual_mem_boundaries_iff D.Ac D.Bc c).mpr hc)

/-- If the deck translation acts trivially on `H₁` of the cover, then
`c + σ c` is a dual boundary for every dual cycle `c`: the duality involution
exchanges cycles and dual cycles and commutes with the deck shift. -/
theorem deckTrivialOnH1_dual (hR : D.DeckTrivialOnH1) {c : G × Fin 2 → ZMod 2}
    (hc : c ∈ D.coverComplex.dualCycles) :
    c + D.deckShift1 c ∈ D.coverComplex.dualBoundaries :=
  (bbDual_mem_boundaries_iff D.Ac D.Bc _).mp <| by
    have h := hR _ ((bbDual_mem_cycles_iff D.Ac D.Bc c).mpr hc)
    rw [← D.bbDualFn_deckShift1] at h
    exact h

/-! ## Symmetry and condition (R) -/

/-- The pairing by the deck translation is symmetric for the cover code. -/
theorem isSymmetric_pairing :
    IsSymmetric D.pairing D.coverComplex.homologicalStabilizerGroup := by
  intro s hs
  obtain ⟨cz, hcz, cx, hcx, rfl⟩ := exists_eq_chainZOperator_mul_chainXOperator hs
  rw [mul_operators, sheetSwap_mul, sheetSwap_chainZOperator, sheetSwap_chainXOperator]
  exact mul_mem
    (operators_mem_operatorImage
      (chainZOperator_mem_of_mem_dualBoundaries (D.deckShift1_mem_dualBoundaries hcz)))
    (operators_mem_operatorImage
      (chainXOperator_mem_of_mem_boundaries (D.deckShift1_mem_boundaries hcx)))

/-- Condition (R): if the deck translation acts trivially on `H₁` of the cover,
then `g * g^σ` is a stabilizer for every logical operator `g` of the cover
code, of any Pauli type. -/
theorem condition_R_of_deckTrivialOnH1 (hR : D.DeckTrivialOnH1) :
    ∀ g ∈ centralizer D.coverComplex.homologicalStabilizerGroup,
      g.operators * sheetSwap D.pairing g.operators ∈
        operatorImage D.coverComplex.homologicalStabilizerGroup.toSubgroup := by
  intro g hg
  rw [operators_eq_chainXOperator_mul_chainZOperator g, sheetSwap_mul, sheetSwap_chainXOperator,
    sheetSwap_chainZOperator, mul_mul_mul_comm, ← mul_operators, ← chainXOperator_add,
    ← mul_operators, ← chainZOperator_add]
  exact mul_mem
    (operators_mem_operatorImage (chainXOperator_mem_of_mem_boundaries
      (hR _ (xChainOf_mem_cycles_of_centralizer g hg))))
    (operators_mem_operatorImage (chainZOperator_mem_of_mem_dualBoundaries
      (D.deckTrivialOnH1_dual hR (zChainOf_mem_dualCycles_of_centralizer g hg))))

/-- Condition (R) as an inclusion of groups: if the deck translation acts
trivially on `H₁` of the cover, every logical fold is a seam operator. -/
theorem logicalFoldImage_le_seamGroup_of_deckTrivialOnH1 (hR : D.DeckTrivialOnH1) :
    logicalFoldImage D.pairing D.coverComplex.homologicalStabilizerGroup ≤
      seamGroup D.pairing D.coverComplex.homologicalStabilizerGroup :=
  (logicalFoldImage_le_seamGroup_iff _ _).mp (D.condition_R_of_deckTrivialOnH1 hR)

/-! ## The four groups on X-type chain operators -/

/-- The X-type chain operator of a base chain `c` is in the doubling group iff
the pullback of `c` is a cover cycle. -/
theorem chainXOperator_mem_doublingGroup_iff (c : H × Fin 2 → ZMod 2) :
    (D.baseComplex.chainXOperator c).operators ∈
        doublingGroup D.pairing D.coverComplex.homologicalStabilizerGroup ↔
      D.pull1 c ∈ D.coverComplex.cycles := by
  rw [mem_doublingGroup, double_chainXOperator, ← mem_centralizer_iff_operators_mem]
  exact chainXOperator_mem_centralizer_iff_mem_cycles _

/-- The X-type chain operator of a base chain `c` is a seam operator iff the
pullback of `c` is a cover boundary. -/
theorem chainXOperator_mem_seamGroup_iff (c : H × Fin 2 → ZMod 2) :
    (D.baseComplex.chainXOperator c).operators ∈
        seamGroup D.pairing D.coverComplex.homologicalStabilizerGroup ↔
      D.pull1 c ∈ D.coverComplex.boundaries := by
  rw [mem_seamGroup, double_chainXOperator]
  exact chainXOperator_operators_mem_operatorImage_iff _

/-- The X-type chain operator of a base chain `c` is a stabilizer fold iff `c`
is a base boundary. -/
theorem chainXOperator_mem_foldImage_iff (c : H × Fin 2 → ZMod 2) :
    (D.baseComplex.chainXOperator c).operators ∈
        foldImage D.pairing D.coverComplex.homologicalStabilizerGroup ↔
      c ∈ D.baseComplex.boundaries := by
  refine ⟨fun hc => ?_, ?_⟩
  · obtain ⟨s, hs, h⟩ := (mem_foldImage _ _).mp hc
    obtain ⟨cz, hcz, cx, hcx, rfl⟩ := exists_eq_chainZOperator_mul_chainXOperator hs
    rw [mul_operators, fold_mul, fold_chainZOperator, fold_chainXOperator] at h
    have hkey : ∀ a b c : ZMod 2,
        ((if a = 1 then PauliOperator.Z else PauliOperator.I).mulOp
          (if b = 1 then PauliOperator.X else PauliOperator.I)).operator =
          (if c = 1 then PauliOperator.X else PauliOperator.I) → b = c := by decide
    have heq : D.push1 cx = c := funext fun p => hkey _ _ _ <| by
      simpa only [NQubitPauliOperator.mul_apply, chainZOperator_operators_edgeEquiv,
        chainXOperator_operators_edgeEquiv] using congrFun h (D.baseComplex.edgeEquiv p)
    exact heq ▸ D.push1_mem_boundaries hcx
  · rintro ⟨f, rfl⟩
    refine (mem_foldImage _ _).mpr ⟨D.coverComplex.chainXOperator (D.liftStab f),
      chainXOperator_mem_of_mem_boundaries (D.liftStab_mem_boundaries f), ?_⟩
    rw [fold_chainXOperator, D.push1_liftStab]
    rfl

/-- X-type doubling logicals are the base chains whose pullback is a cover
cycle that is not a boundary. -/
theorem isDoublingLogical_chainXOperator_iff (c : H × Fin 2 → ZMod 2) :
    IsDoublingLogical D.pairing D.coverComplex.homologicalStabilizerGroup
        (D.baseComplex.chainXOperator c).operators ↔
      D.pull1 c ∈ D.coverComplex.cycles ∧ D.pull1 c ∉ D.coverComplex.boundaries :=
  (D.chainXOperator_mem_doublingGroup_iff c).and (D.chainXOperator_mem_seamGroup_iff c).not

/-! ## The X sector -/

/-- The least weight of an X-type doubling logical is the base distance `d`:
the logical floor bounds every one of them from below, and a base cycle of
weight `d` whose pullback is not a cover boundary attains the bound. -/
theorem isLeast_xType_doublingLogical {d : ℕ} (hbase : D.LogicalFloor d)
    (uStar : H × Fin 2 → ZMod 2) (hu_cyc : uStar ∈ D.baseComplex.cycles)
    (hu_w : D.baseComplex.chainWeight uStar = d)
    (hτnb : D.pull1 uStar ∉ D.coverComplex.boundaries) :
    IsLeast {w | ∃ u, IsDoublingLogical D.pairing D.coverComplex.homologicalStabilizerGroup u ∧
      IsXType u ∧ weight u = w} d := by
  refine ⟨⟨_, (D.isDoublingLogical_chainXOperator_iff uStar).mpr ⟨D.pull1_mem_cycles hu_cyc, hτnb⟩,
    (chainXOperator_isXType (X := D.baseComplex) uStar).2,
    (weight_chainXOperator (X := D.baseComplex) uStar).trans hu_w⟩, ?_⟩
  rintro w ⟨u, hu, huX, rfl⟩
  obtain ⟨c, rfl⟩ := exists_chainXOperator_operators_eq (X := D.baseComplex) huX
  rw [isDoublingLogical_chainXOperator_iff] at hu
  exact (hbase c (D.descend_cycle hu.1) fun h => hu.2 (D.pull1_mem_boundaries h)).trans_eq
    (weight_chainXOperator (X := D.baseComplex) c).symm

/-- Condition (F) on the X sector: under the seam-coset floor
`SeamCosetFloor (2 * d)`, every X-type seam logical has weight `≥ 2 * d`. Such
an operator is the chain operator of a base chain that is not a boundary and
whose pullback is a cover boundary, and these chains are the elements of the
seam cosets (`exists_seamCoset_of_pull1_mem_boundaries`). -/
theorem condition_F_of_seamCosetFloor {d : ℕ} (hMim : D.SeamCosetFloor (2 * d)) :
    ∀ b, IsSeamLogical D.pairing D.coverComplex.homologicalStabilizerGroup b → IsXType b →
      2 * d ≤ weight b := by
  rintro b ⟨hT, hJ⟩ hbX
  obtain ⟨w, rfl⟩ := exists_chainXOperator_operators_eq (X := D.baseComplex) hbX
  rw [chainXOperator_mem_foldImage_iff] at hJ
  obtain ⟨ζ, hζ, f, rfl⟩ := D.exists_seamCoset_of_pull1_mem_boundaries
    ((D.chainXOperator_mem_seamGroup_iff w).mp hT)
  exact (hMim ζ hζ f hJ).trans_eq (weight_chainXOperator (X := D.baseComplex) _).symm

/-- Condition (S) on the X sector: under the dangerous floor
`DangerousFloorNZ (2 * d)`, every nontrivial logical operator `v` with X-type
operator part that folds to a stabilizer fold `b ≠ 1` satisfies
`wt b + 2 · residualWeight v ≥ 2 * d`. For such `v` the left-hand side is the
weight of `v`. -/
theorem condition_S_of_dangerousFloorNZ {d : ℕ} (hM : D.DangerousFloorNZ (2 * d)) :
    ∀ b ∈ foldImage D.pairing D.coverComplex.homologicalStabilizerGroup, b ≠ 1 →
      ∀ v, IsNontrivialLogicalOperator v D.coverComplex.homologicalStabilizerGroup →
        IsXType v.operators → fold D.pairing v.operators = b →
        2 * d ≤ weight b + 2 * residualWeight D.pairing v := by
  rintro b hbJ hb1 v hv hvX rfl
  obtain ⟨c, hc⟩ := exists_chainXOperator_operators_eq (X := D.coverComplex) hvX
  obtain ⟨hcyc, hnb⟩ := (chainXOperator_isNontrivialLogical_iff c).mp
    ((isNontrivialLogicalOperator_iff_of_operators_eq _ hc).mpr hv)
  rw [← hc, fold_chainXOperator] at hbJ hb1
  have hne : D.push1 c ≠ 0 := fun h0 =>
    hb1 (by rw [h0]; exact congrArg operators chainXOperator_zero)
  calc 2 * d ≤ D.coverComplex.chainWeight c :=
        hM c hcyc hnb ((D.chainXOperator_mem_foldImage_iff _).mp hbJ) hne
    _ = weight v.operators := by rw [← hc]; exact (weight_chainXOperator c).symm
    _ = _ := weight_eq_weight_fold_add_two_mul_weight_outsideSupport D.pairing _ (Or.inl hvX)

/-! ## The doubling theorem -/

/-- **The doubling theorem through fold and double.** For a free double cover
`D` of bivariate bicycle codes, assume that every base cycle that is not a
boundary has weight at least `d`; that `uStar` is a base cycle of weight `d`
whose pullback is not a cover boundary; that the deck translation acts
trivially on `H₁` of the cover; that the seam-coset floor
`SeamCosetFloor (2 * d)` holds; and that every nonzero base boundary of weight
`< 2 * d` is admissible. Then `2 * d` is the least weight of a nontrivial
logical operator of the cover code. The X-type logical operators are bounded
by the sector form of the fold-and-double theorem, the Z-type ones by duality,
and all of them by `chainWeight_lower_bound_transfers`. -/
theorem isLeast_logicalWeight_two_mul_of_foldDouble {d : ℕ}
    (hbase : D.LogicalFloor d)
    (uStar : H × Fin 2 → ZMod 2)
    (hu_cyc : uStar ∈ D.baseComplex.cycles)
    (hu_w : D.baseComplex.chainWeight uStar = d)
    (hτnb : D.pull1 uStar ∉ D.coverComplex.boundaries)
    (hR : D.DeckTrivialOnH1)
    (hMim : D.SeamCosetFloor (2 * d))
    (hadm : ∀ b : H × Fin 2 → ZMod 2, b ∈ D.baseComplex.boundaries → b ≠ 0 →
      D.baseComplex.chainWeight b < 2 * d → D.LightBoundaryAdmissible d b) :
    IsLeast {w : ℕ | ∃ g : NQubitPauliGroupElement D.coverComplex.numQubits,
      IsNontrivialLogicalOperator g D.coverComplex.homologicalStabilizerGroup ∧
      NQubitPauliGroupElement.weight g = w} (2 * d) := by
  have hX := isLeast_logicalWeight_two_mul_of_floors_sector D.pairing
    D.coverComplex.homologicalStabilizerGroup IsXType IsXType
    (fun _ hP => isXType_fold D.pairing hP) (fun _ hP => isXType_sheet D.pairing 0 hP)
    (fun _ hu => isXType_double D.pairing hu)
    (D.isLeast_xType_doublingLogical hbase uStar hu_cyc hu_w hτnb)
    (fun b hb => D.condition_F_of_seamCosetFloor hMim b
      ⟨D.logicalFoldImage_le_seamGroup_of_deckTrivialOnH1 hR hb.1, hb.2⟩)
    (fun b hbJ hb1 _ =>
      D.condition_S_of_dangerousFloorNZ (D.dangerousFloorNZ_of_admissible hbase hadm) b hbJ hb1)
  have hXc : ∀ c ∈ D.coverComplex.cycles, c ∉ D.coverComplex.boundaries →
      2 * d ≤ D.coverComplex.chainWeight c := fun c hc hnb =>
    (hX.2 ⟨_, (chainXOperator_isNontrivialLogical_iff c).mpr ⟨hc, hnb⟩,
      (chainXOperator_isXType c).2, rfl⟩).trans_eq (weight_chainXOperator c)
  obtain ⟨g, hg, -, hw⟩ := hX.1
  refine ⟨⟨g, hg, hw⟩, ?_⟩
  rintro w ⟨g, hg, rfl⟩
  exact chainWeight_lower_bound_transfers D.coverComplex (2 * d) hXc
    ((bb_cycle_bound_iff_dual_bound D.Ac D.Bc (2 * d)).mp hXc) g hg

/-- `isLeast_logicalWeight_two_mul_of_foldDouble` has exactly the statement of
`pauli_distance_eq_double_of_admissible`. -/
example : @XDoubleCoverData.isLeast_logicalWeight_two_mul_of_foldDouble G H _ _ _ _ _ _ D =
    @XDoubleCoverData.pauli_distance_eq_double_of_admissible G H _ _ _ _ _ _ D :=
  rfl

end XDoubleCoverData
end BB
end Homological
end Stabilizer
end Quantum
